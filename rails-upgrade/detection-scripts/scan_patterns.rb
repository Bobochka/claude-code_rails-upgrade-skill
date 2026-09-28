# frozen_string_literal: true

# Runs every detection pattern for one upgrade hop against a Rails app and
# prints the findings as a table: same inputs, same output, every run. This is
# the scripted form of Workflow 05 (detect breaking changes). It replaces the
# per-pattern Grep loop, which drifts between sessions and silently skips
# patterns when the list is long.
#
# Usage, from the app root:
#
#   ruby <skill>/detection-scripts/scan_patterns.rb             # hop from Gemfile.lock
#   ruby <skill>/detection-scripts/scan_patterns.rb --target 7.0
#   ruby <skill>/detection-scripts/scan_patterns.rb --patterns path/to/rails-70-patterns.yml
#   ruby <skill>/detection-scripts/scan_patterns.rb --summary   # summary table only
#   ruby <skill>/detection-scripts/scan_patterns.rb --format json
#   ruby <skill>/detection-scripts/scan_patterns.rb --self-test
#
# Without --target or --patterns, the current Rails version is read from the
# app's Gemfile.lock and the target is the next version that has a patterns
# file (4.0 -> 4.1, 6.0 -> 7.0 while there is no 6.1 file, and so on).
#
# Runs with the app's own Ruby, so it stays Ruby 2.3 compatible: stdlib only,
# no `&.`, no `<<~`, no `String#match?`, no `Array#sum`, no `Dir.children`.
#
# How matching works, and why:
#
# 1. A pattern is matched against FILE CONTENT, not one line at a time. A call
#    split across lines is reachable when the pattern is written to reach it
#    (`[^)]*` and `\s*` cross newlines, `[^\n]*` and `.` do not). A line-based
#    grep can never see those sites, so its counts are a floor.
# 2. One row per SITE, keyed on where the match ends. The end is the offending
#    token and is the line reported. Two matches ending at the same offset are
#    one site; two sites sharing a line are two rows.
# 3. `exclude:` is tested on the lines the match spans. A site is suppressed
#    only when every match reaching it was excluded. Suppressed sites are
#    counted and listed with --show-suppressed, because `exclude:` can drop a
#    real hit that shares a line with the excluded form.
# 4. A match may not span more than MAX_SPAN_LINES, so a loose pattern cannot
#    rope two unrelated calls together.
# 5. An entry whose search_paths resolve to no files is UNSCANNED, never zero
#    hits. "Could not scan" and "scanned clean" are different answers.
# 6. Packwerk packs, engines and components are searched too: a search_path
#    like "app/models/" also reaches packs/*/app/models/. node_modules, vendor,
#    tmp, log, coverage are skipped unless a search_path names them.
# 7. An entry with an empty `pattern:` is path-based: it fires when any file
#    exists under its search_paths (e.g. vendor/plugins/).

require "yaml"
require "json"
require "optparse"
require "fileutils"

PATTERNS_DIR = File.expand_path("patterns", __dir__)
PRIORITIES = %w[high_priority medium_priority low_priority].freeze
PRIORITY_LABEL = { "high_priority" => "HIGH", "medium_priority" => "MEDIUM", "low_priority" => "LOW" }.freeze
FIX_BEFORE_BUMP = %w[breaking deprecation].freeze
KINDS = %w[breaking deprecation migration optional].freeze

MAX_SPAN_LINES = 60
# More sites than this on one line means a generated or minified file. Those
# collapse into one row that states the count.
MAX_SITES_PER_LINE = 4
MAX_TEXT = 100

IGNORED_DIRS = %w[node_modules vendor tmp log coverage .git .bundle].freeze
IGNORED_PATH_RE = Regexp.new("(?:\\A|/)(?:" + IGNORED_DIRS.map { |d| Regexp.escape(d) }.join("|") + ")/")
MODULAR_ROOT_SEEDS = %w[packs engines components].freeze
MODULAR_ROOT_MARKERS = ["package.yml", "*.gemspec", "lib/*/engine.rb"].freeze
MAX_MODULAR_ROOT_DEPTH = 2
# Files that describe the app's own environment. A pack or engine ships its
# own copy describing a different bundle, so these never expand into packs.
ENVIRONMENT_MANIFESTS = %w[
  Gemfile Gemfile.lock Gemfile.next Gemfile.next.lock
  .ruby-version .tool-versions .node-version
  Dockerfile Procfile Rakefile config.ru
  package.json package-lock.json yarn.lock
  config/database.yml config/cable.yml config/storage.yml
].freeze

class Scanner
  attr_reader :root

  def initialize(root)
    @root = root
    @text = {}
    @candidates = {}
    @modular_roots = {}
    @modular_members = {}
  end

  def modular_roots(dir = root)
    @modular_roots[dir] ||= begin
      prefix = File.join(dir, "")
      discovered = (1..MAX_MODULAR_ROOT_DEPTH).flat_map do |depth|
        MODULAR_ROOT_MARKERS.flat_map do |marker|
          Dir.glob(File.join(dir, *Array.new(depth + 1, "*"), marker)).map do |f|
            f[prefix.length..-1].split("/").first(depth).join("/")
          end
        end
      end
      discovered = discovered.reject { |m| m.split("/").any? { |seg| IGNORED_DIRS.include?(seg) } }
      (MODULAR_ROOT_SEEDS + discovered).uniq.select { |m| File.directory?(File.join(dir, m)) }.sort
    end
  end

  # { root_name => [member dirs] }, walking root -> member -> nested root.
  # Walking instead of globbing `**` keeps engine dummy apps and node_modules
  # copies of app/ out of the scan.
  def modular_members
    @modular_members[root] ||= begin
      members = {}
      modular_roots.each do |m|
        found = []
        queue = [File.join(root, m)]
        until queue.empty?
          dir = queue.shift
          entries = begin
            Dir.entries(dir).sort.reject { |e| e == "." || e == ".." }
          rescue SystemCallError
            []
          end
          entries.each do |name|
            next if IGNORED_DIRS.include?(name)
            member = File.join(dir, name)
            next if File.symlink?(member) || !File.directory?(member)
            found << member
            queue.concat(modular_roots(member).map { |n| File.join(member, n) })
          end
        end
        members[m] = found
      end
      members
    end
  end

  def text_file?(path)
    return @text[path] if @text.key?(path)
    @text[path] = begin
      head = File.binread(path, 8192)
      head.nil? || !head.include?("\x00".dup.force_encoding("BINARY"))
    rescue StandardError
      false
    end
  end

  def expand(path)
    if File.file?(path)
      [path]
    elsif File.directory?(path)
      Dir.glob(File.join(path, "**", "*")).sort.select { |f| File.file?(f) }
    else
      []
    end
  end

  def ignored?(path)
    !(path =~ IGNORED_PATH_RE).nil?
  end

  def resolve(path)
    files = File.exist?(path) ? expand(path) : Dir.glob(path.chomp("/")).sort.flat_map { |m| expand(m) }
    # A search_path that names an ignored dir (vendor/plugins/) gets it.
    return files if ignored?(path.sub(/\A#{Regexp.escape(File.join(root, ""))}/, ""))
    files.reject { |f| ignored?(f.sub(/\A#{Regexp.escape(File.join(root, ""))}/, "")) }
  end

  def candidate_files(sp)
    @candidates[sp] ||= begin
      locations = [File.join(root, sp)]
      unless ENVIRONMENT_MANIFESTS.include?(sp)
        modular_members.each do |m, dirs|
          next if sp == m || sp.start_with?("#{m}/")
          locations.concat(dirs.map { |d| File.join(d, sp) })
        end
      end
      locations.flat_map { |loc| resolve(loc) }.uniq
    end
  end

  def relative(file)
    file.sub(/\A#{Regexp.escape(File.join(root, ""))}/, "").sub(%r{\A\./}, "")
  end

  # Returns { files_scanned:, hits: [[file, line, text]], suppressed: [...] }.
  def scan(entry)
    files = Array(entry["search_paths"]).flat_map { |sp| candidate_files(sp) }.uniq.select { |f| text_file?(f) }
    return path_only(entry, files) if entry["pattern"].to_s.strip.empty?

    pattern = Regexp.new(entry["pattern"])
    exclude = entry["exclude"].to_s.empty? ? nil : Regexp.new(entry["exclude"])
    hits = []
    suppressed = []
    files.each do |file|
      content = begin
        File.read(file)
      rescue StandardError
        next
      end
      # Scrub rather than skip: skipping a file with one bad byte reports it
      # as scanned clean.
      content = content.scrub("?") unless content.valid_encoding?
      scan_content(content, pattern, exclude).each do |line, text, excluded|
        (excluded ? suppressed : hits) << [relative(file), line, text]
      end
    end
    { :files_scanned => files.length, :hits => hits, :suppressed => suppressed }
  end

  def path_only(entry, files)
    hits = Array(entry["search_paths"]).map do |sp|
      n = candidate_files(sp).length
      n > 0 ? [sp, nil, "#{n} file(s) present"] : nil
    end.compact
    { :files_scanned => files.length, :hits => hits, :suppressed => [], :path_only => true }
  end

  def scan_content(content, pattern, exclude)
    sites = {}
    pos = 0
    line_off = 0
    line_no = 0
    while pos <= content.length && (md = safe_match(pattern, content, pos))
      b = md.begin(0)
      e = md.end(0)
      line_no += content[line_off...b].count("\n")
      line_off = b
      # Anchor on the last non-whitespace character matched: a trailing `\s*`
      # may cross a newline and point at an unrelated line.
      tail = e > b ? e - 1 : b
      tail -= 1 while tail > b && content[tail] =~ /\s/
      end_line = line_no + content[b..tail].to_s.count("\n")
      span_ok = (end_line - line_no) < MAX_SPAN_LINES
      excluded = false
      if span_ok && exclude
        span = content[bol(content, b)...eol(content, tail)].to_s
        excluded = !(span =~ exclude).nil?
      end
      pos = if excluded && end_line > line_no
              eol(content, b) + 1
            else
              e > b ? e : b + 1
            end
      next unless span_ok

      site = sites[e] ||= { :line => end_line + 1, :excluded => true,
                            :text => content[bol(content, tail)...eol(content, tail)].to_s.strip[0, MAX_TEXT] }
      site[:excluded] &&= excluded
    end

    by_line = {}
    sites.keys.sort.each { |k| (by_line[sites[k][:line]] ||= []) << sites[k] }
    rows = []
    by_line.keys.sort.each do |ln|
      group = by_line[ln]
      if group.length > MAX_SITES_PER_LINE
        rows << [ln, "#{group.first[:text][0, 60]} (#{group.length} matches on this line)", group.all? { |g| g[:excluded] }]
      else
        group.each { |s| rows << [ln, s[:text], s[:excluded]] }
      end
    end
    rows
  end

  def bol(content, off)
    i = off.zero? ? nil : content.rindex("\n", off - 1)
    i ? i + 1 : 0
  end

  def eol(content, off)
    content.index("\n", off) || content.length
  end

  def safe_match(pattern, content, pos)
    pattern.match(content, pos)
  rescue ArgumentError, Encoding::CompatibilityError
    nil
  end
end

# ---------------------------------------------------------------------------
# Hop resolution

def version_key(v)
  v.split(".").map(&:to_i)
end

def available_versions
  Dir[File.join(PATTERNS_DIR, "rails-*-patterns.yml")].map do |f|
    digits = File.basename(f)[/rails-(\d+)-patterns\.yml/, 1]
    digits ? "#{digits[0..-2]}.#{digits[-1]}" : nil
  end.compact.sort_by { |v| version_key(v) }
end

def patterns_file_for(version)
  File.join(PATTERNS_DIR, "rails-#{version.delete('.')}-patterns.yml")
end

def lock_rails_version(lockfile)
  return nil unless File.file?(lockfile)
  File.read(lockfile)[/^    rails \((\d+\.\d+)[^)]*\)/, 1]
end

def normalize_target(t)
  t = t.to_s.strip
  t = "#{t[0..-2]}.#{t[-1]}" if t =~ /\A\d{2,3}\z/
  t = t[/\A\d+\.\d+/] || t
  t
end

# ---------------------------------------------------------------------------
# Rendering

def md_cell(s)
  s.to_s.gsub("|", "\\|").gsub("`", "'")
end

def site_ref(file, line)
  line ? "#{file}:#{line}" : file
end

def render_markdown(meta, results, opts)
  out = []
  out << "# Pattern scan: Rails #{meta[:from] || '?'} -> #{meta[:to]}"
  out << ""
  out << "- Patterns: `#{meta[:patterns_rel]}` (#{results.length} entries)"
  out << "- Root: `#{meta[:root]}`"
  out << "- Hop source: #{meta[:hop_source]}"
  out << "- Modular roots: #{meta[:modular_roots].empty? ? 'none found' : meta[:modular_roots].join(', ')}"
  out << ""

  found = results.reject { |r| r[:hits].empty? }
  out << "## Summary"
  out << ""
  if found.empty?
    out << "No pattern matched."
  else
    out << "| Bucket | Priority | Kind | Pattern | Variable | Sites | Files |"
    out << "|--------|----------|------|---------|----------|------:|------:|"
    found.each do |r|
      files = r[:hits].map(&:first).uniq.length
      out << "| #{r[:bucket_label]} | #{PRIORITY_LABEL[r[:priority]]} | #{r[:kind]} | #{md_cell(r[:name])} | `#{r[:variable]}` | #{r[:hits].length} | #{files} |"
    end
  end
  out << ""
  counts = KINDS.map { |k| "#{found.count { |r| r[:kind] == k }} #{k}" }.join(", ")
  total_sites = found.inject(0) { |t, r| t + r[:hits].length }
  affected = found.flat_map { |r| r[:hits].map(&:first) }.uniq.length
  out << "#{found.length} of #{results.length} patterns matched: #{total_sites} site(s) in #{affected} file(s). By kind: #{counts}."
  zero = results.select { |r| r[:hits].empty? && r[:files_scanned] > 0 }
  unscanned = results.select { |r| r[:files_scanned].zero? && r[:hits].empty? }
  suppressed = results.reject { |r| r[:suppressed].empty? }
  out << "#{zero.length} scanned clean, #{unscanned.length} UNSCANNED, #{suppressed.length} with sites suppressed by `exclude:`."

  unless opts[:summary]
    [["Fix before bump", true], ["Fix when ready", false]].each do |label, before|
      group = found.select { |r| FIX_BEFORE_BUMP.include?(r[:kind]) == before }
      next if group.empty?
      out << ""
      out << "## #{label} (#{group.length})"
      group.each do |r|
        out << ""
        out << "### #{PRIORITY_LABEL[r[:priority]]} · #{r[:kind]} · #{r[:name]} (`#{r[:variable]}`), #{r[:hits].length} site(s)"
        out << ""
        out << "Fix: #{r[:fix]}" if r[:fix]
        out << ""
        out << "| Location | Code |"
        out << "|----------|------|"
        r[:hits].each { |f, l, t| out << "| #{md_cell(site_ref(f, l))} | `#{md_cell(t)}` |" }
      end
    end
  end

  unless zero.empty?
    out << ""
    out << "## Scanned clean"
    out << ""
    zero.each { |r| out << "- `#{r[:variable]}` #{r[:name]} (#{r[:files_scanned]} files scanned)" }
  end

  unless suppressed.empty?
    out << ""
    out << "## Suppressed by exclude"
    out << ""
    out << "These sites matched `pattern:` and were then dropped by `exclude:`. Most are already migrated. " \
           "Check the ones where the excluded form can sit on the same line as a real hit#{opts[:show_suppressed] ? '' : ' (re-run with --show-suppressed to list them)'}."
    out << ""
    suppressed.each do |r|
      out << "- `#{r[:variable]}`: #{r[:suppressed].length} site(s), exclude `#{md_cell(r[:exclude])}`"
      next unless opts[:show_suppressed]
      r[:suppressed].each { |f, l, t| out << "  - #{site_ref(f, l)} `#{md_cell(t)}`" }
    end
  end

  unless unscanned.empty?
    out << ""
    out << "## UNSCANNED"
    out << ""
    out << "The search_paths of these entries resolved to no files in this app. This means \"could not scan\", " \
           "not \"scanned clean\". Confirm the paths do not exist here, or search the app's real layout by hand."
    out << ""
    unscanned.each { |r| out << "- `#{r[:variable]}` #{r[:name]}: #{Array(r[:search_paths]).inspect}" }
  end

  out.join("\n") + "\n"
end

def render_json(meta, results)
  JSON.pretty_generate(
    "from" => meta[:from], "to" => meta[:to], "patterns" => meta[:patterns_rel],
    "root" => meta[:root], "modular_roots" => meta[:modular_roots],
    "findings" => results.map do |r|
      {
        "name" => r[:name], "variable_name" => r[:variable], "kind" => r[:kind],
        "priority" => r[:priority], "bucket" => r[:bucket], "fix" => r[:fix],
        "files_scanned" => r[:files_scanned],
        "status" => if !r[:hits].empty? then "found"
                    elsif r[:files_scanned].zero? then "unscanned"
                    else "clean"
                    end,
        "sites" => r[:hits].map { |f, l, t| { "file" => f, "line" => l, "text" => t } },
        "suppressed" => r[:suppressed].map { |f, l, t| { "file" => f, "line" => l, "text" => t } }
      }
    end
  ) + "\n"
end

def run_scan(patterns_path, root)
  doc = YAML.load_file(patterns_path)
  findings = doc.is_a?(Hash) ? doc["upgrade_findings"] : nil
  abort("scan_patterns: #{patterns_path} has no upgrade_findings") unless findings.is_a?(Hash)
  scanner = Scanner.new(root)
  results = []
  PRIORITIES.each do |priority|
    Array(findings[priority]).each do |entry|
      r = scanner.scan(entry)
      bucket = FIX_BEFORE_BUMP.include?(entry["kind"]) ? "fix_before_bump" : "fix_when_ready"
      results << {
        :name => entry["name"], :variable => entry["variable_name"], :kind => entry["kind"],
        :priority => priority, :bucket => bucket,
        :bucket_label => bucket == "fix_before_bump" ? "Fix before bump" : "Fix when ready",
        :fix => entry["fix"], :exclude => entry["exclude"], :search_paths => entry["search_paths"],
        :files_scanned => r[:files_scanned], :hits => r[:hits], :suppressed => r[:suppressed]
      }
    end
  end
  # Bucket first, then priority, then the file's own order.
  order = results.each_with_index.map { |r, i| [r, i] }
  results = order.sort_by do |r, i|
    [r[:bucket] == "fix_before_bump" ? 0 : 1, PRIORITIES.index(r[:priority]), i]
  end.map(&:first)
  [results, scanner.modular_roots]
end

# ---------------------------------------------------------------------------
# Self-test

def self_test
  require "tmpdir"
  failures = []
  check = lambda { |desc, ok| failures << desc unless ok }
  Dir.mktmpdir do |dir|
    w = lambda do |rel, body|
      path = File.join(dir, rel)
      FileUtils.mkdir_p(File.dirname(path))
      File.write(path, body)
    end
    w.call("app/models/a.rb", "scope :recent, where(x: 1)\nscope :ok, -> { all }\n")
    w.call("app/views/show.html.erb", "<%= link_to 'x', y_path, confirm: 'sure?' %>\n")
    w.call("app/multi.rb", "rel.count(conditions: c)\nrel.count(\n  conditions: c,\n  joins: :a\n)\n")
    w.call("app/twice.rb", "match \"/a\" and match \"/b\"\n")
    w.call("app/routes_like.rb", "match \"/a\", via: :get\nmatch \"/b\"\n")
    w.call("packs/p1/package.yml", "enforce_privacy: true\n")
    w.call("packs/p1/app/models/b.rb", "scope :old, where(y: 2)\n")
    w.call("packs/p1/app/webpack/node_modules/x/c.rb", "scope :vendored, where(z: 3)\n")
    w.call("vendor/plugins/foo/init.rb", "# plugin\n")
    w.call("Gemfile.lock", "GEM\n  specs:\n    rails (4.0.13)\n")
    File.binwrite(File.join(dir, "app/badbyte.rb"), "rel.count(conditions: a)\n\xff\xfe\nrel.count(conditions: b)\n")

    s = Scanner.new(dir)
    r = s.scan("pattern" => "scope\\s+:\\w+,\\s*where", "exclude" => "", "search_paths" => ["app/models/"])
    check.call("reaches packs/*/app/models and skips node_modules (want 2 hits, got #{r[:hits].length})", r[:hits].length == 2)
    r = s.scan("pattern" => "confirm:", "exclude" => "", "search_paths" => ["app/views/"])
    check.call("scans non-.rb files", r[:hits].length == 1)
    r = s.scan("pattern" => "\\.count\\([^)]*conditions:", "exclude" => "", "search_paths" => ["app/multi.rb"])
    check.call("finds single-line and multi-line sites (got #{r[:hits].length})", r[:hits].length == 2)
    check.call("multi-line site reports the end line", r[:hits][1] && r[:hits][1][1] == 3 && r[:hits][1][2] == "conditions: c,")
    r = s.scan("pattern" => "match\\s+\"", "exclude" => "", "search_paths" => ["app/twice.rb"])
    check.call("two sites on one line are two rows", r[:hits].length == 2)
    r = s.scan("pattern" => "match\\s+\"", "exclude" => "via:", "search_paths" => ["app/routes_like.rb"])
    check.call("exclude suppresses and counts", r[:hits].length == 1 && r[:suppressed].length == 1)
    r = s.scan("pattern" => "anything", "exclude" => "", "search_paths" => ["engines/"])
    check.call("missing path is unscanned", r[:files_scanned].zero? && r[:hits].empty?)
    r = s.scan("pattern" => "", "exclude" => "", "search_paths" => ["vendor/plugins/"])
    check.call("empty pattern is path-based and honours a named vendor path", r[:hits].length == 1)
    r = s.scan("pattern" => "\\.count\\([^)]*conditions:", "exclude" => "", "search_paths" => ["app/badbyte.rb"])
    check.call("invalid byte keeps the file's hits", r[:hits].length == 2)
    check.call("reads the hop from Gemfile.lock", lock_rails_version(File.join(dir, "Gemfile.lock")) == "4.0")
  end
  check.call("normalizes 41 and 4.1.2", normalize_target("41") == "4.1" && normalize_target("4.1.2") == "4.1")

  # Every shipped patterns file must load and scan without raising.
  Dir.mktmpdir do |dir|
    available_versions.each do |v|
      begin
        run_scan(patterns_file_for(v), dir)
      rescue StandardError => e
        failures << "rails-#{v.delete('.')}-patterns.yml raised #{e.class}: #{e.message}"
      end
    end
  end

  if failures.empty?
    puts "scan_patterns: self-test OK"
    exit 0
  end
  failures.each { |f| warn "FAIL: #{f}" }
  exit 1
end

# ---------------------------------------------------------------------------
# CLI

if $PROGRAM_NAME == __FILE__
  opts = { :root => ".", :format => "markdown" }
  OptionParser.new do |o|
    o.banner = "Usage: ruby scan_patterns.rb [--target X.Y | --patterns FILE] [--root DIR] [options]"
    o.on("--target VERSION", "target Rails version, e.g. 7.0 (default: next hop after Gemfile.lock)") { |v| opts[:target] = v }
    o.on("--patterns FILE", "scan with this patterns file instead") { |v| opts[:patterns] = v }
    o.on("--root DIR", "app root (default: .)") { |v| opts[:root] = v }
    o.on("--format FORMAT", %w[markdown json], "markdown (default) or json") { |v| opts[:format] = v }
    o.on("--summary", "print the summary table only, no per-site detail") { opts[:summary] = true }
    o.on("--show-suppressed", "list the sites dropped by each entry's exclude:") { opts[:show_suppressed] = true }
    o.on("--self-test", "run built-in assertions and exit") { opts[:self_test] = true }
  end.parse!

  self_test if opts[:self_test]

  root = File.expand_path(opts[:root])
  abort("scan_patterns: --root #{opts[:root].inspect} is not a directory") unless File.directory?(root)
  current = lock_rails_version(File.join(root, "Gemfile.lock"))

  if opts[:patterns]
    patterns = File.expand_path(opts[:patterns])
    abort("scan_patterns: #{opts[:patterns]} not found") unless File.file?(patterns)
    target = YAML.load_file(patterns)["version"].to_s
    hop_source = "--patterns"
  else
    if opts[:target]
      target = normalize_target(opts[:target])
      hop_source = "--target"
    else
      abort("scan_patterns: no Gemfile.lock with rails in #{root}; pass --target X.Y") unless current
      target = available_versions.find { |v| (version_key(v) <=> version_key(current)) > 0 }
      abort("scan_patterns: no patterns file newer than Rails #{current}") unless target
      hop_source = "Gemfile.lock pins rails #{current}; next patterns file is #{target}"
    end
    patterns = patterns_file_for(target)
    unless File.file?(patterns)
      abort("scan_patterns: no patterns file for Rails #{target}. Available: #{available_versions.join(', ')}")
    end
  end

  results, roots = run_scan(patterns, root)
  meta = {
    :from => current, :to => target, :root => root, :hop_source => hop_source, :modular_roots => roots,
    :patterns_rel => patterns.sub(%r{\A.*/(detection-scripts/)}, '\1')
  }
  print(opts[:format] == "json" ? render_json(meta, results) : render_markdown(meta, results, opts))
end
