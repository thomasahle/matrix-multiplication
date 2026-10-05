#!/usr/bin/env bash
# Report declaration-name collisions that can break a build the moment two modules meet.
#
# WARN level: this gate never fails the build. It prints findings and always exits 0.
# It is deliberately non-blocking until the two collisions it currently reports are
# resolved by their owning lanes; promote it to a hard gate (exit 1 on findings) only
# once it reports clean.
#
# Usage:
#   bash scripts/check_declaration_collisions.sh          # scan the working tree
#   bash scripts/check_declaration_collisions.sh --quiet  # summary counts only
#
# Two classes are reported, both learned from real breaks in this repository:
#
#   [1] REDECLARATION -- the same fully qualified name declared publicly in two files.
#       If anything ever imports both, Lean fails with "has already been declared".
#       Real instances: `ProbabilityVector.pushforward_mixture` / `pushforward_joint_snd`
#       (Probability/TwoLetter.lean vs Probability/Pushforward.lean, which TwoLetter
#       imports -- a live break) and `Examples.cwBlockOfSplitDigit` (two different bodies,
#       zero co-importers today, one import away from breaking).
#
#   [2] AMBIGUITY -- one short name declared publicly in two namespaces, where some module
#       imports both definers, explicitly `open`s both, and uses the bare name. Lean then
#       reports "Ambiguous term". Real instance: `complementSplitWord` duplicated into
#       InterfaceTensorWordCore.lean, which broke 13 modules.
#
# `private` declarations are ignored on purpose: Lean mangles their names per module, so
# duplicate private helpers in different files are harmless and this repository has many.
set -euo pipefail
cd "$(dirname "$0")/.."

QUIET=0
[[ "${1:-}" == "--quiet" ]] && QUIET=1

python3 - "$QUIET" <<'PYTHON'
import os, re, sys, collections

quiet = sys.argv[1] == "1"

# Only git-TRACKED sources are scanned. Walking the worktree would sweep in other
# lanes' private farm copies under scratchpad/ and tmp/ (tens of thousands of files,
# each a duplicate of the real tree) and report nothing but noise.
# better_bound/ is excluded because it mirrors the Generated payload tables by design.
EXCLUDE_PREFIX = ("better_bound/",)

decl_re = re.compile(
    r'^(?P<prefix>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*)'
    r'(?P<kind>theorem|lemma|def|abbrev|structure|inductive|instance|opaque|axiom|class)\b'
    r'(?P<rest>.*)$')
ns_re    = re.compile(r'^namespace\s+([A-Za-z_][A-Za-z0-9_.\'!?]*)\s*$')
end_re   = re.compile(r'^end(?:\s+([A-Za-z_][A-Za-z0-9_.\'!?]*))?\s*$')
sec_re   = re.compile(r'^section(?:\s+([A-Za-z_][A-Za-z0-9_.\'!?]*))?\s*$')
name_re  = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)")
open_re  = re.compile(r'^open\s+(?:scoped\s+)?(.*?)(?:\s+in)?\s*$')
imp_re   = re.compile(r'^import\s+([A-Za-z_][A-Za-z0-9_.]*)')
tok_re   = re.compile(r"[A-Za-z_][A-Za-z0-9_.'!?₀-₉]*")


def strip_attrs(line):
    probe = line
    while probe.startswith('@['):
        depth = 0
        for k, ch in enumerate(probe):
            if ch == '[':
                depth += 1
            elif ch == ']':
                depth -= 1
                if depth == 0:
                    probe = probe[k + 1:].lstrip()
                    break
        else:
            return ''
    return re.sub(r'^nonrec\s+', '', probe)


def sources():
    import subprocess
    out = subprocess.run(['git', 'ls-files', '-z', '*.lean'],
                         capture_output=True, check=True).stdout
    for path in out.decode('utf-8').split('\0'):
        if path and not path.startswith(EXCLUDE_PREFIX):
            yield path


decls = []      # (fullname, short, path, line, public?)
graph = {}      # module -> [imported modules]
opens = {}      # module -> explicitly opened namespaces
toks = {}       # module -> bare identifiers used

for path in sources():
    mod = path[:-5].replace(os.sep, '.')
    try:
        text = open(path, encoding='utf-8').read()
    except (UnicodeDecodeError, OSError):
        continue
    stack, deps, opened, used = [], [], set(), set()
    in_comment = 0
    for i, raw in enumerate(text.split('\n'), 1):
        s = raw.strip()
        if in_comment:
            in_comment += s.count('/-') - s.count('-/')
            in_comment = max(in_comment, 0)
            continue
        if s.startswith('/-'):
            d = s.count('/-') - s.count('-/')
            if d > 0:
                in_comment = d
            continue
        if s.startswith('--'):
            continue
        m = imp_re.match(raw)
        if m:
            deps.append(m.group(1))
            continue
        m = ns_re.match(s)
        if m:
            stack.append(('ns', m.group(1)))
            continue
        if sec_re.match(s):
            stack.append(('sec', ''))
            continue
        if end_re.match(s):
            if stack:
                stack.pop()
            continue
        m = open_re.match(s)
        if m:
            body = m.group(1)
            if '(' in body:
                body = body[:body.index('(')]
            for w in body.split():
                if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.'!?]*", w):
                    opened.add(w)
            continue
        for w in tok_re.findall(raw):
            if '.' not in w:
                used.add(w)
        m = decl_re.match(strip_attrs(raw.rstrip()))
        if not m:
            continue
        nm = name_re.match(m.group('rest'))
        if not nm:
            continue
        short = nm.group(1)
        ns = '.'.join(n for (t, n) in stack if t == 'ns')
        full = (ns + '.' + short) if ns else short
        decls.append((full, short, path, i, 'private' not in m.group('prefix')))
    graph[mod] = deps
    opens[mod] = opened
    toks[mod] = used

# ---- [1] public cross-file redeclarations -------------------------------------------
by_full = collections.defaultdict(list)
for full, short, path, line, pub in decls:
    if pub:
        by_full[full].append((path, line))

memo = {}
def closure(m):
    if m in memo:
        return memo[m]
    seen, stack = {m}, [m]
    while stack:
        x = stack.pop()
        for y in graph.get(x, []):
            if y in graph and y not in seen:
                seen.add(y)
                stack.append(y)
    memo[m] = seen
    return seen

redecl = []
for full, sites in sorted(by_full.items()):
    files = sorted({p for p, _ in sites})
    if len(files) < 2:
        continue
    mods = [f[:-5].replace(os.sep, '.') for f in files]
    live = any(b in closure(a) for a in mods for b in mods if a != b) or \
           any(all(m in closure(c) for m in mods) for c in graph)
    redecl.append((full, sites, live))

# ---- [2] latent bare-name ambiguity --------------------------------------------------
by_short = collections.defaultdict(lambda: collections.defaultdict(set))
for full, short, path, line, pub in decls:
    if pub and full.endswith('.' + short):
        by_short[short][full[:-(len(short) + 1)]].add(path[:-5].replace(os.sep, '.'))

ambig = []
multi = {s: d for s, d in by_short.items() if len(d) > 1}
for mod in graph:
    cl, ex, tk = closure(mod), opens.get(mod, set()), toks.get(mod, set())
    for short, nsmap in multi.items():
        if short not in tk:
            continue
        hits = [(ns, sorted(ms & cl)) for ns, ms in nsmap.items() if ns in ex and (ms & cl)]
        if len(hits) > 1:
            ambig.append((mod, short, sorted(hits)))

if not quiet:
    if redecl:
        print('WARN [1] public fully-qualified names declared in more than one file:')
        for full, sites, live in sorted(redecl):
            tag = 'LIVE BREAK' if live else 'latent (no co-importer yet)'
            print('  %s  -- %s' % (full, tag))
            for p, l in sorted(sites):
                print('      %s:%d' % (p, l))
    if ambig:
        print('WARN [2] bare names with two in-scope public declarations:')
        for mod, short, hits in sorted(ambig):
            print('  %s uses bare `%s`:' % (mod, short))
            for ns, ms in hits:
                print('      %s.%s   from %s' % (ns, short, ', '.join(ms)))

print('Declaration-collision scan: %d redeclaration(s), %d ambiguity finding(s) '
      '(WARN level, non-blocking).' % (len(redecl), len(ambig)))
PYTHON
