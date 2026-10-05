#!/usr/bin/env bash
# Regenerate the two `CensusRoots.lean` import manifests, or check the committed ones.
#
# `#axiom_census` can only see modules it imports, so the census closure must equal the build.
# `scripts/check_source_coverage.sh` reports the gap as
#   "NOTICE: N module(s) are built only because a focused audit imports them"
# and this script closes it: it takes exactly that list, reduces it to its MAXIMAL elements
# (importing a module pulls its whole cone, so only the roots are needed), splits those roots by
# whether they reach `MatrixMultiplication.Generated.*`, and writes one manifest per census tier.
#
# The split is the layering rule, not a heuristic: roots that reach generated numeral tables go to
# the opt-in certificate census, so the ordinary census stays independent of them.
#
# Usage:
#   bash scripts/regen_census_roots.sh          # check only; prints a NOTICE if stale, exit 0
#   bash scripts/regen_census_roots.sh --write  # rewrite both manifests
#
# Checking never fails the build: a stale manifest means modules landed since the last
# regeneration, which is normal mid-campaign, and the coverage gate already reports the gap.
set -euo pipefail
cd "$(dirname "$0")/.."

WRITE=0
[[ "${1:-}" == "--write" ]] && WRITE=1

# The coverage gate's module set comes partly from the worktree listing, so a dirty tree (other
# lanes' untracked work) changes which modules look maximal. CI judges a clean checkout; so should
# this. Warn rather than refuse, because mid-campaign the shared tree is essentially never clean.
if [[ -n "$(git status --porcelain -- AlgebraicComplexity AxiomAudit AxiomAuditCertificate MatrixMultiplication 2>/dev/null | head -1)" ]]; then
  echo 'WARNING: worktree has uncommitted Lean sources; the manifests derived here may not match a'
  echo '         clean checkout. Regenerate in a clean detached worktree before landing.' >&2
fi

ORDINARY='AxiomAudit/CensusRoots.lean'
CERTIFICATE='AxiomAuditCertificate/CensusRoots.lean'

# The manifests change the very coverage they are derived from, so measuring with them in place
# is self-referential: the second run would see only what the first run missed and shrink the
# manifests to that. Neutralise them to import-free stubs, measure, then restore. This is what
# makes the script idempotent -- running it twice in a row is a no-op.
STUB='/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/
'
saved_ordinary="$(mktemp)"
saved_certificate="$(mktemp)"
restore_manifests() {
  [[ -s "$saved_ordinary" ]] && cp "$saved_ordinary" "$ORDINARY"
  [[ -s "$saved_certificate" ]] && cp "$saved_certificate" "$CERTIFICATE"
  rm -f "$saved_ordinary" "$saved_certificate"
}
trap restore_manifests EXIT
[[ -f "$ORDINARY" ]] && cp "$ORDINARY" "$saved_ordinary"
[[ -f "$CERTIFICATE" ]] && cp "$CERTIFICATE" "$saved_certificate"
[[ -f "$ORDINARY" ]] && printf '%s' "$STUB" > "$ORDINARY"
[[ -f "$CERTIFICATE" ]] && printf '%s' "$STUB" > "$CERTIFICATE"

# The coverage gate exits non-zero whenever any of its classes fail; we only want its NOTICE.
coverage_stderr="$(mktemp)"
bash scripts/check_source_coverage.sh >/dev/null 2>"$coverage_stderr" || true

restore_manifests
trap - EXIT

python3 - "$coverage_stderr" "$WRITE" "$ORDINARY" "$CERTIFICATE" <<'PYTHON'
import os, re, subprocess, sys

stderr_path, write, ordinary_path, certificate_path = sys.argv[1], sys.argv[2] == '1', sys.argv[3], sys.argv[4]

# 1. the audit-only list, straight from the gate's NOTICE block
lines = open(stderr_path, encoding='utf-8', errors='replace').read().split('\n')
audit_only, collecting = [], False
for line in lines:
    if 'built only because a focused audit imports them' in line:
        collecting = True
        continue
    if collecting:
        if line.startswith('  ') and line.strip() and not line.startswith('    so no'):
            candidate = line.strip()
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']*", candidate):
                audit_only.append(candidate)
                continue
        if line.strip() and not line.startswith(' '):
            break
audit_only = sorted(set(audit_only))

# 2. the committed import graph
tracked = subprocess.run(['git', 'ls-files', '-z', '*.lean'], capture_output=True, check=True).stdout
files = [f for f in tracked.decode('utf-8').split('\0') if f and not f.startswith('better_bound/')]
imp = re.compile(r'^import\s+([A-Za-z_][A-Za-z0-9_.]*)')
graph, exists = {}, set()
for path in files:
    module = path[:-5].replace('/', '.')
    exists.add(module)
    deps = []
    try:
        for line in open(path, encoding='utf-8').read().split('\n'):
            m = imp.match(line)
            if m:
                deps.append(m.group(1))
    except (OSError, UnicodeDecodeError):
        pass
    graph[module] = deps

members = set(audit_only) & exists

# 3. maximal elements: a member imported by another member is already covered
imported = {d for m in members for d in graph.get(m, []) if d in members}
roots = sorted(members - imported)

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

def reaches_generated(m):
    return any(x.startswith('MatrixMultiplication.Generated.') for x in closure(m))

certificate_roots = [r for r in roots if reaches_generated(r)]
ordinary_roots = [r for r in roots if not reaches_generated(r)]

covered = set()
for r in roots:
    covered |= closure(r) & members

HEADER = """/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

"""

def render(roots_list, tier, covers, client):
    body = HEADER + ''.join('import %s\n' % r for r in roots_list)
    body += """
/-!
# Census import roots for the %s target

GENERATED FILE -- regenerate with `bash scripts/regen_census_roots.sh --write`; do not edit by
hand.

`#axiom_census` can only see modules it imports, so the census closure has to equal the build.
Some modules are built only because a focused `#assert_axioms` audit imports them, which puts
them inside the build but outside every census closure -- a hole in the trust policy rather than
a cosmetic gap, since `%s` is what actually walks `Environment.constants`.

This module imports the %d maximal such modules for this tier, which pulls %d of them in total
(importing a module pulls its whole cone, so only the roots are listed). It declares nothing; it
exists purely to widen the closure of `%s`.

Tier split: a root that reaches `MatrixMultiplication.Generated.*` belongs to the opt-in
certificate census instead, so this file %s.
-/
""" % (tier, client, len(roots_list), covers, client,
       'contains no root that reaches the generated numeral tables'
       if tier == 'ordinary AxiomAudit' else
       'is where the generated numeral tables are covered')
    return body

ordinary_covers = len(set().union(*[closure(r) & members for r in ordinary_roots]) if ordinary_roots else set())
certificate_covers = len(set().union(*[closure(r) & members for r in certificate_roots]) if certificate_roots else set())

wanted = {
    ordinary_path: render(ordinary_roots, 'ordinary AxiomAudit', ordinary_covers, 'AxiomAudit.CensusAll'),
    certificate_path: render(certificate_roots, 'opt-in AxiomAuditCertificate', certificate_covers, 'AxiomAuditCertificate.Census'),
}

print('audit-only modules: %d   maximal roots: %d (ordinary %d, certificate %d)   covered: %d/%d'
      % (len(members), len(roots), len(ordinary_roots), len(certificate_roots), len(covered), len(members)))

# every emitted import must name a real tracked module -- the realistic failure for an
# import-only file, and cheap to rule out without a kernel
missing = [r for r in roots if r not in exists]
if missing:
    print('REFUSING: %d emitted import(s) name no tracked module: %s' % (len(missing), missing[:5]))
    sys.exit(1)

stale = []
for path, text in wanted.items():
    current = open(path, encoding='utf-8').read() if os.path.exists(path) else None
    if current != text:
        stale.append(path)
    if write:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        open(path, 'w', encoding='utf-8').write(text)

if write:
    print('Wrote %s and %s.' % (ordinary_path, certificate_path))
elif stale:
    print('NOTICE: census root manifest(s) are stale: %s' % ', '.join(stale))
    print('        Regenerate with: bash scripts/regen_census_roots.sh --write')
else:
    print('Census root manifests are current.')
PYTHON

rm -f "$coverage_stderr"
