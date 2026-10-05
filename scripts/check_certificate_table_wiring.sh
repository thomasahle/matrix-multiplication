#!/usr/bin/env bash
# Check that every module's *quoted certificate* agrees with the *primary tables its proofs
# actually reference*.
#
# ## The failure this exists to catch
#
# The generated-module exporter takes both a certificate and a `--primary-lean-family` /
# `--primary-tables-term` pair.  Re-running it over a new certificate while those flags keep their
# previous defaults emits modules whose header docstring advertises certificate A while every proof
# in the body is stated about family B's tables.  Such a module still *builds* — it is a true
# theorem about the wrong data — so no amount of Lean checking notices, and every downstream reader
# believes the numbers were certified against A.  That is how a proposition the kernel later proved
# FALSE entered the tree: modules headed `e7987d7f...` (TotalQuotientPrimary) whose proofs reference
# `generatedPrimaryTables`, which is the `eab2c7ae...` SimplifiedVolume family.  The literals
# reproduce the other family exactly: 0 of 1620 records are unrealizable under TotalQuotientPrimary,
# 111 of 1620 under SimplifiedVolume.
#
# ## What is checked
#
# For every Lean module, the checker resolves three independent facts and demands they agree:
#
#   1. the certificate SHA-256 quoted in a `/-!` module docstring;
#   2. the primary-table *term* the module's proofs reference (`generatedPrimaryTables`,
#      `TotalQuotientVolumeReconstruction.primaryTables`, ...), resolved to a family by reading the
#      term's OWN definition site — not the referencing module's `open` lines;
#   3. the `Generated.<Family>` namespace the module `open`s.
#
#   header-vs-term  (1) vs (2)  the quoted digest is not the digest of the family whose tables the
#                               proofs are stated about.  This is the exact defect above.
#   open-vs-term    (3) vs (2)  the module opens one family's data namespace but its proofs are
#                               stated about another family's tables.  This catches the same
#                               exporter misconfiguration when the header happens to be right, and
#                               is the only rule that can see a module carrying no digest at all.
#
# Rule (2) is the load-bearing subtlety, and it is what a human reviewer gets wrong: Lean resolves
# the *body* of `generatedPrimaryTables` at that definition's own site, so a local
# `open MatrixMultiplication.Generated.TotalQuotientPrimary` does NOT retarget it.  A staging module
# can therefore carry the right namespace, the right `open`, and the right header while still
# proving things about the other family.  `open-vs-term` exists precisely because that decoy reads
# as correct.
#
# Families, digests, and terms are all discovered from the tree; nothing here is hardcoded.
# `Generated/*Manifest.lean` supplies `<Family> -> certificateSHA256`, and a digest counts as
# family-identifying only when it distinguishes families: digests shared by every manifest
# (`archiveSHA256`, `sourceCertificateSHA256`) carry no family information and are ignored.
#
# ## What is deliberately NOT checked
#
#   * Numeric content.  This is a static wiring check; it never reads a certificate blob, never
#     recomputes a SHA-256, and cannot tell you that a literal is wrong -- only that the module is
#     stated about a different family than it advertises.
#   * Modules that reference no primary-table term.  The overwhelming majority of generated modules
#     are pure data tables; a header digest alone is not a claim about which tables a proof uses, so
#     they are out of scope and are never flagged.
#   * Import-graph reachability.  A module that reaches the wrong family transitively through a
#     helper, without naming a primary-table term itself, is invisible here.  See RISKS below.
#   * Whether a manifest's own digest matches its certificate file.  That is provenance, covered by
#     scripts/check_artifact_provenance.sh.
#
# ## Repository, not working tree
#
# Five lanes hold uncommitted edits, so the working tree is nobody's build.  The gate therefore
# analyzes `git archive HEAD` extracted to a temp dir -- the exact bytes a clean checkout and CI
# compile.  `git archive` is used over per-file `git show` because it is one pass (~3s for 12.8k
# sources) instead of ~13k subprocesses, and over `git ls-files` because that still reads worktree
# bytes.  It also excludes untracked scratch copies of the tree for free.  `--worktree` overrides
# this for local pre-commit use and is the mode that shows a lane its own in-flight breakage.
#
# ## Grandfathering
#
# Violations are keyed `<path>#<rule>` and diffed against scripts/certificate_table_wiring_grandfathered.txt.
# That list is APPEND-BLOCKED and may only shrink: an unlisted violation fails the gate, while a
# listed entry that no longer violates is a stale-entry NOTICE rather than a failure, so paying the
# debt down can never fail on the commit that pays it.  Regenerate deliberately with `--update`.
#
# Usage: scripts/check_certificate_table_wiring.sh [--worktree] [--update]
set -euo pipefail
cd "$(dirname "$0")/.."

grandfather_file='scripts/certificate_table_wiring_grandfathered.txt'
source_mode='head'
update_grandfather_file=0

for arg in "$@"; do
  case "$arg" in
    --worktree) source_mode='worktree' ;;
    --update) update_grandfather_file=1 ;;
    *)
      echo "usage: $0 [--worktree] [--update]" >&2
      exit 2
      ;;
  esac
done

if [[ "$source_mode" == 'head' ]]; then
  if ! command -v git >/dev/null 2>&1 || ! git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    echo "NOTICE: not a git worktree; analyzing the working tree instead of HEAD." >&2
    source_mode='worktree'
  fi
fi

scan_root='.'
tmp_root=''
file_list=''
cleanup() {
  [[ -n "$tmp_root" ]] && rm -rf "$tmp_root"
  [[ -n "$file_list" ]] && rm -f "$file_list"
  return 0
}
trap cleanup EXIT

if [[ "$source_mode" == 'head' ]]; then
  tmp_root="$(mktemp -d)"
  git archive HEAD | tar -x -C "$tmp_root"
  scan_root="$tmp_root"
elif command -v git >/dev/null 2>&1 && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  # Worktree mode still restricts to *tracked* paths.  Lanes keep untracked full-tree copies under
  # scratchpad/, and walking those would report each finding twice under a path nobody builds.
  file_list="$(mktemp)"
  git ls-files -z -- '*.lean' | tr '\0' '\n' > "$file_list"
fi

# Per-file Lean parsing is delegated to python3 (stdlib only): it walks the tree itself, so no
# `grep -r` with a file glob is ever constructed.  That combination silently returns zero matches
# under ugrep -- which is how a whole class of "passing" checks checked nothing.
records="$(SCAN_ROOT="$scan_root" FILE_LIST="$file_list" python3 - <<'PY'
import os
import re
import sys

root = os.environ['SCAN_ROOT']
file_list = os.environ.get('FILE_LIST') or ''


def candidate_paths():
    """Relative .lean paths to analyze.

    With FILE_LIST set (worktree mode) the set is exactly git's tracked sources; otherwise the
    scan root is an extracted `git archive HEAD` and everything under it is in scope.
    """
    if file_list:
        with open(file_list, encoding='utf-8') as handle:
            for line in handle:
                rel = line.strip()
                if rel.endswith('.lean'):
                    yield rel
        return
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in ('.git', '.lake', '.venv', '__pycache__')]
        for name in filenames:
            if name.endswith('.lean'):
                yield os.path.relpath(os.path.join(dirpath, name), root)


# ---------------------------------------------------------------- collect sources
sources = {}
for rel in candidate_paths():
    full = os.path.join(root, rel)
    try:
        with open(full, encoding='utf-8') as handle:
            sources[rel] = handle.read()
    except FileNotFoundError:
        continue          # tracked but deleted in the worktree
    except (OSError, UnicodeDecodeError) as exc:
        print('ERROR\t%s\t0\tunreadable source: %s' % (rel, exc))

if not sources:
    print('ERROR\t<scan>\t0\tno .lean sources found under %s' % root)
    sys.exit(0)

DIGEST_IN_DOC = re.compile(r'`([0-9a-f]{64})`')
DOC_BLOCK = re.compile(r'/-!.*?-/', re.S)
SHA_FIELD = re.compile(r'^\s*def\s+([A-Za-z0-9_]+)\s*:\s*String\s*:=\s*"([0-9a-f]{64})"', re.M)
MANIFEST_NS = re.compile(r'^namespace\s+MatrixMultiplication\.Generated\.([A-Za-z0-9_]+)\.Manifest\s*$', re.M)
BINDING_DEF = re.compile(
    r'^(?:noncomputable\s+|private\s+|protected\s+)*'
    r'(?:def|abbrev)\s+([A-Za-z0-9_]+)\s*:\s*PrimaryTables\s+where\s*$', re.M)
NAMESPACE_LINE = re.compile(r'^namespace\s+([A-Za-z0-9_.]+)\s*$', re.M)
GENERATED_QUALIFIER = re.compile(r'(?:^|[^A-Za-z0-9_.])Generated\.([A-Za-z0-9_]+)\.')
OPEN_GENERATED = re.compile(r'^\s*open\s+(?:scoped\s+)?(.*)$', re.M)
OPEN_FAMILY = re.compile(r'MatrixMultiplication\.Generated\.([A-Za-z0-9_]+)')


def line_of(text, index):
    return text.count('\n', 0, index) + 1


def doc_spans(text):
    return [(m.start(), m.group(0)) for m in DOC_BLOCK.finditer(text)]


def namespace_stack_at(text, index):
    """Namespace path in force at a character offset, honouring `namespace`/`end` nesting."""
    stack = []
    for line in text[:index].split('\n'):
        stripped = line.strip()
        m = re.match(r'^namespace\s+([A-Za-z0-9_.]+)$', stripped)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r'^end\s+([A-Za-z0-9_.]+)$', stripped)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
    return '.'.join(stack)


def opened_families(text):
    families = set()
    for m in OPEN_GENERATED.finditer(text):
        for f in OPEN_FAMILY.findall(m.group(1)):
            families.add(f)
    return families


# ---------------------------------------------------------------- family -> digests
# A digest identifies a family only when it is not shared with another family.  archiveSHA256 and
# sourceCertificateSHA256 are identical across manifests and are therefore discarded here.
manifest_fields = {}   # family -> {field: digest}
for rel, text in sorted(sources.items()):
    ns = MANIFEST_NS.search(text)
    if not ns:
        continue
    manifest_fields[ns.group(1)] = dict(
        (m.group(1), m.group(2)) for m in SHA_FIELD.finditer(text))

if not manifest_fields:
    print('ERROR\t<scan>\t0\tno Generated/*Manifest.lean modules found; the family->digest map '
          'would be empty and every module would vacuously pass')
    sys.exit(0)

digest_users = {}
for family, fields in manifest_fields.items():
    for digest in set(fields.values()):
        digest_users.setdefault(digest, set()).add(family)

identifying = dict(
    (digest, next(iter(families)))
    for digest, families in digest_users.items() if len(families) == 1)

certificate_digest = {}
for family, fields in manifest_fields.items():
    if 'certificateSHA256' in fields:
        certificate_digest[family] = fields['certificateSHA256']

# ---------------------------------------------------------------- primary-table term bindings
bindings = {}   # simple name -> (family, fully qualified name)
for rel, text in sorted(sources.items()):
    for m in BINDING_DEF.finditer(text):
        name = m.group(1)
        ns = namespace_stack_at(text, m.start())
        body = text[m.end():]
        # The structure-instance field block: indented lines up to the first non-indented one.
        block = []
        for line in body.split('\n'):
            if line.strip() == '':
                continue
            if not line[:1].isspace():
                break
            block.append(line)
        block = '\n'.join(block)
        # Only manifest-bearing namespaces are certificate families; sibling data namespaces such
        # as Generated.SimplifiedVolumeScalar are ordinary tables and must not enter the vote.
        families = set(GENERATED_QUALIFIER.findall(block)) & set(manifest_fields)
        if not families:
            families = opened_families(text) & set(manifest_fields)
        if len(families) != 1:
            print('ERROR\t%s\t%d\tcannot resolve a single Generated.<Family> for the '
                  'PrimaryTables binding `%s` (candidates: %s); the resolver must be taught this '
                  'shape rather than silently skipping it'
                  % (rel, line_of(text, m.start()), name, ','.join(sorted(families)) or 'none'))
            continue
        family = next(iter(families))
        full = (ns + '.' + name) if ns else name
        if name in bindings and bindings[name][0] != family:
            print('ERROR\t%s\t%d\tprimary-table term `%s` is bound to two families (%s and %s); '
                  'bare references become ambiguous and the resolver cannot be trusted'
                  % (rel, line_of(text, m.start()), name, bindings[name][0], family))
            continue
        bindings[name] = (family, full)

if not bindings:
    print('ERROR\t<scan>\t0\tno `def <name> : PrimaryTables where` bindings found; nothing could '
          'ever be resolved and every module would vacuously pass')
    sys.exit(0)

# ---------------------------------------------------------------- per-module verdicts
in_scope = 0
for rel, text in sorted(sources.items()):
    # A module never audits its own binding site.
    defines_here = set(m.group(1) for m in BINDING_DEF.finditer(text))
    opens = opened_families(text)
    ns_here = set(NAMESPACE_LINE.findall(text))

    referenced = {}   # family -> (line, spelling)
    for name, (family, full) in bindings.items():
        if name in defines_here:
            continue
        # Qualified: any suffix of the binding's full name, e.g. `A.B.primaryTables` or
        # `B.primaryTables`, but never `somethingElse.primaryTables`.
        for m in re.finditer(r'(?<![A-Za-z0-9_])([A-Za-z0-9_.]*\.)?' + re.escape(name)
                             + r'(?![A-Za-z0-9_])', text):
            prefix = (m.group(1) or '').rstrip('.')
            if prefix:
                if not (full == prefix + '.' + name or full.endswith('.' + prefix + '.' + name)):
                    continue
            else:
                # Bare reference: only counts when the binding's namespace is open or enclosing,
                # which keeps a local binder of the same name from being mistaken for the global.
                owner_ns = full[:full.rfind('.')] if '.' in full else ''
                scoped = False
                for m2 in OPEN_GENERATED.finditer(text):
                    if owner_ns and owner_ns in m2.group(1):
                        scoped = True
                for candidate in ns_here:
                    if owner_ns and (candidate == owner_ns or candidate.endswith('.' + owner_ns)
                                     or owner_ns.endswith('.' + candidate)):
                        scoped = True
                if not scoped:
                    continue
            if family not in referenced:
                referenced[family] = (line_of(text, m.start()), m.group(0))

    if not referenced:
        continue
    in_scope += 1

    if len(referenced) > 1:
        # A bridge module relating two families cannot be adjudicated by a single header digest.
        print('INFO\t%s\t0\treferences %d primary-table families (%s); not adjudicated'
              % (rel, len(referenced), ','.join(sorted(referenced))))
        continue

    term_family, (term_line, term_text) = next(iter(referenced.items()))

    # --- rule: header-vs-term
    header = []
    for start, block in doc_spans(text):
        for m in DIGEST_IN_DOC.finditer(block):
            digest = m.group(1)
            if digest in identifying:
                header.append((line_of(text, start + m.start()), digest))
    if header:
        line, digest = header[0]
        claimed = identifying[digest]
        if claimed != term_family:
            want = certificate_digest.get(term_family, '<no certificateSHA256>')
            print('MISMATCH\t%s\t%d\theader-vs-term\theader quotes %s (%s) but proofs reference '
                  '`%s` at line %d, which is bound to %s (%s)'
                  % (rel, line, digest[:12] + '...', claimed, term_text, term_line,
                     term_family, want[:12] + '...'))

    # --- rule: open-vs-term
    known_opens = set(f for f in opens if f in manifest_fields)
    if known_opens and term_family not in known_opens:
        print('MISMATCH\t%s\t%d\topen-vs-term\tmodule opens Generated.%s but proofs reference `%s`, '
              'which is bound to Generated.%s (an `open` does NOT retarget a term defined elsewhere)'
              % (rel, term_line, ','.join(sorted(known_opens)), term_text, term_family))

print('INFO\t<scan>\t0\tsources=%d manifests=%d families=%s bindings=%s in_scope=%d'
      % (len(sources), len(manifest_fields), ','.join(sorted(manifest_fields)),
         ','.join('%s->%s' % (n, f) for n, (f, _) in sorted(bindings.items())), in_scope))
PY
)"

# ---------------------------------------------------------------- structural self-check
# "A check that silently matches nothing is worse than no check at all."  Any ERROR record means
# the resolver hit a shape it does not understand; passing quietly would be the failure mode this
# gate exists to prevent, so it is fatal even in --update mode.
errors="$(printf '%s\n' "$records" | awk -F'\t' '$1 == "ERROR"')"
if [[ -n "$errors" ]]; then
  echo 'FAIL: the certificate/table wiring resolver could not interpret the tree.' >&2
  printf '%s\n' "$errors" | awk -F'\t' '{ printf "  %s:%s: %s\n", $2, $3, $4 }' >&2
  echo 'Refusing to report a clean result from an analysis that understood nothing.' >&2
  exit 1
fi

summary="$(printf '%s\n' "$records" | awk -F'\t' '$1 == "INFO" && $2 == "<scan>" { print $4 }')"
if [[ -z "$summary" ]]; then
  echo 'FAIL: the resolver produced no summary record; the scan did not complete.' >&2
  exit 1
fi

in_scope="$(printf '%s\n' "$summary" | sed -n 's/.*in_scope=\([0-9]*\).*/\1/p')"
if [[ -z "$in_scope" || "$in_scope" -eq 0 ]]; then
  echo 'FAIL: zero modules were in scope, so this gate checked nothing.' >&2
  echo "  scan summary: $summary" >&2
  exit 1
fi

violations="$(printf '%s\n' "$records" |
  awk -F'\t' '$1 == "MISMATCH" { printf "%s#%s\n", $2, $4 }' | sort -u)"

if ((update_grandfather_file == 1)); then
  {
    cat <<'HEADER'
# Modules whose quoted certificate or opened data namespace disagrees with the primary-table term
# their proofs actually reference.
#
# Each entry is `<path>#<rule>` -- see scripts/check_certificate_table_wiring.sh for what the two
# rules mean and why an `open` does not retarget a term defined in another module.
#
# The list is APPEND-BLOCKED and may only shrink.  A violation that is not listed here fails the
# gate; an entry here that no longer violates is reported as a stale-entry notice, not a failure,
# because shrinking the debt must never fail on the commit that shrank it.
#
# To retire an entry: re-export the module with the exporter's --primary-lean-family /
# --primary-tables-term flags set to the family its header names, then delete its line.
HEADER
    printf '%s\n' "$violations" | sed '/^[[:space:]]*$/d'
  } > "$grandfather_file"
  echo "Rewrote $grandfather_file with $(printf '%s\n' "$violations" | grep -c . || true) entries."
  exit 0
fi

if [[ -f "$grandfather_file" ]]; then
  grandfathered="$(sed -e 's/#\{1\}[[:space:]].*//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' \
    -e '/^$/d' "$grandfather_file" | grep -v '^#' | sort -u || true)"
else
  grandfathered=''
fi

violation_file="$(mktemp)"
grandfather_list="$(mktemp)"
printf '%s\n' "$violations" | sed '/^[[:space:]]*$/d' | sort -u > "$violation_file"
printf '%s\n' "$grandfathered" | sed '/^[[:space:]]*$/d' | sort -u > "$grandfather_list"

new_violations="$(comm -23 "$violation_file" "$grandfather_list")"
stale_entries="$(comm -13 "$violation_file" "$grandfather_list")"
grandfathered_hits="$(comm -12 "$violation_file" "$grandfather_list" | grep -c . || true)"
rm -f "$violation_file" "$grandfather_list"

echo "certificate/table wiring: scanned $summary"
echo "  source view: $source_mode"
echo "  grandfathered violations still present: $grandfathered_hits (see $grandfather_file)"

printf '%s\n' "$records" | awk -F'\t' '$1 == "INFO" && $2 != "<scan>" {
  printf "  NOTE %s:%s: %s\n", $2, $3, $4 }'

if [[ -n "$stale_entries" ]]; then
  echo "NOTICE: $grandfather_file is stale — $(printf '%s\n' "$stale_entries" | grep -c .) entr(ies) no longer violate." >&2
  echo "Remove them with: $0 --update" >&2
  printf '%s\n' "$stale_entries" | sed 's/^/  /' >&2
fi

if [[ -n "$new_violations" ]]; then
  count="$(printf '%s\n' "$new_violations" | grep -c .)"
  echo >&2
  echo "FAIL: $count new certificate/table wiring violation(s)." >&2
  echo 'A module advertises one certificate family while its proofs are stated about another.' >&2
  echo 'Such a module still builds: it is a true theorem about the wrong tables.' >&2
  echo >&2
  while IFS= read -r key; do
    [[ -z "$key" ]] && continue
    path="${key%%#*}"
    rule="${key##*#}"
    printf '%s\n' "$records" | awk -F'\t' -v p="$path" -v r="$rule" \
      '$1 == "MISMATCH" && $2 == p && $4 == r { printf "  FAIL %s:%s: [%s] %s\n", $2, $3, $4, $5 }' >&2
  done <<< "$new_violations"
  echo >&2
  echo 'Re-export the offending modules with --primary-lean-family / --primary-tables-term set to' >&2
  echo 'the family named in their header, or correct the header if the tables are the intended ones.' >&2
  exit 1
fi

echo 'OK: every module in scope quotes the certificate of the primary tables its proofs reference.'
