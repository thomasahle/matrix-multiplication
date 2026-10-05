#!/usr/bin/env bash
# Check that no tracked Lean source imports a provenance-quarantined generated artifact.
#
# `scripts/artifact_provenance_quarantine.txt` lists the eab2c7 retained-exponent payload: modules
# whose numbers come from the ARCHIVED (uncorrected) evaluator complement table, whose retained
# exponent is therefore 8.200434 rather than the corrected 8.160594, and which were refuted for
# endpoint use on 2026-08-28 (commit 8a8e110).  Their theorems remain kernel-true as statements
# about the emitted arrays; what must not happen is a new client reaching them, because such a
# client silently inherits a refuted provenance while every other gate stays green.  That is exactly
# the failure mode that cost the volume-only milestone a week, and this script mechanizes the hold
# so that it survives the agents who agreed to it.
#
# Two conventions are borrowed from scripts/check_source_coverage.sh:
#
#   * only TRACKED `.lean` files (`git ls-files`) are scanned, because a clean checkout — and
#     therefore CI — is what a downstream reader actually builds;
#   * quarantined modules importing each other are internal to the payload and are ignored.
#
# Any other import edge into the list is a hard failure unless it appears in the grandfathered
# consumer allowlist below.  That allowlist may ONLY SHRINK: an edge on it that no longer exists is
# reported as a stale notice (the debt shrank, so failing on it would be failing on an improvement),
# and nothing may be added without retiring the quarantine itself.
set -euo pipefail
cd "$(dirname "$0")/.."

quarantine_file='scripts/artifact_provenance_quarantine.txt'

# The three live consumers as measured on 2026-08-28 (ROUTING VERDICT Q4).  Format:
# `<importing module> -> <quarantined module>`.
#
# These are the only DIRECT edges; the paths that make them load-bearing are transitive:
#   * MatrixMultiplicationCertificate -> SimplifiedRetainedCompressionSeam -> SimplifiedSharpEndpoint
#     -> Generated.SimplifiedExponentScalarData (the certificate library root reaches the payload);
#   * AxiomAuditCertificate.SimplifiedSequencePackaging
#     -> MatrixMultiplication.SimplifiedSequencePackaging -> SimplifiedRetainedCompressionSeam
#     (the payload is axiom-audited through the packaging);
#   * SimplifiedCoarseEndpoint is reached from the MatrixMultiplication library umbrella.
# Their `Reconstruction` predicates stay true-but-uninstantiable; see the honest-limits prose in
# each module.  When the sound total-weight (e7987) track replaces one, delete its line here.
grandfathered_consumers=(
  'MatrixMultiplication.SimplifiedSharpEndpoint -> MatrixMultiplication.Generated.SimplifiedExponentScalarData'
  'MatrixMultiplication.SimplifiedCoarseEndpoint -> MatrixMultiplication.Generated.SimplifiedExponentCoarseFloors'
  'MatrixMultiplication.SimplifiedRetainedCompressionSeam -> MatrixMultiplication.Generated.SimplifiedExponentCoarseFloors'
)

if [[ ! -f "$quarantine_file" ]]; then
  echo "FAIL: $quarantine_file is missing; the eab2c7 provenance hold has no list to enforce." >&2
  exit 1
fi

quarantined="$(sed -e 's/#.*//' -e 's/[[:space:]]//g' "$quarantine_file" | grep -v '^$' | sort -u)"
if [[ -z "$quarantined" ]]; then
  echo "FAIL: $quarantine_file lists no modules; it may only shrink by deleting the artifacts." >&2
  exit 1
fi

indent() {
  sed 's/^/  /' >&2
}

# Quarantine entries whose source is gone: the artifact was deleted, so the entry is stale.
missing_quarantined=''
while IFS= read -r module; do
  [[ -n "$module" ]] || continue
  path="$(printf '%s\n' "$module" | tr '.' '/').lean"
  if [[ ! -f "$path" ]]; then
    missing_quarantined="$missing_quarantined$module"$'\n'
  fi
done <<< "$quarantined"
missing_quarantined="$(printf '%s' "$missing_quarantined" | grep -v '^$' || true)"

# Every `import <quarantined>` edge from a tracked file that is not itself quarantined.
#
# Both membership probes read `$quarantined` through a HERE-STRING rather than a pipe.  With a
# pipe, `grep -q` exits on its first match while `printf` is still writing, `printf` takes SIGPIPE,
# and the `set -o pipefail` above turns the successful probe into status 141 — so a *matching*
# module would be reported as not quarantined.  The list is short enough today that it fits in the
# pipe buffer and the race never fires, but the same shape had silently disabled three gates in
# scripts/check_source_coverage.sh, so it is not left in place here.  It also removes one forked
# subshell per probe, i.e. two per tracked source.
edges="$(
  git ls-files -- '*.lean' | while IFS= read -r file; do
    importer="${file%.lean}"
    importer="${importer//\//.}"
    if grep -qxF "$importer" <<<"$quarantined"; then
      continue
    fi
    while IFS= read -r imported; do
      if grep -qxF "$imported" <<<"$quarantined"; then
        printf '%s -> %s\n' "$importer" "$imported"
      fi
    done < <(sed -n 's/^import[[:space:]]\{1,\}\([A-Za-z0-9_.]*\)[[:space:]]*$/\1/p' "$file")
  done | sort -u
)"

allowed="$(printf '%s\n' "${grandfathered_consumers[@]}" | sort -u)"

unlisted="$(comm -23 <(printf '%s\n' "$edges" | grep -v '^$') <(printf '%s\n' "$allowed"))"
stale="$(comm -13 <(printf '%s\n' "$edges" | grep -v '^$') <(printf '%s\n' "$allowed"))"

fail=0
if [[ -n "$unlisted" ]]; then
  echo 'FAIL: tracked Lean sources import a provenance-quarantined eab2c7 retained artifact:' >&2
  printf '%s\n' "$unlisted" | indent
  echo 'The retained exponent behind that payload is an archived-complement-table artifact' >&2
  echo '(8.200434, against the corrected 8.160594 < 8.2) and was refuted for endpoint use.  Point the' >&2
  echo 'client at the sound total-weight (e7987) track — MatrixMultiplication/TotalQuotient* —' >&2
  echo "rather than adding a line to the grandfathered consumer allowlist in $0." >&2
  fail=1
fi

if [[ -n "$missing_quarantined" ]]; then
  echo "NOTICE: $quarantine_file is stale — $(printf '%s\n' "$missing_quarantined" | grep -c .) entr(ies) name a deleted source." >&2
  echo '        The list may only shrink: remove those lines.' >&2
  printf '%s\n' "$missing_quarantined" | indent
fi

# A stale allowlist entry means a consumer was retired, which is the outcome this gate exists to
# reach; report it so the list actually shrinks, but never fail on the improvement.
if [[ -n "$stale" ]]; then
  echo "NOTICE: the grandfathered consumer allowlist is stale — $(printf '%s\n' "$stale" | grep -c .) edge(s) no longer exist." >&2
  echo "        The list may only shrink: delete those lines from $0." >&2
  printf '%s\n' "$stale" | indent
fi

if ((fail == 0)); then
  echo "Artifact provenance clean: $(printf '%s\n' "$quarantined" | grep -c .) quarantined eab2c7 modules, $(printf '%s\n' "$edges" | grep -c . || true) grandfathered import edge(s)."
fi
exit "$fail"
