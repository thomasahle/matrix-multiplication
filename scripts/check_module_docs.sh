#!/usr/bin/env bash
# Require a module overview in every hand-written Lean source.
#
# Generated certificate tables are excluded: their generator owns their file
# headers, and their semantic wrapper modules remain covered by this check.
set -euo pipefail
cd "$(dirname "$0")/.."

list_handwritten_sources() {
  for file in \
      AlgebraicComplexity.lean \
      AlgebraicComplexityClients.lean \
      MatrixMultiplication.lean \
      MatrixMultiplicationCertificate.lean \
      AxiomAudit.lean \
      AxiomAuditCertificate.lean; do
    [[ -f "$file" ]] && printf '%s\n' "$file"
  done

  if command -v rg >/dev/null 2>&1; then
    rg --files AlgebraicComplexity AxiomAudit MatrixMultiplication -g '*.lean' \
      -g '!MatrixMultiplication/Generated/**'
  else
    find AlgebraicComplexity AxiomAudit MatrixMultiplication \
      -type f -name '*.lean' ! -path 'MatrixMultiplication/Generated/*'
  fi
}

missing="$(
  list_handwritten_sources | sort -u | tr '\n' '\0' |
    xargs -0 grep -L -F '/-!' || true
)"

if [[ -n "$missing" ]]; then
  echo 'FAIL: hand-written Lean sources lack a `/-! ... -/` module overview:' >&2
  printf '%s\n' "$missing" >&2
  exit 1
fi

echo 'Module documentation coverage clean.'
