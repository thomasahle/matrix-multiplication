#!/usr/bin/env bash
# Enforce the reusable tensor import boundary at two strengths.
#
# 1. The stable `AlgebraicComplexity.Tensor` umbrella may reach only
#    `AlgebraicComplexity.Tensor.*` and the Mathlib-only shared analysis leaf
#    `AlgebraicComplexity.Asymptotics{Defs,}` pair.
# 2. Every source physically under `AlgebraicComplexity/Tensor/` is checked for
#    direct higher-layer imports. Five pre-existing bridge edges are listed
#    explicitly below; no new exception can enter unnoticed.
set -euo pipefail
cd "$(dirname "$0")/.."

list_project_lean_files() {
  if command -v rg >/dev/null 2>&1; then
    rg --files AlgebraicComplexity -g '*.lean'
  else
    find AlgebraicComplexity -type f -name '*.lean'
  fi
}

# Parse only the Lean module header. In particular, ignore apparent imports in
# line comments and arbitrarily nested block comments, and recognize Lean's
# `public import` and `private import` forms.
import_lines="$(list_project_lean_files | xargs awk '
  FNR == 1 { commentDepth = 0 }

  function withoutComments(line,    clean, i, pair) {
    clean = ""
    i = 1
    while (i <= length(line)) {
      pair = substr(line, i, 2)
      if (commentDepth > 0) {
        if (pair == "/-") {
          commentDepth++
          i += 2
        } else if (pair == "-/") {
          commentDepth--
          i += 2
        } else {
          i++
        }
      } else if (pair == "--") {
        break
      } else if (pair == "/-") {
        commentDepth++
        i += 2
      } else {
        clean = clean substr(line, i, 1)
        i++
      }
    }
    return clean
  }

  {
    line = withoutComments($0)
    if (line ~ /^[[:space:]]*((public|private)[[:space:]]+)?import[[:space:]]/) {
      print FILENAME ":" line
      next
    }
    header = line
    gsub(/^[[:space:]]+|[[:space:]]+$/, "", header)
    if (header == "" || header == "module" || header == "prelude") {
      next
    }
    nextfile
  }
' || true)"

edges="$(printf '%s\n' "$import_lines" | awk '
  {
    colon = index($0, ":")
    if (colon == 0) {
      next
    }
    source = substr($0, 1, colon - 1)
    sub(/[.]lean$/, "", source)
    gsub(/\//, ".", source)
    line = substr($0, colon + 1)
    n = split(line, field, /[[:space:]]+/)
    first = 0
    if (field[1] == "import") {
      first = 2
    } else if ((field[1] == "public" || field[1] == "private") && field[2] == "import") {
      first = 3
    }
    for (i = first; first != 0 && i <= n; i++) {
      if (field[i] == "AlgebraicComplexity" ||
          field[i] ~ /^AlgebraicComplexity[.][A-Za-z0-9_.]+$/) {
        print source, field[i]
      }
    }
  }
')"

umbrella_violations="$(printf '%s\n' "$edges" | awk '
  { edge[$1 SUBSEP $2] = 1 }
  END {
    root = "AlgebraicComplexity.Tensor"
    reachable[root] = 1
    changed = 1
    while (changed) {
      changed = 0
      for (e in edge) {
        split(e, endpoint, SUBSEP)
        source = endpoint[1]
        target = endpoint[2]
        if (reachable[source] && !reachable[target]) {
          reachable[target] = 1
          changed = 1
        }
      }
    }
    for (module in reachable) {
      if (reachable[module] && module != root &&
          index(module, "AlgebraicComplexity.Tensor.") != 1 &&
          module != "AlgebraicComplexity.Asymptotics" &&
          module != "AlgebraicComplexity.AsymptoticsDefs") {
        print module
      }
    }
  }
' | sort)"

if [[ -n "$umbrella_violations" ]]; then
  echo 'FAIL: AlgebraicComplexity.Tensor transitively imports higher-layer modules:' >&2
  printf '%s\n' "$umbrella_violations" >&2
  exit 1
fi

# These bridge modules predate the physical-directory rule. They remain out of
# the stable umbrella and are pending relocation. Keep
# this list edge-specific: changing either endpoint requires explicit review.
directory_violations="$(printf '%s\n' "$edges" | awk '
  function grandfathered(source, target, key) {
    key = source SUBSEP target
    return key == "AlgebraicComplexity.Tensor.TypeExtraction" SUBSEP \
        "AlgebraicComplexity.Combinatorics.WordType" ||
      key == "AlgebraicComplexity.Tensor.IndependenceBlockEntropy" SUBSEP \
        "AlgebraicComplexity.Analysis.Subexponential" ||
      key == "AlgebraicComplexity.Tensor.IndependenceBlockEntropy" SUBSEP \
        "AlgebraicComplexity.Combinatorics.WordType" ||
      key == "AlgebraicComplexity.Tensor.IndependenceBlockEntropy" SUBSEP \
        "AlgebraicComplexity.Probability.EntropyValue" ||
      key == "AlgebraicComplexity.Tensor.IndependenceBlockEntropy" SUBSEP \
        "AlgebraicComplexity.Probability.Finite"
  }

  index($1, "AlgebraicComplexity.Tensor.") == 1 &&
      index($2, "AlgebraicComplexity.Tensor.") != 1 &&
      $2 != "AlgebraicComplexity.Asymptotics" &&
      $2 != "AlgebraicComplexity.AsymptoticsDefs" &&
      !grandfathered($1, $2) {
    print $1 " -> " $2
  }
' | sort)"

if [[ -n "$directory_violations" ]]; then
  echo 'FAIL: a Tensor/ source directly imports a non-tensor higher layer:' >&2
  printf '%s\n' "$directory_violations" >&2
  echo 'Move the mixed statement above Tensor/, or review the boundary explicitly.' >&2
  exit 1
fi

echo 'Tensor boundary clean; five pre-existing bridge edges are explicitly grandfathered.'
