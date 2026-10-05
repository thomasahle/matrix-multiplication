#!/usr/bin/env bash
# Hard trust scan from DESIGN.md "Trust and verification policy".
#
# Fails when any committed Lean source in the reusable library, the client
# umbrella, or the paper library contains sorry, admit, or a declared axiom.
# `axiom` is matched only in declaration position so that docstrings discussing named
# obligations ("never an axiom") do not trip the scan.
# Prose mentions are expected to stay out of these trees; if a legitimate
# prose occurrence ever appears, review it manually and narrow the pattern
# here rather than deleting the scan.
#
# This scan is a fast PRE-FILTER, not the authority. It matches `axiom` only in declaration
# position, i.e. anchored at the start of a line, while Lean's command parser is
# whitespace-insensitive: `/-- doc -/ axiom sneaky : False` declares an axiom and passes here.
# The authority is `#axiom_census` (`AxiomAudit/Census.lean`, run by `AxiomAudit/CensusAll.lean`
# and `AxiomAuditCertificate/Census.lean`), which walks `Environment.constants` and so inspects
# what the kernel accepted rather than what the source text looks like. Keep both: this one runs
# in a second with no toolchain, and tells a contributor which line to fix.
#
# `opaque` is accepted only for the reviewed generated-certificate pattern and
# only when the declaration carries a real body.  Successful scans report the
# size of that reviewed surface without dumping hundreds of accepted locations;
# a reviewer can still obtain the locations with
# `rg -n '^\s*opaque\b' MatrixMultiplication/Generated -g '*.lean'`.
set -u
cd "$(dirname "$0")/.."

fail=0
if command -v rg >/dev/null 2>&1; then
  if rg -n '(\b(sorry|admit)\b|^\s*(@\[[^]]*\]\s*)?((private|protected|noncomputable|unsafe)\s+)*axiom\s)' \
      AlgebraicComplexity AlgebraicComplexityClients.lean MatrixMultiplication -g '*.lean'; then
    echo 'FAIL: found sorry/admit/axiom in committed Lean sources.' >&2
    fail=1
  fi
  if rg -n '^\s*opaque\b' \
      AlgebraicComplexity AlgebraicComplexityClients.lean MatrixMultiplication \
      -g '*.lean' -g '!MatrixMultiplication/Generated/**'; then
    echo 'FAIL: opaque declarations outside MatrixMultiplication/Generated require explicit policy review.' >&2
    fail=1
  fi
else
  if grep -rnE '(\b(sorry|admit)\b|^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable|unsafe)[[:space:]]+)*axiom[[:space:]])' --include='*.lean' \
      AlgebraicComplexity AlgebraicComplexityClients.lean MatrixMultiplication; then
    echo 'FAIL: found sorry/admit/axiom in committed Lean sources.' >&2
    fail=1
  fi
  if grep -rnE '^[[:space:]]*opaque\b' --include='*.lean' \
      --exclude-dir=Generated AlgebraicComplexity MatrixMultiplication; then
    echo 'FAIL: opaque declarations outside MatrixMultiplication/Generated require explicit policy review.' >&2
    fail=1
  fi
fi

# A generated `opaque` is sound for this project only when it seals an actual
# kernel-checked term. Accumulate a multiline declaration until `:=` appears;
# reaching another command or EOF first exposes a bodiless postulate. Strip
# line comments and arbitrarily nested block comments first, so prose cannot
# accidentally make a bodiless declaration appear to have a term.
generated_opaque_without_body="$(
  find MatrixMultiplication/Generated -type f -name '*.lean' -print0 2>/dev/null |
    xargs -0 awk '
      FNR == 1 {
        if (pending) {
          print origin
          pending = 0
        }
        commentDepth = 0
      }

      function withoutComments(source,    clean, i, pair) {
        clean = ""
        i = 1
        while (i <= length(source)) {
          pair = substr(source, i, 2)
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
            clean = clean substr(source, i, 1)
            i++
          }
        }
        return clean
      }

      {
        line = withoutComments($0)
        if (pending) {
          if (line ~ /:=/) {
            pending = 0
            next
          }
          if (line ~ /^[[:space:]]*(opaque|theorem|lemma|def|abbrev|structure|class|instance|example|axiom|inductive|namespace|section|end|#)/) {
            print origin
            pending = 0
          }
        }
        if (line ~ /^[[:space:]]*opaque[[:space:]]/ && line !~ /:=/) {
          pending = 1
          origin = FILENAME ":" FNR
        }
      }
      END { if (pending) print origin }
    ' || true
)"
if [ -n "$generated_opaque_without_body" ]; then
  echo 'FAIL: generated opaque declarations without an explicit body:' >&2
  printf '%s\n' "$generated_opaque_without_body" >&2
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  generated_opaque_count="$({
    find MatrixMultiplication/Generated -type f -name '*.lean' -print0 2>/dev/null |
      xargs -0 awk '/^[[:space:]]*opaque[[:space:]]/ { count++ } END { print count + 0 }'
  } | awk '{ total += $1 } END { print total + 0 }')"
  echo "Reviewed generated opaque declarations with explicit bodies: $generated_opaque_count."
  echo 'Trust scan clean.'
fi
exit "$fail"
