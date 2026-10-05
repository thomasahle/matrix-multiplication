#!/usr/bin/env bash
# Frontier record gate: a PR that moves `frontierConstant` must move it *down by at least*
# `Frontier.recordDelta`, and Lean must be the one to say so.
#
#   scripts/check_frontier_improvement.sh <base-ref>
#
# Extracts `Frontier.frontierConstant` from `<base-ref>:Frontier.lean` and from the working tree,
# and — when they differ — synthesizes and compiles
#
#     example : (new : ℚ) + delta ≤ (old : ℚ) := by norm_num
#
# where `delta` is read from `Frontier.recordDelta` in the working tree rather than duplicated
# here. A record PR therefore cannot regress the leaderboard, cannot tie, cannot pass by asserting
# an ordering in prose, and cannot claim a record for shaving a final digit off an existing search.
# The comparison is exact: both are rationals, never `Real` literals.
#
# Set FRONTIER_LEAN to run a compiler other than `lake env lean` (used to test this script from an
# isolated build farm while the worktree build lock is held).
set -euo pipefail
cd "$(dirname "$0")/.."

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <base-ref>" >&2
  exit 2
fi
base_ref="$1"

# The definition is a single line by construction; `Frontier.lean` is a statement anchor and is
# reviewed as one, so a fragile-looking grep here is a feature: it fails loudly rather than
# guessing if someone reformats the record.
extract_definition() {
  awk -v name="$1" '
    $0 ~ ("^def " name " : ℚ :=") {
      sub("^def " name " : ℚ :=[[:space:]]*", "")
      gsub(/[[:space:]]/, "")
      if (length($0) == 0) { exit 1 }
      print
      found = 1
      exit 0
    }
    END { if (!found) exit 1 }
  '
}

if ! new_constant="$(extract_definition frontierConstant < Frontier.lean)"; then
  echo 'FAIL: could not read `def frontierConstant : ℚ := ...` from Frontier.lean.' >&2
  echo 'The frontier constant must stay a one-line rational definition.' >&2
  exit 1
fi

# The minimum record improvement lives in Lean, next to the constant it governs.
if ! record_delta="$(extract_definition recordDelta < Frontier.lean)"; then
  echo 'FAIL: could not read `def recordDelta : ℚ := ...` from Frontier.lean.' >&2
  echo 'The minimum record improvement must stay a one-line rational definition.' >&2
  exit 1
fi

if ! old_constant="$(git show "$base_ref:Frontier.lean" 2>/dev/null | extract_definition frontierConstant)"; then
  echo "NOTE: $base_ref has no readable Frontier.lean; treating this as the inaugural record" \
    "$new_constant."
  exit 0
fi

if [[ "$old_constant" == "$new_constant" ]]; then
  echo "Frontier record unchanged at $new_constant; nothing to compare."
  exit 0
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

cat > "$work/FrontierImprovement.lean" <<EOF
import Mathlib.Tactic.NormNum

/-!
Synthesized by \`scripts/check_frontier_improvement.sh\`.  A frontier record PR is admissible only
if the new constant beats the one it replaces by at least \`Frontier.recordDelta\`, and only if Lean
agrees.
-/

example : (($new_constant : ℚ)) + ($record_delta : ℚ) ≤ (($old_constant : ℚ)) := by norm_num
EOF

echo "Frontier record: $old_constant -> $new_constant; asking Lean to confirm the improvement" \
  "is at least delta = $record_delta."
if [[ -n "${FRONTIER_LEAN:-}" ]]; then
  # shellcheck disable=SC2086
  lean_status=0
  $FRONTIER_LEAN "$work/FrontierImprovement.lean" || lean_status=$?
else
  lean_status=0
  lake env lean "$work/FrontierImprovement.lean" || lean_status=$?
fi

if [[ "$lean_status" -ne 0 ]]; then
  echo >&2
  echo "FAIL: $new_constant does not beat $old_constant by the minimum record improvement" \
    "delta = $record_delta." >&2
  echo "A record claim must satisfy  new + $record_delta <= old  in exact rationals" \
    "(Frontier.recordDelta)." >&2
  echo 'Without that floor the cheapest route onto the leaderboard is to run an existing numerical' >&2
  echo 'search slightly longer and shave a final digit, which moves the constant with no new' >&2
  echo 'mathematics. A genuine sub-delta improvement is still welcome: batch it, or send it as a' >&2
  echo "non-record pull request tightening the existing entry's stated constant. See" >&2
  echo 'CONTRIBUTING.md section 3.' >&2
  exit 1
fi

echo "OK: $new_constant + $record_delta <= $old_constant is machine-checked."
