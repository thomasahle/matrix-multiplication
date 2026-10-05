#!/usr/bin/env bash
# Prove that scripts/check_heartbeat_governor.sh actually fires.
#
# A gate that silently matches nothing is worse than no gate: it converts an unchecked invariant
# into a green check mark. This test therefore does not merely confirm that the gate passes on a
# clean tree -- it builds synthetic revisions that reintroduce `set_option maxHeartbeats 0` and
# asserts that the gate FAILS on each of them, with the offending file:line in its output.
#
# The payload used for the generated-module case is genuine historical content: the text a
# producer emitted before commit 252dc5e3 taught the producers to emit finite bounds. That is the
# exact regression this gate exists to catch.
#
# Everything happens in a throwaway `--local --no-checkout` clone, and every synthetic revision is
# assembled with git plumbing against a temporary index, so the test never touches the source
# repository's worktree, index, or refs, and never runs lean or lake.
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/../.."
source_repo="$PWD"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

clone="$tmp/clone"
git clone --quiet --local --no-checkout "$source_repo" "$clone"
mkdir -p "$clone/scripts/tests"
cp scripts/check_heartbeat_governor.sh scripts/heartbeat_governor_grandfathered.txt "$clone/scripts/"
check="$clone/scripts/check_heartbeat_governor.sh"

base="$(git -C "$clone" rev-parse HEAD)"

# commit_with <blob-source-file> <path-in-tree> ... -> prints the synthetic commit sha
# Builds a commit on top of $base with the given files added/replaced, using a private index.
commit_with() {
  local index="$tmp/index.$$"
  rm -f "$index"
  GIT_INDEX_FILE="$index" git -C "$clone" read-tree "$base"
  while [ "$#" -gt 0 ]; do
    local content_file="$1" tree_path="$2"; shift 2
    local blob
    blob="$(git -C "$clone" hash-object -w "$content_file")"
    GIT_INDEX_FILE="$index" git -C "$clone" update-index --add --cacheinfo "100644,$blob,$tree_path"
  done
  local tree
  tree="$(GIT_INDEX_FILE="$index" git -C "$clone" write-tree)"
  rm -f "$index"
  git -C "$clone" commit-tree "$tree" -p "$base" -m 'synthetic test revision'
}

failures=0
check_case() {  # check_case <description> <expected-exit> <rev> [<expected substring> ...]
  local description="$1" expected_exit="$2" rev="$3"; shift 3
  local out status=0
  out="$(bash "$check" --rev "$rev" 2>&1)" || status=$?
  local ok=1
  [ "$status" -eq "$expected_exit" ] || ok=0
  local needle
  for needle in "$@"; do
    case "$out" in *"$needle"*) ;; *) ok=0 ;; esac
  done
  if [ "$ok" -eq 1 ]; then
    printf 'ok    %s\n' "$description"
  else
    printf 'FAIL  %s (exit %s, expected %s)\n' "$description" "$status" "$expected_exit"
    printf '%s\n' "$out" | sed 's/^/        /'
    failures=$((failures + 1))
  fi
}

# --- 1. the current repository must stay green ---------------------------------------------------
check_case 'HEAD is clean (330 grandfathered)' 0 "$base" \
  'Heartbeat governor scan clean' \
  'pre-existing debt): 330'

# --- 2. a producer regression emits a NEW generated module with the governor off ------------------
# Real pre-252dc5e3 output, re-emitted under a new chunk name, exactly as a reverted producer would.
# Prefer the genuine pre-fix blob. A shallow CI checkout (actions/checkout default fetch-depth: 1)
# has no 252dc5e3, so fall back to the equally genuine text of a payload that still carries the
# option at HEAD -- the fixture must contain the governor line either way, and the test refuses to
# run on a fixture that does not, rather than passing vacuously.
historical='252dc5e3^:MatrixMultiplication/Generated/SimplifiedVolumeScalarPositiveData.lean'
if git -C "$clone" cat-file -e "$historical" 2>/dev/null; then
  fixture_origin='pre-252dc5e3 producer output'
else
  historical="$base:MatrixMultiplication/Generated/SimplifiedVolumeScalarPositiveData.lean"
  fixture_origin='an unregenerated payload at HEAD (shallow clone: no 252dc5e3)'
fi
git -C "$clone" show "$historical" | head -40 > "$tmp/regressed_generated.lean"
if ! awk '/maxHeartbeats[ \t]+0+([^0-9]|$)/ { found = 1 } END { exit !found }' \
    "$tmp/regressed_generated.lean"; then
  echo "FAIL: fixture ($fixture_origin) has no governor line; the test would prove nothing." >&2
  exit 1
fi
echo "      (generated-regression fixture: $fixture_origin)"
rev_generated="$(commit_with "$tmp/regressed_generated.lean" \
  'MatrixMultiplication/Generated/SimplifiedVolumeScalarPositiveData99.lean')"
check_case 'NEW generated module (historical producer regression) fails' 1 "$rev_generated" \
  'FAIL: 1 NEW committed Lean source' \
  'generated payload -- regenerate with the fixed producer' \
  'MatrixMultiplication/Generated/SimplifiedVolumeScalarPositiveData99.lean:'

# --- 3. a NEW hand-written module with the governor off -------------------------------------------
printf '/-! A new hand-written module. -/\n\nset_option maxHeartbeats 0\n\ntheorem t : True := trivial\n' \
  > "$tmp/regressed_handwritten.lean"
rev_handwritten="$(commit_with "$tmp/regressed_handwritten.lean" 'MatrixMultiplication/NewModule.lean')"
check_case 'NEW hand-written module fails, named with its line' 1 "$rev_handwritten" \
  'hand-written -- replace 0 with a finite bound' \
  'MatrixMultiplication/NewModule.lean:3'

# --- 4. a finite bound in the same position is accepted -------------------------------------------
printf '/-! A new hand-written module. -/\n\nset_option maxHeartbeats 400000\n\ntheorem t : True := trivial\n' \
  > "$tmp/finite.lean"
rev_finite="$(commit_with "$tmp/finite.lean" 'MatrixMultiplication/NewModule.lean')"
check_case 'NEW module with a finite bound passes' 0 "$rev_finite" \
  'Heartbeat governor scan clean'

# --- 5. paying the debt down is a NOTICE, never a failure -----------------------------------------
git -C "$clone" show "$base:MatrixMultiplication/TotalQuotientExponentLevelTwoActiveEdges.lean" \
  | sed 's/^set_option maxHeartbeats 0$/set_option maxHeartbeats 400000/' > "$tmp/repaired.lean"
rev_repaired="$(commit_with "$tmp/repaired.lean" \
  'MatrixMultiplication/TotalQuotientExponentLevelTwoActiveEdges.lean')"
check_case 'repairing a grandfathered carrier passes with a stale notice' 0 "$rev_repaired" \
  'NOTICE: 1 grandfather entries no longer carry the option' \
  'MatrixMultiplication/TotalQuotientExponentLevelTwoActiveEdges.lean' \
  'Heartbeat governor scan clean'

# --- 6. prose about the option is not a violation --------------------------------------------------
printf '/-! We deliberately never write a zero heartbeat bound; see the board ruling. -/\n\ntheorem t : True := trivial\n' \
  > "$tmp/prose.lean"
rev_prose="$(commit_with "$tmp/prose.lean" 'MatrixMultiplication/Prose.lean')"
check_case 'prose mentioning the option is not flagged' 0 "$rev_prose" \
  'Heartbeat governor scan clean'

# --- 7. the integrity guards are wired -------------------------------------------------------------
check_case 'a non-commit revision is refused, not silently skipped' 1 'refs/heads/no-such-branch' \
  'is not a commit in this repository'

if [ "$failures" -ne 0 ]; then
  echo
  echo "$failures test case(s) failed." >&2
  exit 1
fi
echo
echo 'check_heartbeat_governor.sh: all cases passed.'
