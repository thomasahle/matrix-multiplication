#!/usr/bin/env bash
# Prove that scripts/check_decide_budget.sh actually fires.
#
# A gate that silently matches nothing is worse than no gate: it converts an unchecked invariant
# into a green check mark.  This test therefore does not merely confirm that the gate passes on the
# current tree -- it reconstructs each historical failure and asserts that the gate FAILS on it,
# with the offending file:line in its output.
#
# The cases are the real ones from 2026-08-28:
#
#   1. MEASURED.  MatrixMultiplication.Generated.SimplifiedVolumeRecurrenceZeroFour1 peaked at
#      133662 MB.  With its grandfather line removed the gate must fail and name the number.
#   2. STATIC, on the historical file.  With the measurement file emptied, so that NOBODY has
#      measured ZeroFour1, the static payload proxy alone must still flag it.  This is the case
#      that matters: it is what the gate would have done BEFORE anyone spent hours discovering
#      133 GB the hard way.
#   3. STATIC, on a genuinely new module.  A synthetic commit adds ZeroFour1's exact shape -- a
#      2 KB checker whose proof inlines a large imported payload module -- and the gate must fail
#      on it even though the new file itself is tiny.
#   4. REGRESSION.  A grandfathered entry that gets worse must fail.
#   5. SHRINKAGE.  An entry that stops violating must be a NOTICE and exit 0, so the commit that
#      pays debt down is never the commit that goes red.
#
# Everything happens in a throwaway `--local --no-checkout` clone, and the synthetic revision is
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
cp scripts/check_decide_budget.py scripts/check_decide_budget.sh \
   scripts/decide_memory_budget.tsv scripts/decide_budget_grandfathered.txt "$clone/scripts/"
check="$clone/scripts/check_decide_budget.py"

pass=0
fail=0

expect_fail() { # name, pattern, args...
  local name="$1" pattern="$2"; shift 2
  local out status
  set +e
  out="$(python3 "$check" "$@" 2>&1)"
  status=$?
  set -e
  if [ "$status" -eq 0 ]; then
    printf 'not ok - %s: expected a nonzero exit, got 0\n' "$name"
    printf '%s\n' "$out" | sed 's/^/    /'
    fail=$((fail + 1))
    return
  fi
  if ! printf '%s\n' "$out" | grep -qF "$pattern"; then
    printf 'not ok - %s: exit %d but output never mentioned %s\n' "$name" "$status" "$pattern"
    printf '%s\n' "$out" | sed 's/^/    /'
    fail=$((fail + 1))
    return
  fi
  printf 'ok - %s\n' "$name"
  printf '%s\n' "$out" | grep -F "$pattern" | sed 's/^/    /'
  pass=$((pass + 1))
}

expect_pass() { # name, pattern, args...
  local name="$1" pattern="$2"; shift 2
  local out status
  set +e
  out="$(python3 "$check" "$@" 2>&1)"
  status=$?
  set -e
  if [ "$status" -ne 0 ]; then
    printf 'not ok - %s: expected exit 0, got %d\n' "$name" "$status"
    printf '%s\n' "$out" | sed 's/^/    /'
    fail=$((fail + 1))
    return
  fi
  if ! printf '%s\n' "$out" | grep -qF "$pattern"; then
    printf 'not ok - %s: exit 0 but output never mentioned %s\n' "$name" "$pattern"
    printf '%s\n' "$out" | sed 's/^/    /'
    fail=$((fail + 1))
    return
  fi
  printf 'ok - %s\n' "$name"
  printf '%s\n' "$out" | grep -F "$pattern" | sed 's/^/    /'
  pass=$((pass + 1))
}

# 0. The built-in fixture, and the unmodified gate.
expect_pass 'self-test fixture fires' 'self-test ok' --self-test
expect_pass 'clean on the committed tree' 'Decide budget check clean.'

# 1. MEASURED: ungrandfather ZeroFour1's 133 GB measurement.
grep -v 'SimplifiedVolumeRecurrenceZeroFour1' "$clone/scripts/decide_budget_grandfathered.txt" \
  > "$tmp/no_zerofour1.txt"
expect_fail 'measured 133 GB module fails when not grandfathered' \
  'measured peak of 133662 MB' --grandfather-file "$tmp/no_zerofour1.txt"

# 2. STATIC on the historical file: nobody has measured anything.
printf '# no measurements\n' > "$tmp/empty_budget.tsv"
grep -v 'SimplifiedVolumeRecurrenceZeroFour1' "$clone/scripts/decide_budget_grandfathered.txt" \
  > "$tmp/no_zerofour1.txt"
expect_fail 'static proxy alone flags ZeroFour1 with no measurement in hand' \
  'MatrixMultiplication/Generated/SimplifiedVolumeRecurrenceZeroFour1.lean:54' \
  --budget-file "$tmp/empty_budget.tsv" --grandfather-file "$tmp/no_zerofour1.txt"

# 3. STATIC on a genuinely new module, committed: ZeroFour1's shape, 2 KB of new checker.
payload="$tmp/NewPayload.lean"
{
  printf 'namespace NewSelfTestPayload\n'
  printf 'def rawData : List Nat := [\n'
  i=0
  while [ "$i" -lt 4000 ]; do printf '  %d,\n' "$((100000 + i))"; i=$((i + 1)); done
  printf '  999999]\n'
  printf 'def data : List Nat := rawData\n'
  printf 'theorem data_eq_rawData : data = rawData := rfl\n'
  printf 'end NewSelfTestPayload\n'
} > "$payload"
checker="$tmp/NewChecker.lean"
cat > "$checker" <<'INNER'
import MatrixMultiplication.Generated.NewSelfTestPayload

/-! A new generated checker with ZeroFour1's exact shape: two kilobytes of source whose one
reduction inlines an entire imported payload module before reducing. -/

set_option maxRecDepth 1000000

opaque new_recurrence_normalizes :
    NewSelfTestPayload.data = NewSelfTestPayload.rawData := by
  rw [NewSelfTestPayload.data_eq_rawData]
  decide +kernel
INNER
test "$(wc -c < "$checker")" -lt 2048 || { echo 'fixture checker is not tiny'; exit 1; }

export GIT_INDEX_FILE="$tmp/index"
git -C "$clone" read-tree HEAD
add_blob() { # local file, repo path
  local blob
  blob="$(git -C "$clone" hash-object -w --stdin < "$1")"
  git -C "$clone" update-index --add --cacheinfo "100644,$blob,$2"
}
add_blob "$payload" 'MatrixMultiplication/Generated/NewSelfTestPayload.lean'
add_blob "$checker" 'MatrixMultiplication/Generated/NewSelfTestChecker.lean'
tree="$(git -C "$clone" write-tree)"
commit="$(git -C "$clone" commit-tree "$tree" -p HEAD -m 'synthetic: a new ZeroFour1-shaped decide')"
unset GIT_INDEX_FILE
git -C "$clone" update-ref HEAD "$commit"

expect_fail 'a NEW module with ZeroFour1 shape fails, though its own file is under 2 KB' \
  'MatrixMultiplication/Generated/NewSelfTestChecker.lean:11'
expect_fail 'the failure names the payload it would inline' \
  'digits of literal payload into one reduction'

# 4. REGRESSION: a grandfathered entry that got worse.
sed 's#^payload MatrixMultiplication/Generated/SimplifiedVolumeRecurrenceZeroFour0.lean::recurrence_normalizes .*#payload MatrixMultiplication/Generated/SimplifiedVolumeRecurrenceZeroFour0.lean::recurrence_normalizes 12000#' \
  "$clone/scripts/decide_budget_grandfathered.txt" > "$tmp/shrunk_baseline.txt"
printf 'payload MatrixMultiplication/Generated/NewSelfTestChecker.lean::new_recurrence_normalizes 24006\n' \
  >> "$tmp/shrunk_baseline.txt"
expect_fail 'a grandfathered entry that got worse fails' \
  'got WORSE' --grandfather-file "$tmp/shrunk_baseline.txt"

# 5. SHRINKAGE is a notice, not a failure.
git -C "$clone" update-ref HEAD "$(git -C "$clone" rev-parse HEAD^)"
{
  cat "$clone/scripts/decide_budget_grandfathered.txt"
  printf 'payload MatrixMultiplication/Generated/NoSuchModule.lean::gone 99999\n'
  printf 'measured MatrixMultiplication.Generated.NoSuchModuleEither 99999\n'
} > "$tmp/with_stale.txt"
expect_pass 'a retired violation is a notice, not a failure' \
  'stale grandfather entry' --grandfather-file "$tmp/with_stale.txt"

printf '\n%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
