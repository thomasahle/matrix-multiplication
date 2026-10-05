#!/usr/bin/env bash
# Regression tests for scripts/check_assert_axioms_targets.sh.
#
# The point of these is that the gate must actually FIRE.  Today's dark-axiom failure hid for
# weeks because nothing ever evaluated the assertions; a static check that silently matches
# nothing would hide it just as well.  So the tests assert both directions:
#
#   1. the built-in classifier fixture produces exactly the expected verdicts;
#   2. the committed tree at HEAD is clean (exit 0) against the grandfather list;
#   3. the pre-repair revision 95347e18^ -- the real historical case, six
#      `Region{i}.coverageChecked` assertions naming a declaration that existed nowhere --
#      exits nonzero and names those six lines.
set -euo pipefail
cd "$(dirname "$0")/../.."

fail() { echo "TEST FAIL: $*" >&2; exit 1; }

echo '1) classifier self-test'
python3 scripts/check_assert_axioms_targets.py --self-test >/dev/null ||
  fail 'the built-in classifier fixture did not produce the expected verdicts'

echo '2) HEAD is clean against the grandfather list'
bash scripts/check_assert_axioms_targets.sh >/dev/null ||
  fail 'the gate is red on HEAD; it must only fail on NEW dark assertions'

echo '3) the historical case (95347e18^) is caught'
if ! git cat-file -e 95347e18^ 2>/dev/null; then
  echo '   SKIP: 95347e18 is not in this clone (shallow checkout).'
else
  output="$(python3 scripts/check_assert_axioms_targets.py --rev 95347e18^ 2>&1)" && status=0 || status=$?
  [ "$status" -eq 1 ] ||
    fail "expected exit 1 on 95347e18^, got $status"
  count="$(printf '%s\n' "$output" | awk '/^FAIL:.*coverageChecked/ { n++ } END { print n + 0 }')"
  [ "$count" -eq 6 ] ||
    fail "expected 6 coverageChecked failures on 95347e18^, got $count"
  printf '%s\n' "$output" |
    awk '/^FAIL:/ && /TotalQuotientExponentLevelFourValidity\.lean:26:/ { found = 1 }
         END { exit !found }' ||
    fail 'the report did not name AxiomAuditCertificate/TotalQuotientExponentLevelFourValidity.lean:26'
fi

echo 'All scripts/check_assert_axioms_targets.sh tests passed.'
