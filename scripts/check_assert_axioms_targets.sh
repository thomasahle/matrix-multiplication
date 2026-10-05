#!/usr/bin/env bash
# Every `#assert_axioms` target must name a declaration that exists.
#
# `#assert_axioms id` (AxiomAudit/Command.lean) calls `realizeGlobalConstWithInfos` before it
# collects a single axiom, so an unknown constant does not fail the assertion -- it aborts the
# command, and with it every other assertion in the same module.  Commit 95347e18 repaired nine
# such dark assertions in AxiomAuditCertificate/TotalQuotientExponentLevelFourValidity.lean,
# where six `Region{i}.coverageChecked` names had been regenerated out of existence.  This gate
# catches that class statically, with no compiler.
#
# WHAT IS READ: the committed tree at HEAD, via `git archive HEAD` inside the Python checker,
# never the working tree.  Five lanes hold uncommitted edits here; a declaration that exists only
# in one lane's unstaged buffer is not something CI's checkout can resolve, so treating the
# working tree as the repository would hide exactly the failures this gate is for.
#
# NO `grep` IS INVOLVED anywhere in this check.  `grep` on the maintainer's machine is ugrep
# 7.8.4, where `grep -r PAT dir/*.lean` returns zero matches silently instead of erroring; all
# scanning happens inside the Python checker so that macOS and the ubuntu-latest runner agree.
# The checker also refuses to report a clean scan when it found no assertions at all, and runs a
# built-in fixture (`--self-test`) first, so "silently matched nothing" cannot pass as green.
#
# Pre-existing violations are grandfathered in scripts/assert_axioms_dark_grandfathered.txt; the
# count is printed on every run so the debt stays visible.  Only a NEW dark assertion fails.
set -euo pipefail
cd "$(dirname "$0")/.."

case "${1:-}" in
  '')
    ;;
  --update|--list-unresolved)
    ;;
  *)
    echo "usage: $0 [--update | --list-unresolved]" >&2
    exit 2
    ;;
esac

if ! command -v python3 >/dev/null 2>&1; then
  echo 'FAIL: python3 is required by scripts/check_assert_axioms_targets.sh.' >&2
  exit 2
fi

python3 scripts/check_assert_axioms_targets.py --self-test
exec python3 scripts/check_assert_axioms_targets.py ${1:+"$1"}
