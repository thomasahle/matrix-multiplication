#!/usr/bin/env bash
# No single reduction command may become the project's memory boundary -- DESIGN.md:590, in
# "Reduction and elaboration budgets" (DESIGN.md:580) -- and `decide` is reserved for "genuinely
# tiny closed finite facts" (DESIGN.md:545).
#
# Both rules were written by this project and never enforced.  On 2026-08-28 one `decide +kernel`
# in MatrixMultiplication/Generated/SimplifiedVolumeRecurrenceZeroFour1.lean needed 133 GB, and the
# whole SimplifiedVolumeRecurrenceEdge* family needed 7.3-19.6 GB per module, on a 16 GB machine --
# each discovered by running out of memory, hours in, rather than by any gate.
#
# "Genuinely tiny" is not mechanically decidable, so this gate is a two-part honest proxy:
#
#   * MEASURED.  scripts/decide_memory_budget.tsv records real per-module peak RSS.  A module over
#     the budget (default 6000 MB = half a 16 GB runner, since CI elaborates two modules at once)
#     fails.  Where a measurement exists it is authoritative and no proxy is consulted.
#   * STATIC.  For an un-measured module, the proxy is the literal numeric payload a single
#     `decide` / `decide +kernel` / `decide_cbv` drags into its goal -- counted THROUGH IMPORTS,
#     because ZeroFour1 is a 2 KB file whose 133 GB comes entirely from the sixteen payload
#     modules its proof inlines with `rw [... .data_eq_rawData]` before reducing.  A proxy that
#     measured file size would have missed the worst case in the repository.
#   * CENSUS.  `opaque name : ... := by decide` is invisible to any tool that scans for `theorem`;
#     the count is printed on every run, and one outside MatrixMultiplication/Generated fails.
#
# WHAT IS READ: the committed tree at HEAD, via `git archive HEAD` inside the Python checker, never
# the working tree.  Five lanes hold uncommitted edits in this checkout; scoring a lane's in-flight
# buffer as repository state produced three wrong conclusions on 2026-08-28.  Authors can pass
# --worktree to score their own edits before committing; CI must not.
#
# NO `grep` IS INVOLVED anywhere in this check.  `grep` on the maintainer's machine is ugrep 7.8.4,
# where `grep -rl PAT dir/*.lean` returns zero matches SILENTLY instead of erroring; all scanning
# happens inside the Python checker so macOS and the ubuntu-latest runner agree exactly.  The
# checker runs a built-in fixture (`--self-test`) first and refuses to report a clean scan when it
# found no reductions at all, so "silently matched nothing" cannot pass as green.
#
# Pre-existing violations are grandfathered in scripts/decide_budget_grandfathered.txt; the count is
# printed on every run so the debt stays visible.  Only a NEW violation -- or a grandfathered one
# that got measurably WORSE -- fails.
set -euo pipefail
cd "$(dirname "$0")/.."

case "${1:-}" in
  '')
    ;;
  --update|--report|--worktree)
    ;;
  *)
    echo "usage: $0 [--update | --report | --worktree]" >&2
    exit 2
    ;;
esac

if ! command -v python3 >/dev/null 2>&1; then
  echo 'FAIL: python3 is required by scripts/check_decide_budget.sh.' >&2
  exit 2
fi

python3 scripts/check_decide_budget.py --self-test
exec python3 scripts/check_decide_budget.py ${1:+"$1"}
