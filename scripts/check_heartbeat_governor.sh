#!/usr/bin/env bash
# Ban `set_option maxHeartbeats 0` from committed Lean sources.
#
# WHY THIS GATE EXISTS
# --------------------
# `maxHeartbeats 0` disables Lean's deterministic elaboration governor: the elaborator will
# grind forever rather than report a `(deterministic) timeout`. A runaway build ran 1h54m and
# reached 133 GB before it was killed, and the reason it could run away at all is that the
# generated payloads it was elaborating had switched the governor off. The board banned the
# option in generated payloads; the producers were fixed in 252dc5e3 (they now emit finite
# bounds). Nothing enforced the ban, so this script does.
#
# WHAT IS SCANNED: THE REPOSITORY, NOT THE WORKING TREE
# -----------------------------------------------------
# The scan reads a git revision (`HEAD` by default), never the checkout. Five lanes hold
# uncommitted edits in this repo and worktree state is NOT repository state. The mechanism is
# `git grep <rev>`, which is exactly "read `git show <rev>:<path>` for every tracked file" without
# materializing a temp tree the way `git archive` would; it is a single deterministic matcher that
# behaves identically on macOS and on ubuntu-latest.
#
# That choice is not academic. Measured on this tree the two views disagree badly:
#   * `MatrixMultiplication/Generated/` carries 327 of these at HEAD, but 452 in the checkout --
#     125 are UNTRACKED regenerated files that no clean checkout and no CI run will ever see;
#   * a plain `find . -name '*.lean'` over this checkout visits ~27000 files, because
#     `scratchpad/` alone holds ~95000 untracked `.lean` files. A worktree-based check would be
#     drowned by scratch output and would report numbers that mean nothing to CI.
# Use `--worktree-preview` for an advisory local view of uncommitted work; it never runs in CI.
#
# THE SILENT-GLOB HAZARD, AND HOW THIS SCRIPT AVOIDS IT
# -----------------------------------------------------
# `grep` on the maintainer's machine is ugrep 7.8.4, where `-r` combined with an explicit file
# glob silently returns zero matches instead of erroring:
#     grep -rl PAT dir/*.lean             -> 0     (WRONG, silent)
#     grep -rl PAT --include='*.lean' dir -> 452   (right)
# A check that silently matches nothing is worse than no check. This script therefore calls no
# system `grep` on the source universe at all, and -- because the same class of bug bites git too
# (`git ls-tree -r HEAD -- '*.lean'` silently yields 0 here, since ls-tree pathspecs are
# prefix-based, not wildmatch) -- it does not restrict the scan with a pathspec either. It greps
# the whole revision and filters to `.lean` in awk, where the filter is explicit and testable.
# Two integrity guards run before every scan and fail loudly rather than silently passing:
#   G1  the revision must contain at least one `.lean` file;
#   G2  the ban pattern must flag known-positive fixtures and spare known-negative ones.
#
# WHAT IT DETECTS / WHAT IT DOES NOT
# ----------------------------------
# Detects: any tracked `.lean` file at the revision whose text contains `maxHeartbeats` followed
# by an all-zero numeral (`0`, `00`, ...). Finite bounds (`maxHeartbeats 400000`) and bare prose
# mentions of the option name are not matched.
# Does NOT detect: producers that would EMIT the option. All fifteen `better_bound/export_*.py`
# producers mention `maxHeartbeats 0` today, in comments that document the ban -- scanning them
# would be fifteen guaranteed false positives and could not distinguish a template from prose. The
# emitted `.lean` payload is the ground truth and is what this gate reads.
# Does NOT detect: an uncommitted violation (by design, see above), a comment-only occurrence
# (none exist; all 490 current matches are the exact line `set_option maxHeartbeats 0`), or
# elaboration cost that is high but bounded.
#
# GRANDFATHERING
# --------------
# The repository already violates this rule. `scripts/heartbeat_governor_grandfathered.txt` lists
# every current carrier so that only NEW ones fail, and the standing debt is printed on every run
# rather than forgotten. The list is APPEND-BLOCKED and may only shrink, matching
# `scripts/heavy_audit_grandfathered.txt`: an unlisted carrier is a hard failure, while a listed
# entry that has stopped violating (fixed or deleted) is a stale-entry NOTICE, never a failure,
# so paying the debt down can never fail on the commit that pays it.
# Regenerate deliberately, under review, with `scripts/check_heartbeat_governor.sh --update`.
#
# Carriers are reported in three classes because their remedies differ:
#   generated payload  MatrixMultiplication/Generated/  -> regenerate; never hand-edit
#   producer staging   better_bound/                    -> regenerate from the fixed producers
#   hand-written       everything else                  -> a human decision under the board ruling
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."

grandfather_file='scripts/heartbeat_governor_grandfathered.txt'
# `maxHeartbeats` + whitespace + an all-zero numeral, not followed by another digit.
# `0+` catches `00`/`000000`, which Lean also reads as zero; the trailing guard keeps
# `maxHeartbeats 400000` and a hypothetical `maxHeartbeats 0400` out.
pattern='maxHeartbeats[[:space:]]+0+([^0-9]|$)'
rev='HEAD'
update=0
worktree_preview=0

usage() {
  cat >&2 <<'USAGE'
usage: check_heartbeat_governor.sh [--rev <rev>] [--update] [--worktree-preview]

  --rev <rev>          revision to scan (default: HEAD)
  --update             regenerate the grandfather list from <rev>; review the diff
  --worktree-preview   additionally report uncommitted tracked carriers (advisory, local only)
USAGE
  exit 2
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --update) update=1; shift ;;
    --worktree-preview) worktree_preview=1; shift ;;
    --rev) [ "$#" -ge 2 ] || usage; rev="$2"; shift 2 ;;
    --rev=*) rev="${1#--rev=}"; shift ;;
    -h|--help) usage ;;
    *) echo "unknown argument: $1" >&2; usage ;;
  esac
done

if ! git rev-parse --verify --quiet "$rev^{commit}" >/dev/null; then
  echo "FAIL: '$rev' is not a commit in this repository; nothing to scan." >&2
  exit 1
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# --- G2: prove the ban pattern still discriminates, before trusting a clean result -------------
# A regex that has silently stopped matching is the exact failure mode this whole script guards
# against, so it is tested against fixtures on every run rather than assumed.
mkdir -p "$work/selftest"
printf 'set_option maxHeartbeats 0\n'          > "$work/selftest/pos_plain.lean"
printf 'set_option maxHeartbeats 0 in\n'       > "$work/selftest/pos_inline.lean"
printf '  set_option   maxHeartbeats   00  \n' > "$work/selftest/pos_spaced.lean"
printf 'set_option maxHeartbeats 400000\n'     > "$work/selftest/neg_finite.lean"
printf 'set_option maxHeartbeats 1000000 in\n' > "$work/selftest/neg_million.lean"
printf 'pushes a `simp` step past `maxHeartbeats`. -/\n' > "$work/selftest/neg_prose.lean"
selftest_status=0
git -C "$work/selftest" grep --no-index -l -E "$pattern" \
    -- pos_plain.lean pos_inline.lean pos_spaced.lean \
       neg_finite.lean neg_million.lean neg_prose.lean \
    > "$work/selftest.out" 2>/dev/null || selftest_status=$?
if [ "$selftest_status" -gt 1 ]; then
  echo 'FAIL: heartbeat-governor pattern self-test could not run (git grep error).' >&2
  exit 1
fi
if [ "$(sort "$work/selftest.out" | tr '\n' ' ')" != 'pos_inline.lean pos_plain.lean pos_spaced.lean ' ]; then
  echo 'FAIL: heartbeat-governor pattern self-test did not discriminate as expected.' >&2
  echo '      Expected exactly the three pos_*.lean fixtures to match; got:' >&2
  sed 's/^/        /' "$work/selftest.out" >&2
  echo '      The scan is not trustworthy until the pattern is repaired.' >&2
  exit 1
fi

# --- G1: the scanned universe must be non-empty -------------------------------------------------
# `git ls-tree` pathspecs are prefix-based, so `-- '*.lean'` would silently yield zero here.
# Filter in awk instead, where the filter is visible.
git ls-tree -r --name-only "$rev" > "$work/tracked.txt"
awk '/\.lean$/' "$work/tracked.txt" > "$work/universe.txt"
universe_count="$(wc -l < "$work/universe.txt" | tr -d ' ')"
if [ "$universe_count" -eq 0 ]; then
  echo "FAIL: no .lean files found at '$rev'." >&2
  echo '      A scan over an empty universe would pass vacuously; refusing to report clean.' >&2
  exit 1
fi

# `git grep -n` prints `<rev>:<path>:<line>:<text>`; the path field is split on the first colon,
# which is only sound while no tracked path contains one.
if awk -F/ '{ if (index($0, ":")) { bad = 1 } } END { exit !bad }' "$work/tracked.txt"; then
  echo "FAIL: a tracked path at '$rev' contains a colon, which this script's output parser" >&2
  echo '      cannot split unambiguously. Repair the parser before trusting the scan.' >&2
  exit 1
fi

# --- the scan ------------------------------------------------------------------------------------
# No pathspec: the whole revision is grepped and `.lean` is selected in awk. See the header.
scan_rev() {
  local scan_rev_name="$1" scan_out="$2" scan_status=0
  git grep -n -I -E "$pattern" "$scan_rev_name" > "$work/raw.txt" || scan_status=$?
  if [ "$scan_status" -gt 1 ]; then
    echo "FAIL: 'git grep' failed while scanning '$scan_rev_name' (exit $scan_status)." >&2
    exit 1
  fi
  awk -v pre="$scan_rev_name:" '
    index($0, pre) == 1 { $0 = substr($0, length(pre) + 1) }
    {
      colon = index($0, ":")
      if (colon == 0) next
      path = substr($0, 1, colon - 1)
      if (path !~ /\.lean$/) next
      rest = substr($0, colon + 1)
      colon = index(rest, ":")
      if (colon == 0) next
      print path "\t" substr(rest, 1, colon - 1)
    }
  ' "$work/raw.txt" | sort -u > "$scan_out"
}

scan_rev "$rev" "$work/hits.txt"
cut -f1 "$work/hits.txt" | sort -u > "$work/carriers.txt"

first_line_of() {
  awk -F'\t' -v want="$1" '$1 == want { print $2; exit }' "$work/hits.txt"
}

# One classifier, shared by every report and by --update, so the grandfather list and the
# console output can never disagree about which remedy a carrier needs.
classify_awk='
  function carrier_class(p) {
    if (index(p, "MatrixMultiplication/Generated/") == 1) return "generated"
    if (index(p, "better_bound/") == 1) return "staging"
    return "handwritten"
  }
'

select_class() {  # select_class <file> <class>
  awk -v want="$2" "$classify_awk"' carrier_class($0) == want { print }' "$1"
}

count_class() {  # count_class <file> <class>
  awk -v want="$2" "$classify_awk"' carrier_class($0) == want { n++ } END { print n + 0 }' "$1"
}

write_grandfather_file() {
  {
    cat <<'HEADER'
# Committed Lean sources that still disable the elaboration governor.
#
# Every path here contains `set_option maxHeartbeats 0`, which turns off Lean's deterministic
# elaboration limit. A build over these payloads cannot time out; it can only run until something
# else kills it. One did: 1h54m and 133 GB. The option is banned in generated payloads by board
# ruling, and the producers stopped emitting it in 252dc5e3 -- these files predate that fix.
#
# The list is APPEND-BLOCKED and may only shrink. `scripts/check_heartbeat_governor.sh` fails on
# any carrier that is NOT listed here; an entry that has stopped violating (regenerated, fixed, or
# deleted) is reported as a stale-entry notice rather than a failure, so that paying the debt down
# can never fail on the commit that pays it.
#
# Do not add a line here to silence the gate on new work. Remedies by class:
#
#   generated payload (MatrixMultiplication/Generated/)
#       Regenerate with the fixed producer and drop the line. Never hand-edit these files.
#   producer staging (better_bound/)
#       Producer output staged in the producer tree; regenerate from the fixed producers.
#   hand-written
#       A human decision under the board ruling: replace `0` with a finite bound large enough for
#       the declaration, or split the declaration until a finite bound suffices.
#
# Regenerate this file deliberately, and review the diff, with:
#
#   scripts/check_heartbeat_governor.sh --update
#
# Paths are relative to the repository root, one per line, sorted within each class.
HEADER
    for class_name in generated staging handwritten; do
      case "$class_name" in
        generated)   heading='generated payload -- MatrixMultiplication/Generated/ (regenerate)' ;;
        staging)     heading='producer staging -- better_bound/ (regenerate from fixed producers)' ;;
        handwritten) heading='hand-written -- requires a human decision' ;;
      esac
      class_listing="$(select_class "$work/carriers.txt" "$class_name")"
      if [ -n "$class_listing" ]; then
        printf '\n# %s\n' "$heading"
        printf '%s\n' "$class_listing"
      fi
    done
  } > "$grandfather_file"
}

if [ "$update" -eq 1 ]; then
  write_grandfather_file
  echo "Regenerated $grandfather_file from '$rev':"
  echo "  carriers listed: $(wc -l < "$work/carriers.txt" | tr -d ' ')"
  echo '  Review the diff before committing; this list may only shrink.'
  exit 0
fi

if [ ! -f "$grandfather_file" ]; then
  echo "FAIL: missing grandfather list '$grandfather_file'." >&2
  echo '      Generate it with: scripts/check_heartbeat_governor.sh --update' >&2
  exit 1
fi
awk '!/^[[:space:]]*#/ && NF { print $0 }' "$grandfather_file" | sort -u > "$work/allowed.txt"

comm -23 "$work/carriers.txt" "$work/allowed.txt" > "$work/new.txt"
comm -13 "$work/carriers.txt" "$work/allowed.txt" > "$work/stale.txt"
comm -12 "$work/carriers.txt" "$work/allowed.txt" > "$work/grandfathered.txt"

report_class() {
  local listing_file="$1" class_name="$2" label="$3"
  local paths
  paths="$(select_class "$listing_file" "$class_name")"
  [ -n "$paths" ] || return 0
  printf '  %s\n' "$label" >&2
  while IFS= read -r carrier_path; do
    printf '    %s:%s\n' "$carrier_path" "$(first_line_of "$carrier_path")" >&2
  done <<EOF
$paths
EOF
}

echo "Heartbeat governor scan of '$rev' ($universe_count tracked .lean files)."

grandfathered_total="$(wc -l < "$work/grandfathered.txt" | tr -d ' ')"
echo "Grandfathered carriers of \`set_option maxHeartbeats 0\` (pre-existing debt): $grandfathered_total"
echo "  generated payload  MatrixMultiplication/Generated/  $(count_class "$work/grandfathered.txt" generated)  (remedy: regenerate)"
echo "  producer staging   better_bound/                    $(count_class "$work/grandfathered.txt" staging)  (remedy: regenerate from fixed producers)"
echo "  hand-written       elsewhere                        $(count_class "$work/grandfathered.txt" handwritten)  (remedy: a human decision)"
# The hand-written carriers are few and cannot be regenerated away, so they are named on every
# run: they are the part of this debt that only a person can retire.
select_class "$work/grandfathered.txt" handwritten > "$work/grandfathered_handwritten.txt"
if [ -s "$work/grandfathered_handwritten.txt" ]; then
  while IFS= read -r carrier_path; do
    printf '    %s:%s\n' "$carrier_path" "$(first_line_of "$carrier_path")"
  done < "$work/grandfathered_handwritten.txt"
fi

if [ -s "$work/stale.txt" ]; then
  echo "NOTICE: $(wc -l < "$work/stale.txt" | tr -d ' ') grandfather entries no longer carry the option (fixed or deleted)."
  sed 's/^/    /' "$work/stale.txt"
  echo '    Debt paid: drop these lines from the list (scripts/check_heartbeat_governor.sh --update).'
fi

if [ "$worktree_preview" -eq 1 ]; then
  # Advisory only, and deliberately restricted to TRACKED files: an unrestricted worktree walk
  # here would drag in ~95000 untracked scratchpad sources. Never gates CI.
  preview_status=0
  git grep -n -I -E "$pattern" -- '*.lean' > "$work/wt_raw.txt" || preview_status=$?
  if [ "$preview_status" -le 1 ]; then
    awk -F: '$1 ~ /\.lean$/ { print $1 }' "$work/wt_raw.txt" | sort -u > "$work/wt_carriers.txt"
    comm -23 "$work/wt_carriers.txt" "$work/allowed.txt" > "$work/wt_new.txt"
    if [ -s "$work/wt_new.txt" ]; then
      echo "PREVIEW: $(wc -l < "$work/wt_new.txt" | tr -d ' ') tracked worktree carriers are not in the list (uncommitted; not gated)."
      sed 's/^/    /' "$work/wt_new.txt"
    else
      echo 'PREVIEW: the tracked worktree introduces no new carriers.'
    fi
  fi
fi

if [ -s "$work/new.txt" ]; then
  echo >&2
  echo "FAIL: $(wc -l < "$work/new.txt" | tr -d ' ') NEW committed Lean source(s) disable the elaboration governor" >&2
  echo '      with `set_option maxHeartbeats 0`. This is banned: it removes the only bound on' >&2
  echo '      elaboration time, and a build over such a payload cannot time out -- it can only be' >&2
  echo '      killed (1h54m / 133 GB, the incident this gate exists to prevent).' >&2
  report_class "$work/new.txt" generated \
    'generated payload -- regenerate with the fixed producer (252dc5e3); do not hand-edit:'
  report_class "$work/new.txt" staging \
    'producer staging -- regenerate from the fixed producers; a hit here means a producer regressed:'
  report_class "$work/new.txt" handwritten \
    'hand-written -- replace 0 with a finite bound, or split the declaration until one suffices:'
  echo >&2
  echo "      Do not silence this by editing $grandfather_file; that list may only shrink." >&2
  exit 1
fi

echo 'Heartbeat governor scan clean: no new carriers.'
