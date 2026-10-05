#!/usr/bin/env bash
# Require the CSLib copyright header on every hand-written Lean source.
#
# DESIGN.md ("Module hygiene") says every new module carries the CSLib
# copyright header, and CSLib itself refuses a file without one.  Nothing enforced it, so the
# tree drifted: 288 tracked hand-written sources at the time this gate was written began with
# `import` instead.  This check is static — no Lean, no compiler, no network.
#
# THE HEADER
# ----------
# Exactly the four-line block used by every other file in the tree, delimited by `/-` and `-/`
# and starting at byte zero:
#
#     /-
#     Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
#     Released under Apache 2.0 license as described in the file LICENSE.
#     Authors: Thomas Dybdahl Ahle
#     -/
#
# The year and the author names are matched by shape, not literally, so a second contributor or a
# later year is accepted; the licence line is matched exactly, because it is the legally
# load-bearing one.
#
# WHAT IS SCANNED
# ---------------
# Tracked `.lean` sources (`git ls-files`, the same convention as
# scripts/check_source_coverage.sh) under `AlgebraicComplexity/`, `MatrixMultiplication/`,
# `AxiomAudit/` and `AxiomAuditCertificate/`, plus the top-level library roots.  Two directories
# are deliberately out of scope because a generator owns their bytes and a header would have to be
# emitted rather than written:
#
#   * MatrixMultiplication/Generated/ — the exported certificate tables;
#   * better_bound/                   — producer staging output.
#
# NO `grep` IS INVOLVED anywhere in this scan.  `grep` on the maintainer's machine is ugrep 7.8.4,
# where `grep -r PAT dir/*.lean` returns zero matches silently instead of erroring, and a check
# that silently matches nothing is worse than no check.  The scan is one `awk` program that is
# handed the path list on stdin and opens each file itself, reading only its first five lines.
# Two integrity guards run before every scan and fail loudly rather than passing quietly:
#
#   G1  the scope must be non-empty;
#   G2  the matcher must flag known-bad fixtures and spare a known-good one.
#
# GRANDFATHERING
# --------------
# Pre-existing offenders are listed in scripts/copyright_headers_grandfathered.txt so that the
# gate is green at HEAD and only NEW files fail.  The list is APPEND-BLOCKED and may only shrink,
# matching scripts/heavy_audit_grandfathered.txt and scripts/source_coverage_grandfathered.txt: an
# unlisted offender is a hard failure, while a listed path that has grown a header (or been
# deleted) is a stale-entry NOTICE, never a failure, so paying the debt down can never fail on the
# commit that pays it.  Adding a header is a comment-only edit; regenerate the list deliberately,
# under review, with `scripts/check_copyright_headers.sh --update`.
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."

grandfather_file='scripts/copyright_headers_grandfathered.txt'
update_grandfather_file=0
case "${1:-}" in
  '')
    ;;
  --update)
    update_grandfather_file=1
    ;;
  *)
    echo "usage: $0 [--update]" >&2
    exit 2
    ;;
esac

# The matcher.  Paths arrive on stdin, one per line; offending paths leave on stdout.  Interval
# expressions (`[0-9]{4}`) are avoided because they are not portable across the awk versions on
# macOS and on ubuntu-latest.
header_filter='
  {
    path = $0
    ok = 1
    for (i = 1; i <= 5; i++) {
      if ((getline line < path) <= 0) { ok = 0; break }
      if (i == 1) { if (line != "/-") ok = 0 }
      else if (i == 2) {
        if (line !~ /^Copyright \(c\) [0-9][0-9][0-9][0-9](-[0-9][0-9][0-9][0-9])? .+\. All rights reserved\.$/) ok = 0
      }
      else if (i == 3) {
        if (line != "Released under Apache 2.0 license as described in the file LICENSE.") ok = 0
      }
      else if (i == 4) { if (line !~ /^Authors: .+$/) ok = 0 }
      else { if (line != "-/") ok = 0 }
    }
    close(path)
    if (!ok) print path
  }
'

# --- the scope -------------------------------------------------------------------------------
# `git ls-files` is what a clean checkout builds; untracked lane scratch is not repository state.
in_scope() {
  git ls-files -- '*.lean' | awk '
    /^better_bound\// { next }
    /^MatrixMultiplication\/Generated\// { next }
    { print }
  '
}

scope_file="$(mktemp)"
fixture_dir="$(mktemp -d)"
cleanup() {
  rm -f "$scope_file"
  rm -rf "$fixture_dir"
}
trap cleanup EXIT

in_scope | sort -u > "$scope_file"

# --- G1: the scope must not be empty ----------------------------------------------------------
if [[ ! -s "$scope_file" ]]; then
  echo 'FAIL: no tracked Lean sources are in scope; this check would pass vacuously.' >&2
  echo '      Run it from inside the repository, with git available.' >&2
  exit 1
fi

# --- G2: prove the matcher still discriminates, before trusting a clean result -----------------
{
  printf '/-\nCopyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.\n'
  printf 'Released under Apache 2.0 license as described in the file LICENSE.\n'
  printf 'Authors: Thomas Dybdahl Ahle\n-/\n\nimport X\n'
} > "$fixture_dir/neg_good.lean"
printf 'import X\n' > "$fixture_dir/pos_import_first.lean"
{
  printf '/-\nCopyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.\n'
  printf 'Released under the MIT license as described in the file LICENSE.\n'
  printf 'Authors: Thomas Dybdahl Ahle\n-/\n'
} > "$fixture_dir/pos_wrong_licence.lean"
{
  printf '/-\nCopyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.\n'
  printf 'Released under Apache 2.0 license as described in the file LICENSE.\n-/\n'
} > "$fixture_dir/pos_no_authors.lean"
fixture_result="$(
  printf '%s\n' \
    "$fixture_dir/neg_good.lean" \
    "$fixture_dir/pos_import_first.lean" \
    "$fixture_dir/pos_wrong_licence.lean" \
    "$fixture_dir/pos_no_authors.lean" |
    awk "$header_filter" | sed "s|^$fixture_dir/||" | sort | tr '\n' ' '
)"
if [[ "$fixture_result" != 'pos_import_first.lean pos_no_authors.lean pos_wrong_licence.lean ' ]]; then
  echo 'FAIL: copyright-header matcher self-test did not discriminate as expected.' >&2
  echo '      Expected exactly the three pos_*.lean fixtures to be flagged; got:' >&2
  printf '        %s\n' "$fixture_result" >&2
  echo '      The scan is not trustworthy until the matcher is repaired.' >&2
  exit 1
fi

# --- the scan --------------------------------------------------------------------------------
offenders_file="$(mktemp)"
listed_file="$(mktemp)"
cleanup() {
  rm -f "$scope_file" "$offenders_file" "$listed_file"
  rm -rf "$fixture_dir"
}

awk "$header_filter" < "$scope_file" | sort -u > "$offenders_file"

if ((update_grandfather_file == 1)); then
  {
    echo '# Tracked hand-written Lean sources without the CSLib copyright header.'
    echo '#'
    echo '# Standing debt recorded so that `scripts/check_copyright_headers.sh` is green at HEAD and'
    echo '# only NEW headerless files fail.  The list is APPEND-BLOCKED and may only shrink: adding'
    echo '# the four-line header to a file is a comment-only edit, so delete its line here in the'
    echo '# same commit.  A listed path that already has a header is reported as a stale notice.'
    echo '#'
    echo '# Regenerate deliberately, under review, with:'
    echo '#'
    echo '#   scripts/check_copyright_headers.sh --update'
    echo
    cat "$offenders_file"
  } > "$grandfather_file"
  echo "Wrote $grandfather_file with $(grep -c . "$offenders_file" || true) entr(ies); review the diff."
  exit 0
fi

# `sed` rather than `grep -v`: `grep -v` exits 1 on empty input, which under the `set -o pipefail`
# above would abort this gate exactly when the debt has been paid off in full.
if [[ -f "$grandfather_file" ]]; then
  sed -e 's/#.*//' -e 's/[[:space:]]//g' -e '/^$/d' "$grandfather_file" | sort -u > "$listed_file"
else
  : > "$listed_file"
fi

unlisted="$(comm -23 "$offenders_file" "$listed_file")"
stale="$(comm -13 "$offenders_file" "$listed_file")"

status=0
if [[ -n "$unlisted" ]]; then
  echo 'FAIL: hand-written Lean sources do not begin with the CSLib copyright header:' >&2
  printf '  %s\n' $unlisted >&2
  echo 'Copy the four-line header from any neighbouring module.  Do not add a line to' >&2
  echo "$grandfather_file: that list may only shrink." >&2
  status=1
fi

# A stale entry means a header was added, which is the outcome this gate exists to reach; report
# it so the list actually shrinks, but never fail on the improvement.
if [[ -n "$stale" ]]; then
  echo "NOTICE: $grandfather_file is stale — $(printf '%s\n' "$stale" | grep -c .) entr(ies) now have a header or are gone." >&2
  echo '        The list may only shrink: remove those lines.' >&2
  printf '  %s\n' $stale >&2
fi

if ((status == 0)); then
  echo "Copyright headers clean: $(grep -c . "$scope_file" || true) hand-written sources in scope, $(grep -c . "$listed_file" || true) grandfathered."
fi
exit "$status"
