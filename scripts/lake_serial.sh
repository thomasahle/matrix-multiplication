#!/usr/bin/env bash
# Run one low-priority Lake command at a time in this shared worktree.
#
# Commands such as `lake query TARGET:deps` may build missing or stale artifacts,
# so they need the same worktree lock as an explicit `lake build`.
# For `--direct-lean`, set `AC_PRIVATE_LEAN_PATH_PREFIX` to prepend a private
# olean farm without making that farm the source-package root.
set -u

cd "$(dirname "$0")/.."

lock_dir=".lake/matrix-multiplication.build.lock"
if ! mkdir "$lock_dir" 2>/dev/null; then
  echo "Another serialized Lake command is already using this worktree." >&2
  echo "Wait for it to finish; if no Lake process exists, remove the stale lock: $lock_dir" >&2
  exit 2
fi

cleanup() {
  rmdir "$lock_dir" 2>/dev/null || true
}
trap cleanup EXIT INT TERM

# The lock coordinates updated scripts, but an older/raw `lake build` may already
# be compiling into this worktree. Detect the Lake parent by its current working
# directory as well as compiler children containing the absolute output path;
# checking both closes the short gap between successive Lean writer processes.
raw_lake_in_worktree=0
raw_lean_in_worktree=0
if command -v pgrep >/dev/null 2>&1; then
  while IFS= read -r pid; do
    [[ -n "$pid" ]] || continue
    process_cwd=""
    if [[ -e "/proc/$pid/cwd" ]]; then
      process_cwd="$(readlink "/proc/$pid/cwd" 2>/dev/null || true)"
    elif command -v lsof >/dev/null 2>&1; then
      process_cwd="$(lsof -a -p "$pid" -d cwd -Fn 2>/dev/null |
        sed -n 's/^n//p' | head -n 1)"
    fi
    if [[ "$process_cwd" == "$PWD" ]]; then
      raw_lake_in_worktree=1
      break
    fi
  done < <(pgrep -x lake 2>/dev/null || true)

  # Inspect only actual Lean compiler processes.  A broad command-line search for
  # `$PWD/.lake/build` also matches harmless shells that wait for an artifact to appear, causing
  # the serialization gate to remain closed indefinitely even though no process can write it.
  while IFS= read -r pid; do
    [[ -n "$pid" ]] || continue
    process_cwd=""
    process_command="$(ps -p "$pid" -o command= 2>/dev/null || true)"
    if [[ -e "/proc/$pid/cwd" ]]; then
      process_cwd="$(readlink "/proc/$pid/cwd" 2>/dev/null || true)"
    elif command -v lsof >/dev/null 2>&1; then
      process_cwd="$(lsof -a -p "$pid" -d cwd -Fn 2>/dev/null |
        sed -n 's/^n//p' | head -n 1)"
    fi
    if [[ "$process_cwd" == "$PWD" ]] || [[ "$process_command" == *"$PWD/.lake/build"* ]]; then
      raw_lean_in_worktree=1
      break
    fi
  done < <(pgrep -x lean 2>/dev/null || true)
fi

if [[ "$raw_lake_in_worktree" -eq 1 ]] || [[ "$raw_lean_in_worktree" -eq 1 ]]; then
  echo "A raw Lean build is already writing this worktree; not starting another Lake command." >&2
  exit 2
fi

if [[ "${1:-}" == "--direct-lean" ]]; then
  shift

  # `lake env lean ...` retains the Lake process while Lean elaborates.  On the
  # current toolchain that parent alone can occupy hundreds of megabytes, which
  # defeats the purpose of a low-memory single-file check.  Resolve the two
  # search paths first, let Lake exit, and then run the same compiler directly
  # while this shell continues to hold the worktree lock.
  resolved_lean_env="$(lake env printenv LEAN_PATH LEAN_SRC_PATH)"
  task_lean_path="${resolved_lean_env%%$'\n'*}"
  if [[ "$resolved_lean_env" == *$'\n'* ]]; then
    task_lean_src_path="${resolved_lean_env#*$'\n'}"
  else
    task_lean_src_path=""
  fi
  if [[ -n "${AC_PRIVATE_LEAN_PATH_PREFIX:-}" ]]; then
    task_lean_path="${AC_PRIVATE_LEAN_PATH_PREFIX}${task_lean_path:+:$task_lean_path}"
  fi

  LEAN_PATH="$task_lean_path" LEAN_SRC_PATH="$task_lean_src_path" \
    nice -n 19 lean "$@"
else
  LEAN_NUM_THREADS=1 nice -n 19 lake "$@"
fi
