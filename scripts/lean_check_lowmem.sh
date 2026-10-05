#!/usr/bin/env bash
# Check one Lean file without allowing a large concurrent elaboration.
#
# The defaults are intentionally conservative for a shared worktree.  Override
# LEAN_MEM_MB only for a file that has been profiled and reviewed.
set -euo pipefail

if [[ "$#" -eq 0 ]]; then
  echo "usage: $0 path/to/File.lean [lean options ...]" >&2
  exit 2
fi

lean_mem_mb="${LEAN_MEM_MB:-768}"
lean_threads="${LEAN_THREADS:-1}"
script_dir="$(cd "$(dirname "$0")" && pwd)"

exec "$script_dir/lake_serial.sh" --direct-lean -j "$lean_threads" -M "$lean_mem_mb" "$@"
