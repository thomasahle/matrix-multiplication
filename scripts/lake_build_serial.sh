#!/usr/bin/env bash
# Convenience wrapper for the common serialized-build command.
set -u

cd "$(dirname "$0")/.."
exec scripts/lake_serial.sh build "$@"
