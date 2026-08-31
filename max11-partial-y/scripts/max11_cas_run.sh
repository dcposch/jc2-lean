#!/usr/bin/env bash
# Stable CLI shim; lifecycle and timeout safety live in typed Python code.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
exec python3 "$project_dir/scripts/max11_cas_run.py" "$@"
