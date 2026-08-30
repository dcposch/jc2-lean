#!/usr/bin/env bash
# Reject recursive local import closures that declare the same global name.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
exec python3 "$project_dir/scripts/max11_import_collision_lint.py" "$@"
