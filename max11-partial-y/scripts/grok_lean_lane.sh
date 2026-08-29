#!/usr/bin/env bash
# Launch one guarded Grok proof lane with the Max-11 verification contract.
set -euo pipefail

usage() {
  echo "usage: $0 TARGET_SCRATCH.lean INSTRUCTION..." >&2
  exit 2
}

(($# >= 2)) || usage

target="$1"
shift
instruction="$*"
project_dir="$(cd "$(dirname "$0")/.." && pwd)"
guard_dir="$project_dir/scripts/no-local-lean"

[[ "$target" =~ ^Grok[A-Za-z0-9_.-]*Scratch\.lean$ ]] || {
  echo "invalid Grok scratch target: $target" >&2
  exit 2
}
[[ "$target" == "${target##*/}" ]] || usage

if git -C "$project_dir" ls-files --error-unmatch -- "$target" >/dev/null 2>&1; then
  echo "refusing tracked target: $target" >&2
  exit 65
fi

worker_rows="$(ps -axo command= | awk -v project="$project_dir" '
  index($0, "grok --yolo") && index($0, project) {print}')"
worker_count=0
if [[ -n "$worker_rows" ]]; then
  worker_count="$(wc -l <<<"$worker_rows" | tr -d ' ')"
  if grep -Fq "$target" <<<"$worker_rows"; then
    echo "a managed worker already mentions target: $target" >&2
    exit 75
  fi
fi
if ((worker_count >= 4)); then
  echo "managed Grok worker cap reached: $worker_count/4" >&2
  exit 75
fi

command -v grok >/dev/null || {
  echo "grok is not available" >&2
  exit 69
}
[[ -x "$guard_dir/lake" && -x "$guard_dir/lean" ]] || {
  echo "missing local Lean guards in $guard_dir" >&2
  exit 69
}

contract="No tracked edits, sorry, new axioms, finite-root shortcuts, or closure overclaims. Do not invoke local Lean or Lake; the guarded PATH intentionally disables them. Use ./scripts/box_lean_verify.sh --file $target for every Lean compilation/check. Finish only after literal BUILD_EXIT=0 ERROR_COUNT=0 SORRYAX_COUNT=0, and report recursive SHA-256 hashes, exact gain, next unused row, and residual. LOCAL_LEAN_GUARD=enabled. Requested output: $target"

cd "$project_dir"
exec env PATH="$guard_dir:$PATH" \
  grok --yolo --output-format plain -p "$instruction $contract"
