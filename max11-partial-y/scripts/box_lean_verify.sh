#!/usr/bin/env bash
# Sync this project to the dedicated Lean box and run a fail-closed build.
set -euo pipefail

box_host="${BOX_LEAN_HOST:-ubuntu@54.81.66.156}"
box_key="${BOX_LEAN_KEY:-/Users/dc/.ssh/claude-cli.pem}"
box_dir="${BOX_LEAN_DIR:-/home/ubuntu/jc2-lean/max11-partial-y}"
run_axioms=0
full_build=0
verbose="${BOX_LEAN_VERBOSE:-0}"
modules=()

usage() {
  echo "usage: $0 [--full] [--axioms] [LeanModule ...]" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --full) full_build=1 ;;
    --axioms) run_axioms=1 ;;
    --help|-h) usage ;;
    -*) usage ;;
    *)
      [[ "$1" =~ ^[A-Za-z0-9_.-]+$ ]] || {
        echo "invalid Lean module name: $1" >&2
        exit 2
      }
      modules+=("$1")
      ;;
  esac
  shift
done

if ((full_build)) && ((${#modules[@]})); then
  echo "choose either --full or explicit modules" >&2
  exit 2
fi
if ((!full_build)) && ((${#modules[@]} == 0)); then
  usage
fi
[[ -r "$box_key" ]] || {
  echo "missing SSH key: $box_key" >&2
  exit 2
}

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
ssh_args=(-i "$box_key" -o BatchMode=yes -o StrictHostKeyChecking=no)
rsync_shell="ssh -i $box_key -o BatchMode=yes -o StrictHostKeyChecking=no"

echo "SYNC $project_dir -> $box_host:$box_dir"
rsync -az \
  --exclude .git \
  --exclude .lake \
  --exclude '*.olean' \
  -e "$rsync_shell" \
  "$project_dir/" "$box_host:$box_dir/"

if ((full_build)); then
  build_command="lake build"
else
  build_command="lake build ${modules[*]}"
fi

local_log="$(mktemp -t box-lean-build.XXXXXX)"
axiom_log="$(mktemp -t box-lean-axioms.XXXXXX)"
trap 'rm -f "$local_log" "$axiom_log"' EXIT

set +e
ssh "${ssh_args[@]}" "$box_host" \
  "cd '$box_dir' && export PATH=/home/ubuntu/.elan/bin:\$PATH && $build_command" \
  >"$local_log" 2>&1
build_exit=$?
set -e
error_count="$(grep -c 'error:' "$local_log" || true)"
sorry_count="$(grep -c 'sorryAx' "$local_log" || true)"
echo "BUILD_EXIT=$build_exit ERROR_COUNT=$error_count SORRYAX_COUNT=$sorry_count"
if ((build_exit != 0 || error_count != 0 || sorry_count != 0)); then
  cat "$local_log"
  exit 1
fi
if [[ "$verbose" == 1 ]]; then
  cat "$local_log"
else
  tail -n 3 "$local_log"
fi

if ((run_axioms)); then
  set +e
  ssh "${ssh_args[@]}" "$box_host" \
    "cd '$box_dir' && export PATH=/home/ubuntu/.elan/bin:\$PATH && ./scripts/check_axioms.sh" \
    >"$axiom_log" 2>&1
  axiom_exit=$?
  set -e
  axiom_error_count="$(grep -c 'error:' "$axiom_log" || true)"
  axiom_sorry_count="$(grep -c 'sorryAx' "$axiom_log" || true)"
  echo "AXIOM_EXIT=$axiom_exit ERROR_COUNT=$axiom_error_count SORRYAX_COUNT=$axiom_sorry_count"
  if ((axiom_exit != 0 || axiom_error_count != 0 || axiom_sorry_count != 0)); then
    cat "$axiom_log"
    exit 1
  fi
  if [[ "$verbose" == 1 ]]; then
    cat "$axiom_log"
  else
    tail -n 2 "$axiom_log"
  fi
fi
