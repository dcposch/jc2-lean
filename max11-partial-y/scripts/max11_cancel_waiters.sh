#!/usr/bin/env bash
# Cancel an explicitly superseded queued proof target and optional descendants.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
wait_root="$project_dir/.max11-lanes/waits"
target=""
reason=""
cascade=0
dry_run=0

usage() {
  echo "usage: $0 --target FILE.lean [--cascade] [--dry-run] --reason TEXT" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --target)
      shift
      (($#)) || usage
      target="$1"
      ;;
    --reason)
      shift
      (($#)) || usage
      reason="$1"
      ;;
    --cascade) cascade=1 ;;
    --dry-run) dry_run=1 ;;
    *) usage ;;
  esac
  shift
done

[[ "$target" =~ ^[A-Za-z0-9_.-]+Scratch[.]lean$ &&
    "$target" == "${target##*/}" && -n "$reason" ]] || usage

active_waiter_state() {
  case "$1" in
    queued|waiting_for_gate|waiting_for_capacity) return 0 ;;
    *) return 1 ;;
  esac
}

selected_targets=("$target")
selected_dirs=()
if [[ -d "$wait_root" ]]; then
  changed=1
  while ((changed)); do
    changed=0
    for wait_dir in "$wait_root"/*; do
      [[ -d "$wait_dir" ]] || continue
      state="$(sed -n '1p' "$wait_dir/state" 2>/dev/null || true)"
      active_waiter_state "$state" || continue
      waiter_target="$(sed -n '1p' "$wait_dir/target" 2>/dev/null || true)"
      predecessor="$(sed -n '1p' "$wait_dir/predecessor" 2>/dev/null || true)"
      include=0
      for selected_target in "${selected_targets[@]}"; do
        if [[ "$waiter_target" == "$selected_target" ]]; then
          include=1
          break
        elif ((cascade)) && [[ "$predecessor" == "$selected_target" ]]; then
          include=1
          break
        fi
      done
      ((include)) || continue

      already_selected=0
      for selected_dir in ${selected_dirs[@]+"${selected_dirs[@]}"}; do
        [[ "$selected_dir" == "$wait_dir" ]] && already_selected=1
      done
      ((already_selected)) && continue
      selected_dirs+=("$wait_dir")

      known_target=0
      for selected_target in "${selected_targets[@]}"; do
        [[ "$selected_target" == "$waiter_target" ]] && known_target=1
      done
      if ((cascade && !known_target)); then
        selected_targets+=("$waiter_target")
        changed=1
      fi
    done
  done
fi

if ((${#selected_dirs[@]} == 0)); then
  echo "CANCEL_SUMMARY matched=0 canceled=0 dry_run=$dry_run target=$target cascade=$cascade"
  exit 0
fi

canceled=0
for wait_dir in "${selected_dirs[@]}"; do
  waiter_target="$(sed -n '1p' "$wait_dir/target")"
  predecessor="$(sed -n '1p' "$wait_dir/predecessor")"
  waiter_pid="$(sed -n '1p' "$wait_dir/pid" 2>/dev/null || true)"
  process_group=""
  if [[ "$waiter_pid" =~ ^[0-9]+$ ]] && kill -0 "$waiter_pid" 2>/dev/null; then
    process_group="$(ps -o pgid= -p "$waiter_pid" | tr -d '[:space:]')"
    [[ "$process_group" =~ ^[0-9]+$ ]] || {
      echo "SKIP target=$waiter_target reason=missing_process_group" >&2
      continue
    }
    group_command="$(ps -o command= -p "$process_group" 2>/dev/null || true)"
    if [[ "$group_command" != *"max11_lean_after.sh"* ||
          "$group_command" != *"--run $wait_dir"* ]]; then
      echo "SKIP target=$waiter_target reason=unvalidated_process_group pgid=$process_group" >&2
      continue
    fi
  fi

  if ((dry_run)); then
    echo "WOULD_CANCEL target=$waiter_target after=$predecessor pid=${waiter_pid:-none} pgid=${process_group:-none}"
    continue
  fi

  # Write the terminal state before signaling.  The waiter's EXIT trap then
  # preserves `canceled` rather than misclassifying the intentional stop as a
  # dependency or launch failure.
  epoch="$(date +%s)"
  printf '%s\n' canceled >"$wait_dir/state"
  printf '%s\n' "$reason" >"$wait_dir/cancel_reason"
  printf '%s\n' "$epoch" >"$wait_dir/ended_epoch"
  if [[ -n "$process_group" ]]; then
    kill -TERM -- "-$process_group" 2>/dev/null || true
    for _ in {1..50}; do
      kill -0 -- "-$process_group" 2>/dev/null || break
      sleep 0.1
    done
    if kill -0 -- "-$process_group" 2>/dev/null; then
      kill -KILL -- "-$process_group" 2>/dev/null || true
    fi
  fi
  echo "CANCELED target=$waiter_target after=$predecessor pid=${waiter_pid:-none} pgid=${process_group:-none} reason=$reason"
  canceled=$((canceled + 1))
done

echo "CANCEL_SUMMARY matched=${#selected_dirs[@]} canceled=$canceled dry_run=$dry_run target=$target cascade=$cascade"
