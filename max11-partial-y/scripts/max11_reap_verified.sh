#!/usr/bin/env bash
# Reclaim delegated model processes that linger after their exact gate passed.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
state_root="$project_dir/.max11-lanes"
dry_run=0

usage() {
  echo "usage: $0 [--dry-run]" >&2
  exit 2
}

if [[ "${1:-}" == --dry-run ]]; then
  dry_run=1
  shift
fi
(($# == 0)) || usage

candidate_count=0
reaped_count=0
for lane_dir in "$state_root"/*; do
  [[ -d "$lane_dir" && -f "$lane_dir/state" && -f "$lane_dir/target" ]] || continue
  [[ "$(sed -n '1p' "$lane_dir/state")" == running ]] || continue

  target="$(sed -n '1p' "$lane_dir/target")"
  [[ "$target" =~ ^[A-Za-z0-9_.-]+Scratch[.]lean$ &&
      "$target" == "${target##*/}" && -f "$project_dir/$target" ]] || continue

  receipt_output="$(
    "$project_dir/scripts/box_lean_verify.sh" --file "$target" --receipt-only 2>/dev/null
  )" || continue
  expected_sha="$(sed -nE \
    "s/^VERIFIED_SHA256=([0-9a-f]{64}) FILE=${target//./[.]}$/\\1/p" \
    <<<"$receipt_output" | tail -1)"
  [[ "$expected_sha" =~ ^[0-9a-f]{64}$ ]] || continue
  current_sha="$(LC_ALL=C shasum -a 256 "$project_dir/$target" | awk '{print $1}')"
  [[ "$current_sha" == "$expected_sha" ]] || continue
  candidate_count=$((candidate_count + 1))

  runner_pid="$(sed -n '1p' "$lane_dir/pid" 2>/dev/null || true)"
  process_group=""
  if [[ "$runner_pid" =~ ^[0-9]+$ ]] && kill -0 "$runner_pid" 2>/dev/null; then
    process_group="$(ps -o pgid= -p "$runner_pid" | tr -d '[:space:]')"
    [[ "$process_group" =~ ^[0-9]+$ ]] || {
      echo "SKIP target=$target reason=missing_process_group" >&2
      continue
    }
    group_leader_command="$(ps -o command= -p "$process_group" 2>/dev/null || true)"
    if [[ "$group_leader_command" != *"max11_lean_lane.sh --run $lane_dir"* ]]; then
      echo "SKIP target=$target reason=unvalidated_process_group pgid=$process_group" >&2
      continue
    fi
  fi

  if ((dry_run)); then
    echo "WOULD_REAP target=$target pid=${runner_pid:-none} pgid=${process_group:-none} sha256=$expected_sha"
    continue
  fi

  if [[ -n "$process_group" ]]; then
    kill -TERM -- "-$process_group" 2>/dev/null || true
    for _ in {1..50}; do
      kill -0 -- "-$process_group" 2>/dev/null || break
      sleep 0.1
    done
    if kill -0 -- "-$process_group" 2>/dev/null; then
      kill -KILL -- "-$process_group" 2>/dev/null || true
      for _ in {1..20}; do
        kill -0 -- "-$process_group" 2>/dev/null || break
        sleep 0.1
      done
    fi
    if kill -0 -- "-$process_group" 2>/dev/null; then
      echo "SKIP target=$target reason=process_group_survived pgid=$process_group" >&2
      continue
    fi
  fi

  # Fail closed across the shutdown window: recursive dependencies, tracked
  # environment, and the leaf must still match the exact successful receipt.
  if ! "$project_dir/scripts/box_lean_verify.sh" --file "$target" \
      --receipt-only >/dev/null 2>&1; then
    echo "SKIP target=$target reason=receipt_changed_after_shutdown" >&2
    continue
  fi
  current_sha="$(LC_ALL=C shasum -a 256 "$project_dir/$target" | awk '{print $1}')"
  [[ "$current_sha" == "$expected_sha" ]] || {
    echo "SKIP target=$target reason=source_changed_after_shutdown" >&2
    continue
  }

  epoch="$(date +%s)"
  printf '%s\n' verified >"$lane_dir/state"
  printf '%s\n' "$expected_sha" >"$lane_dir/verified_sha256"
  printf '%s\n' "$epoch" >"$lane_dir/verified_epoch"
  printf '%s\n' "$epoch" >"$lane_dir/ended_epoch"
  echo "REAPED target=$target pid=${runner_pid:-none} pgid=${process_group:-none} sha256=$expected_sha"
  reaped_count=$((reaped_count + 1))
done

echo "REAP_SUMMARY candidates=$candidate_count reaped=$reaped_count dry_run=$dry_run"
