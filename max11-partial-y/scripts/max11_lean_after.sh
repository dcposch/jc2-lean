#!/usr/bin/env bash
# Queue one delegated proof lane behind an exact predecessor gate receipt.
set -euo pipefail

# Waiters can live for hours.  Run only the detached --run process from an
# immutable, unlinked copy so edits cannot splice bytes into live Bash.  The
# short foreground enqueue path must leave a pathname for Screen to start.
if [[ "${1:-}" == --run && -z "${MAX11_AFTER_SELF_SNAPSHOT:-}" ]]; then
  original_project_dir="$(cd "$(dirname "$0")/.." && pwd)"
  script_snapshot="$(mktemp -t max11_lean_after.sh.XXXXXX)"
  cp -p -- "$0" "$script_snapshot"
  export MAX11_AFTER_SELF_SNAPSHOT="$script_snapshot"
  export MAX11_AFTER_PROJECT_DIR="$original_project_dir"
  exec /bin/bash "$script_snapshot" "$@"
fi
if [[ -n "${MAX11_AFTER_SELF_SNAPSHOT:-}" ]]; then
  script_snapshot="$MAX11_AFTER_SELF_SNAPSHOT"
  rm -f -- "$script_snapshot"
  project_dir="${MAX11_AFTER_PROJECT_DIR:?missing immutable waiter project directory}"
else
  project_dir="$(cd "$(dirname "$0")/.." && pwd)"
fi
state_root="$project_dir/.max11-lanes/waits"

usage() {
  echo "usage: $0 --after FILE.lean --engine claude|grok --target FILE.lean [--dry-run] -- INSTRUCTION..." >&2
  exit 2
}

if [[ "${1:-}" == --run ]]; then
  (($# == 6)) || usage
  wait_dir="$2"
  predecessor="$3"
  engine="$4"
  target="$5"
  instruction="$6"
  # Nine concurrent Fable workers remain comfortably below local memory
  # pressure on the 32 GiB coordinator.  Put the tested ceiling in queued
  # successors without changing the live lane runner underneath old jobs.
  if [[ "$engine" == claude && -z "${MAX11_CLAUDE_CAP:-}" ]]; then
    export MAX11_CLAUDE_CAP=9
  fi
  case "$wait_dir" in
    "$state_root"/*) ;;
    *) echo "unsafe waiter state directory: $wait_dir" >&2; exit 2 ;;
  esac
  printf '%s\n' "$$" >"$wait_dir/pid"
  printf '%s\n' "$(date +%s)" >"$wait_dir/started_epoch"
  printf '%s\n' waiting_for_gate >"$wait_dir/state"

  finish_waiter() {
    exit_code=$?
    printf '%s\n' "$exit_code" >"$wait_dir/exit_code"
    printf '%s\n' "$(date +%s)" >"$wait_dir/ended_epoch"
    current_state="$(sed -n '1p' "$wait_dir/state" 2>/dev/null || true)"
    if [[ "$current_state" == waiting_for_gate ||
          "$current_state" == recovering_predecessor_gate ||
          "$current_state" == waiting_for_capacity ]]; then
      printf '%s\n' failed >"$wait_dir/state"
    fi
  }
  trap finish_waiter EXIT

  # Receipt lookup is exact over the predecessor's recursive source hashes and
  # tracked environment, so a changed or merely model-reported file cannot
  # release the successor.  A delegated lane can fail its independent gate and
  # then leave behind a repaired source (for example, after an asynchronous
  # edit lands).  Once no producer is active and that source has been stable
  # for three polls, recover by gating that exact content once.  This avoids a
  # permanently orphaned successor without racing a live writer or repeatedly
  # recompiling the same failed hash.
  last_seen_sha=""
  stable_source_polls=0
  last_recovery_sha=""
  while true; do
    if [[ -f "$project_dir/$predecessor" ]] &&
        "$project_dir/scripts/box_lean_verify.sh" --file "$predecessor" \
          --receipt-only >"$wait_dir/predecessor_receipt.log" 2>&1; then
      break
    fi
    if [[ -f "$project_dir/$predecessor" ]]; then
      current_sha="$(LC_ALL=C shasum -a 256 "$project_dir/$predecessor" | awk '{print $1}')"
      if [[ "$current_sha" == "$last_seen_sha" ]]; then
        stable_source_polls=$((stable_source_polls + 1))
      else
        last_seen_sha="$current_sha"
        stable_source_polls=1
      fi

      active_producer=0
      for lane_dir in "$project_dir/.max11-lanes"/*; do
        [[ -d "$lane_dir" && -f "$lane_dir/target" && -f "$lane_dir/state" ]] || continue
        [[ "$(sed -n '1p' "$lane_dir/target")" == "$predecessor" ]] || continue
        lane_state="$(sed -n '1p' "$lane_dir/state")"
        if [[ "$lane_state" == queued || "$lane_state" == running ||
              "$lane_state" == verifying ]]; then
          active_producer=1
          break
        fi
      done

      if ((active_producer == 0 && stable_source_polls >= 3)) &&
          [[ "$current_sha" != "$last_recovery_sha" ]]; then
        last_recovery_sha="$current_sha"
        printf '%s\n' recovering_predecessor_gate >"$wait_dir/state"
        set +e
        "$project_dir/scripts/box_lean_verify.sh" --file "$predecessor" \
          --wait-lock 900 >"$wait_dir/predecessor_recovery_gate.log" 2>&1
        recovery_exit=$?
        set -e
        if ((recovery_exit == 0)) &&
            "$project_dir/scripts/box_lean_verify.sh" --file "$predecessor" \
              --receipt-only >"$wait_dir/predecessor_receipt.log" 2>&1; then
          break
        fi
        printf '%s\n' waiting_for_gate >"$wait_dir/state"
      fi
    fi
    sleep "${MAX11_AFTER_POLL_SECONDS:-20}"
  done
  printf '%s\n' waiting_for_capacity >"$wait_dir/state"

  while true; do
    set +e
    launch_output="$("$project_dir/scripts/max11_lean_lane.sh" \
      --engine "$engine" --target "$target" -- "$instruction" 2>&1)"
    launch_exit=$?
    set -e
    printf '%s\n' "$launch_output" >"$wait_dir/launch.log"
    if ((launch_exit == 0)); then
      printf '%s\n' launched >"$wait_dir/state"
      printf '%s\n' "$launch_output"
      exit 0
    fi
    if ((launch_exit != 75)); then
      printf '%s\n' launch_failed >"$wait_dir/state"
      printf '%s\n' "$launch_output" >&2
      exit "$launch_exit"
    fi
    sleep "${MAX11_AFTER_POLL_SECONDS:-20}"
  done
fi

predecessor=""
engine=""
target=""
dry_run=0
while (($#)); do
  case "$1" in
    --after)
      shift
      (($#)) || usage
      predecessor="$1"
      ;;
    --engine)
      shift
      (($#)) || usage
      engine="$1"
      ;;
    --target)
      shift
      (($#)) || usage
      target="$1"
      ;;
    --dry-run)
      dry_run=1
      ;;
    --)
      shift
      break
      ;;
    *) usage ;;
  esac
  shift
done
(($#)) || usage
instruction="$*"

[[ "$predecessor" =~ ^[A-Za-z0-9_.-]+Scratch\.lean$ ]] || usage
[[ "$predecessor" == "${predecessor##*/}" ]] || usage
[[ "$engine" == claude || "$engine" == grok ]] || usage
if [[ "$engine" == claude ]]; then
  [[ "$target" =~ ^Fable[A-Za-z0-9_.-]*Scratch\.lean$ ]] || usage
else
  [[ "$target" =~ ^Grok[A-Za-z0-9_.-]*Scratch\.lean$ ]] || usage
fi
[[ "$target" == "${target##*/}" && "$target" != "$predecessor" ]] || usage
# Match the chain helper's prompt ergonomics for one-off successors.  This
# avoids silently handing literal placeholders to a delegated prover.
instruction="${instruction//@PREDECESSOR@/$predecessor}"
instruction="${instruction//@TARGET@/$target}"
if ((dry_run)); then
  printf 'AFTER=%s ENGINE=%s TARGET=%s INSTRUCTION=%q\n' \
    "$predecessor" "$engine" "$target" "$instruction"
  exit 0
fi
command -v screen >/dev/null || {
  echo "screen is not available" >&2
  exit 69
}

mkdir -p "$state_root"
for existing in "$state_root"/*; do
  [[ -d "$existing" ]] || continue
  existing_target="$(sed -n '1p' "$existing/target" 2>/dev/null || true)"
  existing_state="$(sed -n '1p' "$existing/state" 2>/dev/null || true)"
  if [[ "$existing_target" == "$target" &&
        "$existing_state" != failed && "$existing_state" != launch_failed ]]; then
    echo "a waiter already targets $target: $existing" >&2
    exit 75
  fi
done

wait_id="$(date -u +%Y%m%dT%H%M%SZ)-${target%.lean}-$RANDOM"
wait_dir="$state_root/$wait_id"
mkdir "$wait_dir"
printf '%s\n' "$predecessor" >"$wait_dir/predecessor"
printf '%s\n' "$engine" >"$wait_dir/engine"
printf '%s\n' "$target" >"$wait_dir/target"
printf '%s\n' "$instruction" >"$wait_dir/instruction"
printf '%s\n' queued >"$wait_dir/state"
screen_name="max11-after-${RANDOM}-$$"
printf '%s\n' "$screen_name" >"$wait_dir/screen_session"
screen -dmS "$screen_name" "$project_dir/scripts/max11_lean_after.sh" --run \
  "$wait_dir" "$predecessor" "$engine" "$target" "$instruction"

for _ in {1..20}; do
  [[ -s "$wait_dir/pid" ]] && break
  sleep 0.05
done
pid="$(sed -n '1p' "$wait_dir/pid" 2>/dev/null || printf '?')"
printf 'WAIT=%s PID=%s SCREEN=%s AFTER=%s ENGINE=%s TARGET=%s\n' \
  "$wait_id" "$pid" "$screen_name" "$predecessor" "$engine" "$target"
