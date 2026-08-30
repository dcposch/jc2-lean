#!/usr/bin/env bash
# Gate a dependency DAG opportunistically, with bounded AWS parallelism.
set -euo pipefail

# Like the individual gate and chain helpers, a durable batch executes an
# unlinked immutable snapshot so later maintenance cannot splice its shell.
if [[ "${1:-}" == --run && -z "${MAX11_GATE_BATCH_SNAPSHOT:-}" ]]; then
  original_project_dir="$(cd "$(dirname "$0")/.." && pwd)"
  script_snapshot="$(mktemp -t max11_gate_batch.sh.XXXXXX)"
  cp -p -- "$0" "$script_snapshot"
  export MAX11_GATE_BATCH_SNAPSHOT="$script_snapshot"
  export MAX11_GATE_BATCH_PROJECT_DIR="$original_project_dir"
  exec /bin/bash "$script_snapshot" "$@"
fi
if [[ -n "${MAX11_GATE_BATCH_SNAPSHOT:-}" ]]; then
  script_snapshot="$MAX11_GATE_BATCH_SNAPSHOT"
  rm -f -- "$script_snapshot"
  project_dir="${MAX11_GATE_BATCH_PROJECT_DIR:?missing project directory}"
else
  project_dir="$(cd "$(dirname "$0")/.." && pwd)"
fi
state_root="$project_dir/.max11-lanes/gate-batches"

usage() {
  echo "usage: $0 [--jobs N] [--wait-lock SECONDS] [--compile-timeout SECONDS] [--poll-seconds SECONDS] [--authoritative] -- FILE.lean [FILE.lean ...]" >&2
  exit 2
}

receipt_ready() {
  local target="$1" log="$2"
  "$project_dir/scripts/box_lean_verify.sh" --file "$target" --receipt-only \
    >"$log" 2>&1
}

newest_active_gate() {
  local target="$1" verifier_dir state candidate=""
  for verifier_dir in "$project_dir/.max11-lanes/verifiers"/*; do
    [[ -d "$verifier_dir" ]] || continue
    [[ "$(sed -n '1p' "$verifier_dir/target" 2>/dev/null || true)" == "$target" ]] || continue
    state="$(sed -n '1p' "$verifier_dir/state" 2>/dev/null || true)"
    [[ "$state" == queued || "$state" == running ]] || continue
    if [[ -z "$candidate" || "${verifier_dir##*/}" > "${candidate##*/}" ]]; then
      candidate="$verifier_dir"
    fi
  done
  printf '%s\n' "$candidate"
}

if [[ "${1:-}" == --run ]]; then
  (($# == 7)) || usage
  batch_dir="$2"
  max_jobs="$3"
  wait_lock_seconds="$4"
  authoritative="$5"
  poll_seconds="$6"
  compile_timeout_seconds="$7"
  case "$batch_dir" in
    "$state_root"/*) ;;
    *) echo "unsafe batch directory: $batch_dir" >&2; exit 2 ;;
  esac

  printf '%s\n' "$$" >"$batch_dir/pid"
  printf '%s\n' "$(date +%s)" >"$batch_dir/started_epoch"
  printf '%s\n' running >"$batch_dir/state"
  cp -p -- "$batch_dir/targets" "$batch_dir/pending"
  : >"$batch_dir/running.tsv"
  : >"$batch_dir/results.tsv"
  : >"$batch_dir/failures.tsv"
  finish_batch() {
    local exit_code=$?
    printf '%s\n' "$exit_code" >"$batch_dir/exit_code"
    printf '%s\n' "$(date +%s)" >"$batch_dir/ended_epoch"
    current_state="$(sed -n '1p' "$batch_dir/state" 2>/dev/null || true)"
    case "$current_state" in completed|failed|blocked) ;; *) printf '%s\n' failed >"$batch_dir/state" ;; esac
  }
  trap finish_batch EXIT

  while true; do
    # Reap completed gates without blocking independent branches.
    next_running="$batch_dir/running.next.$$"
    : >"$next_running"
    while IFS=$'\t' read -r target gate_job; do
      [[ -n "$target" && -n "$gate_job" ]] || continue
      gate_dir="$project_dir/.max11-lanes/verifiers/$gate_job"
      gate_state="$(sed -n '1p' "$gate_dir/state" 2>/dev/null || true)"
      case "$gate_state" in
        queued|running)
          printf '%s\t%s\n' "$target" "$gate_job" >>"$next_running"
          ;;
        verified)
          verified_sha="$(sed -n '1p' "$gate_dir/verified_sha256" 2>/dev/null || true)"
          gate_fingerprint="$(sed -nE \
            's/^GATE_FINGERPRINT=([0-9a-f]{64})$/\1/p' \
            "$gate_dir/handoff.txt" 2>/dev/null | tail -n 1)"
          printf '%s\t%s\t%s\t%s\n' "$target" "$gate_job" \
            "$verified_sha" "${gate_fingerprint:-unknown}" \
            >>"$batch_dir/results.tsv"
          ;;
        *)
          printf '%s\t%s\t%s\n' "$target" "$gate_job" \
            "${gate_state:-missing}" >>"$batch_dir/failures.tsv"
          ;;
      esac
    done <"$batch_dir/running.tsv"
    mv -f -- "$next_running" "$batch_dir/running.tsv"

    running_count="$(wc -l <"$batch_dir/running.tsv" | tr -d '[:space:]')"
    launched=0
    next_pending="$batch_dir/pending.next.$$"
    : >"$next_pending"
    while IFS= read -r target; do
      [[ -n "$target" ]] || continue
      if ((running_count >= max_jobs)); then
        printf '%s\n' "$target" >>"$next_pending"
        continue
      fi

      receipt_log="$batch_dir/receipt-${target%.lean}.log"
      if receipt_ready "$target" "$receipt_log"; then
        verified_sha="$(sed -nE \
          "s/^VERIFIED_SHA256=([0-9a-f]{64}) FILE=${target//./[.]}$/\\1/p" \
          "$receipt_log" | tail -n 1)"
        gate_fingerprint="$(sed -nE \
          's/^GATE_RECEIPT_SHA256=([0-9a-f]{64})$/\1/p' \
          "$receipt_log" | tail -n 1)"
        if [[ "$verified_sha" =~ ^[0-9a-f]{64}$ &&
              "$gate_fingerprint" =~ ^[0-9a-f]{64}$ ]]; then
          printf '%s\treceipt-reused\t%s\t%s\n' "$target" \
            "$verified_sha" "$gate_fingerprint" >>"$batch_dir/results.tsv"
          launched=$((launched + 1))
          continue
        fi
        printf '%s\treceipt-invalid\tmissing_exact_fields\n' "$target" \
          >>"$batch_dir/failures.tsv"
        continue
      fi

      # Direct verified imports encode the DAG readiness relation.  A blocked
      # target remains pending while any independent ready target can launch.
      if ! "$project_dir/scripts/max11_verified_imports.sh" --quiet "$target" \
          >"$batch_dir/imports-${target%.lean}.log" 2>&1; then
        printf '%s\n' "$target" >>"$next_pending"
        continue
      fi

      gate_args=(--file "$target" --wait-lock "$wait_lock_seconds"
        --compile-timeout "$compile_timeout_seconds")
      ((authoritative == 0)) || gate_args+=(--authoritative)
      set +e
      launch_output="$("$project_dir/scripts/max11_gate_lane.sh" \
        "${gate_args[@]}" 2>&1)"
      launch_exit=$?
      set -e
      printf '%s\n' "$launch_output" >"$batch_dir/launch-${target%.lean}.log"
      gate_job="$(sed -nE 's/^GATE_JOB=([^ ]+).*$/\1/p' \
        <<<"$launch_output" | tail -n 1)"
      if ((launch_exit == 75)) && [[ -z "$gate_job" ]]; then
        active_gate="$(newest_active_gate "$target")"
        gate_job="${active_gate##*/}"
      fi
      if ((launch_exit != 0 && launch_exit != 75)) || [[ -z "$gate_job" ]]; then
        printf '%s\tlaunch\texit_%s\n' "$target" "$launch_exit" \
          >>"$batch_dir/failures.tsv"
        continue
      fi
      printf '%s\t%s\n' "$target" "$gate_job" >>"$batch_dir/running.tsv"
      running_count=$((running_count + 1))
      launched=$((launched + 1))
    done <"$batch_dir/pending"
    mv -f -- "$next_pending" "$batch_dir/pending"

    pending_count="$(wc -l <"$batch_dir/pending" | tr -d '[:space:]')"
    running_count="$(wc -l <"$batch_dir/running.tsv" | tr -d '[:space:]')"
    result_count="$(wc -l <"$batch_dir/results.tsv" | tr -d '[:space:]')"
    failure_count="$(wc -l <"$batch_dir/failures.tsv" | tr -d '[:space:]')"
    printf 'pending=%s running=%s verified=%s failed=%s\n' \
      "$pending_count" "$running_count" "$result_count" "$failure_count" \
      >"$batch_dir/progress"

    if ((pending_count == 0 && running_count == 0)); then
      if ((failure_count == 0)); then
        printf '%s\n' completed >"$batch_dir/state"
        exit 0
      fi
      printf '%s\n' failed >"$batch_dir/state"
      exit 1
    fi
    if ((pending_count > 0 && running_count == 0 && launched == 0)); then
      {
        printf 'no target is ready and no gate is running; unresolved imports follow\n'
        while IFS= read -r target; do
          [[ -n "$target" ]] || continue
          printf '\nTARGET=%s\n' "$target"
          "$project_dir/scripts/max11_verified_imports.sh" "$target" 2>&1 || true
        done <"$batch_dir/pending"
      } >"$batch_dir/error.log"
      printf '%s\n' blocked >"$batch_dir/state"
      exit 1
    fi
    sleep "$poll_seconds"
  done
fi

max_jobs=3
wait_lock_seconds=900
poll_seconds=2
authoritative=0
compile_timeout_seconds="${BOX_LEAN_COMPILE_TIMEOUT_SECONDS:-1800}"
while (($#)); do
  case "$1" in
    --jobs)
      shift
      (($#)) || usage
      max_jobs="$1"
      ;;
    --wait-lock)
      shift
      (($#)) || usage
      wait_lock_seconds="$1"
      ;;
    --poll-seconds)
      shift
      (($#)) || usage
      poll_seconds="$1"
      ;;
    --authoritative) authoritative=1 ;;
    --compile-timeout)
      shift
      (($#)) || usage
      compile_timeout_seconds="$1"
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
[[ "$max_jobs" =~ ^[1-9][0-9]*$ && "$wait_lock_seconds" =~ ^[0-9]+$ &&
    "$poll_seconds" =~ ^[1-9][0-9]*$ &&
    "$compile_timeout_seconds" =~ ^[1-9][0-9]*$ ]] || usage
targets=("$@")
for target in "${targets[@]}"; do
  [[ "$target" =~ ^[A-Za-z0-9_.-]+Scratch[.]lean$ &&
      "$target" == "${target##*/}" && -f "$project_dir/$target" ]] || usage
done
command -v screen >/dev/null || {
  echo "screen is not available" >&2
  exit 69
}

mkdir -p "$state_root"
batch_id="$(date -u +%Y%m%dT%H%M%SZ)-gate-batch-$RANDOM"
batch_dir="$state_root/$batch_id"
mkdir "$batch_dir"
printf '%s\n' "${targets[@]}" >"$batch_dir/targets"
printf '%s\n' "$max_jobs" >"$batch_dir/max_jobs"
printf '%s\n' "$wait_lock_seconds" >"$batch_dir/wait_lock_seconds"
printf '%s\n' "$poll_seconds" >"$batch_dir/poll_seconds"
printf '%s\n' "$authoritative" >"$batch_dir/authoritative"
printf '%s\n' "$compile_timeout_seconds" >"$batch_dir/compile_timeout_seconds"
printf '%s\n' queued >"$batch_dir/state"
screen_name="max11-gate-batch-${RANDOM}-$$"
printf '%s\n' "$screen_name" >"$batch_dir/screen_session"
screen -dmS "$screen_name" "$project_dir/scripts/max11_gate_batch.sh" --run \
  "$batch_dir" "$max_jobs" "$wait_lock_seconds" "$authoritative" \
  "$poll_seconds" "$compile_timeout_seconds"
for _ in {1..20}; do
  [[ -s "$batch_dir/pid" ]] && break
  sleep 0.05
done
pid="$(sed -n '1p' "$batch_dir/pid" 2>/dev/null || printf '?')"
printf 'GATE_BATCH=%s PID=%s SCREEN=%s JOBS=%s TARGETS=%s COMPILE_TIMEOUT=%s\n' \
  "$batch_id" "$pid" "$screen_name" "$max_jobs" "${#targets[@]}" \
  "$compile_timeout_seconds"
