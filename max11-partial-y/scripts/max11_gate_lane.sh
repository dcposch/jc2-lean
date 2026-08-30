#!/usr/bin/env bash
# Run one exact scratch gate detached from the invoking Codex/terminal process.
set -euo pipefail

# Long gates must survive both caller termination and edits to this helper.
if [[ "${1:-}" == --run && -z "${MAX11_GATE_SELF_SNAPSHOT:-}" ]]; then
  original_project_dir="$(cd "$(dirname "$0")/.." && pwd)"
  script_snapshot="$(mktemp -t max11_gate_lane.sh.XXXXXX)"
  cp -p -- "$0" "$script_snapshot"
  export MAX11_GATE_SELF_SNAPSHOT="$script_snapshot"
  export MAX11_GATE_PROJECT_DIR="$original_project_dir"
  exec /bin/bash "$script_snapshot" "$@"
fi
if [[ -n "${MAX11_GATE_SELF_SNAPSHOT:-}" ]]; then
  script_snapshot="$MAX11_GATE_SELF_SNAPSHOT"
  rm -f -- "$script_snapshot"
  project_dir="${MAX11_GATE_PROJECT_DIR:?missing immutable gate project directory}"
else
  project_dir="$(cd "$(dirname "$0")/.." && pwd)"
fi
state_root="$project_dir/.max11-lanes/verifiers"

usage() {
  echo "usage: $0 --file FILE.lean [--wait-lock SECONDS] [--authoritative] [--retry-known-failure] [--allow-unverified-imports]" >&2
  exit 2
}

if [[ "${1:-}" == --run ]]; then
  (($# == 6)) || usage
  job_dir="$2"
  target="$3"
  wait_lock_seconds="$4"
  reuse_receipt="$5"
  retry_known_failure="$6"
  case "$job_dir" in
    "$state_root"/*) ;;
    *) echo "unsafe verifier state directory: $job_dir" >&2; exit 2 ;;
  esac

  printf '%s\n' "$$" >"$job_dir/pid"
  printf '%s\n' "$(date +%s)" >"$job_dir/started_epoch"
  printf '%s\n' running >"$job_dir/state"

  finish_gate() {
    exit_code=$?
    printf '%s\n' "$exit_code" >"$job_dir/exit_code"
    printf '%s\n' "$(date +%s)" >"$job_dir/ended_epoch"
    current_state="$(sed -n '1p' "$job_dir/state" 2>/dev/null || true)"
    if [[ "$current_state" == queued || "$current_state" == running ]]; then
      printf '%s\n' failed >"$job_dir/state"
    fi
  }
  trap finish_gate EXIT

  verify_args=(--file "$target" --wait-lock "$wait_lock_seconds")
  ((reuse_receipt == 0)) || verify_args+=(--reuse-receipt)
  ((retry_known_failure == 0)) || verify_args+=(--retry-known-failure)
  set +e
  "$project_dir/scripts/box_lean_verify.sh" "${verify_args[@]}" \
    >"$job_dir/output.log" 2>&1
  verify_exit=$?
  set -e
  if ((verify_exit != 0)); then
    first_error="$(grep -m 1 -E \
      '^[^[:space:]]+[.]lean:[0-9]+:[0-9]+: error:|^[^[:space:]]+[.]lean:[0-9]+:[0-9]+: error\(|^LEAN_COMPILE_TIMEOUT ' \
      "$job_dir/output.log" 2>/dev/null || true)"
    {
      printf 'HANDOFF_VERSION=1\nRESULT=failed\nTARGET=%s\nEXIT_CODE=%s\n' \
        "$target" "$verify_exit"
      [[ -z "$first_error" ]] || printf 'FIRST_ERROR=%s\n' "$first_error"
    } >"$job_dir/handoff.txt"
    exit "$verify_exit"
  fi

  if ! "$project_dir/scripts/box_lean_verify.sh" --file "$target" \
      --receipt-only >"$job_dir/receipt.log" 2>&1; then
    echo "successful gate lost its exact receipt: $target" >>"$job_dir/output.log"
    exit 1
  fi
  verified_sha="$(sed -nE \
    "s/^VERIFIED_SHA256=([0-9a-f]{64}) FILE=${target//./[.]}$/\\1/p" \
    "$job_dir/receipt.log" | tail -1)"
  [[ "$verified_sha" =~ ^[0-9a-f]{64}$ ]] || {
    echo "exact leaf SHA missing from receipt: $target" >>"$job_dir/output.log"
    exit 1
  }
  gate_fingerprint="$(sed -nE \
    's/^GATE_RECEIPT_SHA256=([0-9a-f]{64})$/\1/p' \
    "$job_dir/receipt.log" | tail -1)"
  printf '%s\n' "$verified_sha" >"$job_dir/verified_sha256"
  {
    printf 'HANDOFF_VERSION=1\nRESULT=verified\nTARGET=%s\n' "$target"
    printf 'VERIFIED_SHA256=%s\nGATE_FINGERPRINT=%s\n' \
      "$verified_sha" "${gate_fingerprint:-unknown}"
    printf 'RECENT_DECLARATIONS\n'
    rg -n --no-heading \
      '^(private |protected )?(noncomputable )?(theorem|lemma|def|abbrev) ' \
      "$project_dir/$target" 2>/dev/null | tail -n 8 | cut -c 1-400 || true
  } >"$job_dir/handoff.txt"
  printf '%s\n' verified >"$job_dir/state"
  exit 0
fi

target=""
wait_lock_seconds=900
reuse_receipt=1
retry_known_failure=0
allow_unverified_imports=0
while (($#)); do
  case "$1" in
    --file)
      shift
      (($#)) || usage
      target="$1"
      ;;
    --wait-lock)
      shift
      (($#)) || usage
      [[ "$1" =~ ^[0-9]+$ ]] || usage
      wait_lock_seconds="$1"
      ;;
    --authoritative) reuse_receipt=0 ;;
    --retry-known-failure) retry_known_failure=1 ;;
    --allow-unverified-imports) allow_unverified_imports=1 ;;
    *) usage ;;
  esac
  shift
done

[[ "$target" =~ ^[A-Za-z0-9_.-]+Scratch[.]lean$ &&
    "$target" == "${target##*/}" && -f "$project_dir/$target" ]] || usage
command -v screen >/dev/null || {
  echo "screen is not available" >&2
  exit 69
}

if ((allow_unverified_imports == 0)); then
  "$project_dir/scripts/max11_verified_imports.sh" "$target"
fi

mkdir -p "$state_root"
for existing in "$state_root"/*; do
  [[ -d "$existing" ]] || continue
  existing_target="$(sed -n '1p' "$existing/target" 2>/dev/null || true)"
  existing_state="$(sed -n '1p' "$existing/state" 2>/dev/null || true)"
  if [[ "$existing_target" == "$target" &&
        ( "$existing_state" == queued || "$existing_state" == running ) ]]; then
    echo "a durable verifier already targets $target: $existing" >&2
    exit 75
  fi
done

job_id="$(date -u +%Y%m%dT%H%M%SZ)-${target%.lean}-$RANDOM"
job_dir="$state_root/$job_id"
mkdir "$job_dir"
printf '%s\n' "$target" >"$job_dir/target"
printf '%s\n' "$wait_lock_seconds" >"$job_dir/wait_lock_seconds"
printf '%s\n' "$reuse_receipt" >"$job_dir/reuse_receipt"
printf '%s\n' "$retry_known_failure" >"$job_dir/retry_known_failure"
printf '%s\n' queued >"$job_dir/state"
screen_name="max11-gate-${RANDOM}-$$"
printf '%s\n' "$screen_name" >"$job_dir/screen_session"
screen -dmS "$screen_name" "$project_dir/scripts/max11_gate_lane.sh" --run \
  "$job_dir" "$target" "$wait_lock_seconds" "$reuse_receipt" \
  "$retry_known_failure"

for _ in {1..20}; do
  [[ -s "$job_dir/pid" ]] && break
  sleep 0.05
done
pid="$(sed -n '1p' "$job_dir/pid" 2>/dev/null || printf '?')"
printf 'GATE_JOB=%s PID=%s SCREEN=%s TARGET=%s LOG=%s\n' \
  "$job_id" "$pid" "$screen_name" "$target" "$job_dir/output.log"
