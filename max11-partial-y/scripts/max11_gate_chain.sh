#!/usr/bin/env bash
# Run an ordered chain of exact Max-11 gates without coordinator polling gaps.
set -euo pipefail

# A chain can outlive the shell that enqueued it.  Snapshot this helper before
# entering the durable worker so later edits cannot splice into a live run.
if [[ "${1:-}" == --run && -z "${MAX11_GATE_CHAIN_SNAPSHOT:-}" ]]; then
  original_project_dir="$(cd "$(dirname "$0")/.." && pwd)"
  script_snapshot="$(mktemp -t max11_gate_chain.sh.XXXXXX)"
  cp -p -- "$0" "$script_snapshot"
  export MAX11_GATE_CHAIN_SNAPSHOT="$script_snapshot"
  export MAX11_GATE_CHAIN_PROJECT_DIR="$original_project_dir"
  exec /bin/bash "$script_snapshot" "$@"
fi
if [[ -n "${MAX11_GATE_CHAIN_SNAPSHOT:-}" ]]; then
  script_snapshot="$MAX11_GATE_CHAIN_SNAPSHOT"
  rm -f -- "$script_snapshot"
  project_dir="${MAX11_GATE_CHAIN_PROJECT_DIR:?missing project directory}"
else
  project_dir="$(cd "$(dirname "$0")/.." && pwd)"
fi
state_root="$project_dir/.max11-lanes/gate-chains"

usage() {
  echo "usage: $0 [--after FILE.lean] [--wait-lock SECONDS] [--authoritative] -- FILE.lean [FILE.lean ...]" >&2
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
  (($# == 5)) || usage
  chain_dir="$2"
  predecessor="$3"
  wait_lock_seconds="$4"
  authoritative="$5"
  case "$chain_dir" in
    "$state_root"/*) ;;
    *) echo "unsafe chain directory: $chain_dir" >&2; exit 2 ;;
  esac

  printf '%s\n' "$$" >"$chain_dir/pid"
  printf '%s\n' "$(date +%s)" >"$chain_dir/started_epoch"
  printf '%s\n' starting >"$chain_dir/state"
  finish_chain() {
    local exit_code=$?
    printf '%s\n' "$exit_code" >"$chain_dir/exit_code"
    printf '%s\n' "$(date +%s)" >"$chain_dir/ended_epoch"
    current_state="$(sed -n '1p' "$chain_dir/state" 2>/dev/null || true)"
    case "$current_state" in
      completed|failed) ;;
      *) printf '%s\n' failed >"$chain_dir/state" ;;
    esac
  }
  trap finish_chain EXIT

  if [[ -n "$predecessor" ]]; then
    printf '%s\n' waiting_for_predecessor >"$chain_dir/state"
    while ! receipt_ready "$predecessor" "$chain_dir/predecessor_receipt.log"; do
      active_gate="$(newest_active_gate "$predecessor")"
      if [[ -n "$active_gate" ]]; then
        printf '%s\n' "${active_gate##*/}" >"$chain_dir/predecessor_gate_job"
        while true; do
          gate_state="$(sed -n '1p' "$active_gate/state" 2>/dev/null || true)"
          case "$gate_state" in
            queued|running) sleep 2 ;;
            verified) break ;;
            *)
              printf 'predecessor gate ended in state %s: %s\n' \
                "$gate_state" "$predecessor" >"$chain_dir/error.log"
              printf '%s\n' failed >"$chain_dir/state"
              exit 1
              ;;
          esac
        done
      else
        sleep 20
      fi
    done
  fi

  : >"$chain_dir/results.tsv"
  while IFS= read -r target; do
    [[ -n "$target" ]] || continue
    printf '%s\n' "$target" >"$chain_dir/current_target"
    printf '%s\n' launching_gate >"$chain_dir/state"
    gate_args=(--file "$target" --wait-lock "$wait_lock_seconds")
    ((authoritative == 0)) || gate_args+=(--authoritative)
    set +e
    launch_output="$("$project_dir/scripts/max11_gate_lane.sh" \
      "${gate_args[@]}" 2>&1)"
    launch_exit=$?
    set -e
    printf '%s\n' "$launch_output" >"$chain_dir/launch-${target%.lean}.log"
    gate_job="$(sed -nE 's/^GATE_JOB=([^ ]+).*$/\1/p' <<<"$launch_output" | tail -1)"
    if ((launch_exit == 75)) && [[ -z "$gate_job" ]]; then
      active_gate="$(newest_active_gate "$target")"
      gate_job="${active_gate##*/}"
    fi
    if ((launch_exit != 0 && launch_exit != 75)) || [[ -z "$gate_job" ]]; then
      printf 'gate launch failed exit=%s target=%s\n%s\n' \
        "$launch_exit" "$target" "$launch_output" >"$chain_dir/error.log"
      printf '%s\n' failed >"$chain_dir/state"
      exit 1
    fi
    gate_dir="$project_dir/.max11-lanes/verifiers/$gate_job"
    [[ -d "$gate_dir" ]] || {
      printf 'missing verifier ledger target=%s job=%s\n' \
        "$target" "$gate_job" >"$chain_dir/error.log"
      printf '%s\n' failed >"$chain_dir/state"
      exit 1
    }
    printf '%s\n' "$gate_job" >"$chain_dir/current_gate_job"
    printf '%s\n' waiting_for_gate >"$chain_dir/state"
    while true; do
      gate_state="$(sed -n '1p' "$gate_dir/state" 2>/dev/null || true)"
      case "$gate_state" in
        queued|running) sleep 2 ;;
        verified)
          verified_sha="$(sed -n '1p' "$gate_dir/verified_sha256")"
          printf '%s\t%s\t%s\n' "$target" "$gate_job" "$verified_sha" \
            >>"$chain_dir/results.tsv"
          break
          ;;
        *)
          printf 'gate ended in state %s target=%s job=%s\n' \
            "$gate_state" "$target" "$gate_job" >"$chain_dir/error.log"
          printf '%s\n' failed >"$chain_dir/state"
          exit 1
          ;;
      esac
    done
  done <"$chain_dir/targets"

  rm -f -- "$chain_dir/current_target" "$chain_dir/current_gate_job"
  printf '%s\n' completed >"$chain_dir/state"
  exit 0
fi

predecessor=""
wait_lock_seconds=900
authoritative=0
while (($#)); do
  case "$1" in
    --after)
      shift
      (($#)) || usage
      predecessor="$1"
      ;;
    --wait-lock)
      shift
      (($#)) || usage
      wait_lock_seconds="$1"
      ;;
    --authoritative) authoritative=1 ;;
    --)
      shift
      break
      ;;
    *) usage ;;
  esac
  shift
done
(($#)) || usage
[[ "$wait_lock_seconds" =~ ^[0-9]+$ ]] || usage
if [[ -n "$predecessor" ]]; then
  [[ "$predecessor" =~ ^[A-Za-z0-9_.-]+Scratch[.]lean$ &&
      "$predecessor" == "${predecessor##*/}" &&
      -f "$project_dir/$predecessor" ]] || usage
fi
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
chain_id="$(date -u +%Y%m%dT%H%M%SZ)-gate-chain-$RANDOM"
chain_dir="$state_root/$chain_id"
mkdir "$chain_dir"
printf '%s\n' "$predecessor" >"$chain_dir/predecessor"
printf '%s\n' "$wait_lock_seconds" >"$chain_dir/wait_lock_seconds"
printf '%s\n' "$authoritative" >"$chain_dir/authoritative"
printf '%s\n' "${targets[@]}" >"$chain_dir/targets"
printf '%s\n' queued >"$chain_dir/state"
screen_name="max11-gate-chain-${RANDOM}-$$"
printf '%s\n' "$screen_name" >"$chain_dir/screen_session"
screen -dmS "$screen_name" "$project_dir/scripts/max11_gate_chain.sh" --run \
  "$chain_dir" "$predecessor" "$wait_lock_seconds" "$authoritative"
for _ in {1..20}; do
  [[ -s "$chain_dir/pid" ]] && break
  sleep 0.05
done
pid="$(sed -n '1p' "$chain_dir/pid" 2>/dev/null || printf '?')"
printf 'GATE_CHAIN=%s PID=%s SCREEN=%s AFTER=%s TARGETS=%s\n' \
  "$chain_id" "$pid" "$screen_name" "${predecessor:-none}" "${#targets[@]}"
