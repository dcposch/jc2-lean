#!/usr/bin/env bash
# Run a bounded symbolic-algebra check with a durable, inspectable ledger.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
state_root="$project_dir/.max11-lanes/cas"
name=""
timeout_seconds="${MAX11_CAS_TIMEOUT_SECONDS:-900}"
input_file=""

usage() {
  echo "usage: $0 --name LABEL [--timeout SECONDS] [--input FILE] -- COMMAND [ARG ...]" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --name)
      shift
      (($#)) || usage
      name="$1"
      ;;
    --timeout)
      shift
      (($#)) || usage
      timeout_seconds="$1"
      ;;
    --input)
      shift
      (($#)) || usage
      input_file="$1"
      ;;
    --)
      shift
      break
      ;;
    *) usage ;;
  esac
  shift
done

[[ "$name" =~ ^[A-Za-z0-9_.-]+$ && "$timeout_seconds" =~ ^[1-9][0-9]*$ ]] || usage
(($#)) || usage
if [[ -n "$input_file" ]]; then
  [[ -f "$input_file" ]] || {
    echo "missing CAS input: $input_file" >&2
    exit 2
  }
  input_file="$(cd "$(dirname "$input_file")" && pwd)/$(basename "$input_file")"
fi

mkdir -p "$state_root"
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
job_dir="$state_root/$stamp-$name-$$"
mkdir "$job_dir"

started_epoch="$(date +%s)"
printf '%s\n' "$name" >"$job_dir/name"
printf '%s\n' "$started_epoch" >"$job_dir/started_epoch"
printf '%s\n' "$timeout_seconds" >"$job_dir/timeout_seconds"
printf 'running\n' >"$job_dir/state"
printf '%q ' "$@" >"$job_dir/command"
printf '\n' >>"$job_dir/command"
if [[ -n "$input_file" ]]; then
  printf '%s\n' "$input_file" >"$job_dir/input"
  shasum -a 256 "$input_file" | awk '{print $1}' >"$job_dir/input_sha256"
fi

output_log="$job_dir/output.log"
samples="$job_dir/resources.tsv"
printf 'epoch\tpid\tcpu_percent\trss_kib\telapsed\n' >"$samples"
printf 'CAS_JOB=%s TIMEOUT_SECONDS=%s\n' "$job_dir" "$timeout_seconds"

if [[ -n "$input_file" ]]; then
  "$@" <"$input_file" >"$output_log" 2>&1 &
else
  "$@" >"$output_log" 2>&1 &
fi
child_pid=$!
printf '%s\n' "$child_pid" >"$job_dir/pid"

terminal_state="interrupted"
finish_ledger() {
  local ended_epoch
  ended_epoch="$(date +%s)"
  printf '%s\n' "$ended_epoch" >"$job_dir/ended_epoch"
  printf '%s\n' "$terminal_state" >"$job_dir/state"
}
stop_child() {
  if kill -0 "$child_pid" 2>/dev/null; then
    kill -TERM "$child_pid" 2>/dev/null || true
    for _ in {1..50}; do
      kill -0 "$child_pid" 2>/dev/null || break
      sleep 0.1
    done
    kill -0 "$child_pid" 2>/dev/null && kill -KILL "$child_pid" 2>/dev/null || true
  fi
}
on_signal() {
  stop_child
  terminal_state="interrupted"
  finish_ledger
  exit 130
}
trap on_signal INT TERM HUP

deadline=$((started_epoch + timeout_seconds))
while kill -0 "$child_pid" 2>/dev/null; do
  child_state="$(ps -p "$child_pid" -o state= 2>/dev/null | tr -d '[:space:]')"
  [[ -n "$child_state" && "$child_state" != *Z* ]] || break
  now="$(date +%s)"
  ps -p "$child_pid" -o pid=,%cpu=,rss=,etime= 2>/dev/null |
    awk -v epoch="$now" '{print epoch "\t" $1 "\t" $2 "\t" $3 "\t" $4}' >>"$samples" || true
  if ((now >= deadline)); then
    stop_child
    set +e
    wait "$child_pid" 2>/dev/null
    set -e
    terminal_state="timed_out"
    printf '124\n' >"$job_dir/exit_code"
    finish_ledger
    printf 'CAS_EXIT=124 STATE=timed_out LOG=%s\n' "$output_log"
    exit 124
  fi
  sleep 2
done

set +e
wait "$child_pid"
exit_code=$?
set -e
printf '%s\n' "$exit_code" >"$job_dir/exit_code"
if ((exit_code == 0)); then
  terminal_state="succeeded"
else
  terminal_state="failed"
fi
finish_ledger
printf 'CAS_EXIT=%s STATE=%s LOG=%s\n' "$exit_code" "$terminal_state" "$output_log"
exit "$exit_code"
