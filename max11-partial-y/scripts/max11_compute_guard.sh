#!/usr/bin/env bash
# Find long-running Max-11 CAS processes that bypassed the durable job ledger.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
max_age="${MAX11_UNMANAGED_COMPUTE_MAX_AGE_SECONDS:-900}"
terminate=0

usage() {
  echo "usage: $0 [--max-age SECONDS] [--terminate]" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --max-age)
      shift
      (($#)) || usage
      max_age="$1"
      ;;
    --terminate) terminate=1 ;;
    *) usage ;;
  esac
  shift
done
[[ "$max_age" =~ ^[0-9]+$ ]] || usage

elapsed_seconds() {
  local elapsed="$1" days=0 hours=0 minutes=0 seconds=0
  if [[ "$elapsed" == *-* ]]; then
    days="${elapsed%%-*}"
    elapsed="${elapsed#*-}"
  fi
  local fields
  fields="$(awk -F: '{print NF}' <<<"$elapsed")"
  case "$fields" in
    3) IFS=: read -r hours minutes seconds <<<"$elapsed" ;;
    2) IFS=: read -r minutes seconds <<<"$elapsed" ;;
    1) seconds="$elapsed" ;;
    *) return 1 ;;
  esac
  printf '%s\n' "$((10#$days * 86400 + 10#$hours * 3600 + 10#$minutes * 60 + 10#$seconds))"
}

managed_pid_file="$(mktemp -t max11-managed-cas.XXXXXX)"
rows_file="$(mktemp -t max11-unmanaged-compute.XXXXXX)"
trap 'rm -f -- "$managed_pid_file" "$rows_file"' EXIT

cas_root="$project_dir/.max11-lanes/cas"
if [[ -d "$cas_root" ]]; then
  for job_dir in "$cas_root"/*; do
    [[ -d "$job_dir" ]] || continue
    [[ "$(sed -n '1p' "$job_dir/state" 2>/dev/null || true)" == running ]] || continue
    sed -nE '/^[0-9]+$/p' "$job_dir/pid" 2>/dev/null >>"$managed_pid_file" || true
  done
fi

# `ps` cannot report cwd portably.  First restrict to likely CAS commands,
# then ask lsof only about those few candidates and require this exact project
# directory.  This avoids ever touching unrelated user processes.
ps -axo pid=,ppid=,%cpu=,rss=,etime=,ucomm=,command= |
  while read -r pid ppid cpu rss elapsed executable command; do
    [[ "$pid" =~ ^[0-9]+$ ]] || continue
    case "$executable" in
      *Python*|*python*|*Singular*|*sage*|*Macaulay2*|*macaulay2*|*sympy*) ;;
      *) continue ;;
    esac
    grep -qx "$pid" "$managed_pid_file" 2>/dev/null && continue
    age="$(elapsed_seconds "$elapsed" 2>/dev/null || printf '0')"
    ((age >= max_age)) || continue
    cwd="$(lsof -a -p "$pid" -d cwd -Fn 2>/dev/null | sed -n 's/^n//p' | head -n 1)"
    [[ "$cwd" == "$project_dir" ]] || continue
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$pid" "$ppid" "$cpu" "$rss" "$age" "$command"
  done >"$rows_file"

if [[ ! -s "$rows_file" ]]; then
  printf 'none (threshold=%ss)\n' "$max_age"
  exit 0
fi

while IFS=$'\t' read -r pid ppid cpu rss age command; do
  printf 'pid=%s ppid=%s age=%ss cpu=%s%% rss_mib=%s command=%s\n' \
    "$pid" "$ppid" "$age" "$cpu" "$((rss / 1024))" "$command"
  if ((terminate)); then
    if kill -TERM "$pid" 2>/dev/null; then
      printf 'TERMINATED pid=%s signal=TERM\n' "$pid"
    else
      printf 'TERMINATE_FAILED pid=%s\n' "$pid" >&2
    fi
  fi
done <"$rows_file"

if ((!terminate)); then
  printf 'ACTION=review_then_run_%s_--terminate\n' "${0##*/}"
fi
