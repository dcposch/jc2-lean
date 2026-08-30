#!/usr/bin/env bash
# Read-only status for the dedicated Lean verifier box.
set -euo pipefail

box_host="${BOX_LEAN_HOST:-ubuntu@54.81.66.156}"
box_key="${BOX_LEAN_KEY:-/Users/dc/.ssh/claude-cli.pem}"
box_dir="${BOX_LEAN_DIR:-/home/ubuntu/jc2-lean/max11-partial-y}"
ssh_args=(-i "$box_key" -o BatchMode=yes -o StrictHostKeyChecking=no)

[[ -r "$box_key" ]] || {
  echo "missing SSH key: $box_key" >&2
  exit 2
}

printf 'LOCAL VERIFIER HELPERS\n'
# Bash forks subshells for the tracked-environment hash pipeline.  Those
# children retain the script argv, so report only matching processes whose
# parent is not itself a verifier helper.
ps -axo pid=,ppid=,etime=,pcpu=,pmem=,comm=,args= |
  awk '
    ($6 == "bash" || $6 == "/bin/bash") &&
      (index($0, "bash ./scripts/box_lean_verify.sh") ||
       index($0, "box_lean_verify.sh.") ||
       index($0, "box-lean-verify-script.")) {
      row[$1] = $0
      parent[$1] = $2
    }
    END {
      for (pid in row)
        if (!(parent[pid] in row)) print row[pid]
    }' || true

lock_key="$(printf '%s\n' "$box_host|$box_dir" | LC_ALL=C shasum -a 256 | awk '{print $1}')"
canonical_lock_dir="${TMPDIR:-/tmp}/box-lean-canonical-${lock_key}.lock"
printf '\nCANONICAL GATE LOCK\n'
if [[ -d "$canonical_lock_dir" ]]; then
  printf 'held %s\n' "$canonical_lock_dir"
else
  printf 'free\n'
fi

ssh "${ssh_args[@]}" "$box_host" /bin/bash -s -- "$box_dir" <<'REMOTE'
set -euo pipefail
remote_box_dir="$1"
printf '\nREMOTE MEMORY\n'
free -h

printf '\nREMOTE SCRATCH CACHE LOCKS\n'
cache_locks="$({ ps -C flock -o pid=,etimes=,stat=,args= 2>/dev/null || true; } |
  awk -v cache="$remote_box_dir/.scratch-olean-cache/" 'index($0, cache)')"
if [[ -n "$cache_locks" ]]; then
  printf '%s\n' "$cache_locks"
else
  printf 'none\n'
fi

printf '\nREMOTE DETERMINISTIC FAILURE CACHE\n'
failure_cache_summary="$({
  while IFS= read -r failure_log; do
    failure_name="${failure_log##*/}"
    failure_bytes="$(stat -c %s "$failure_log")"
    first_error="$(grep -m 1 -E '^[^[:space:]]+[.]lean:[0-9]+:[0-9]+: error:|^[^[:space:]]+[.]lean:[0-9]+:[0-9]+: error\(' \
      "$failure_log" 2>/dev/null || true)"
    if [[ -n "$first_error" ]]; then
      first_error="${first_error%%: error*}"
    else
      first_error="unknown-location"
    fi
    printf '%s %s bytes first=%s\n' "$failure_name" "$failure_bytes" "$first_error"
  done < <(find "$remote_box_dir/.scratch-olean-cache" \
    -maxdepth 1 -type f -name '*.failure.log' -print 2>/dev/null | sort)
} || true)"
if [[ -n "$failure_cache_summary" ]]; then
  printf '%s\n' "$failure_cache_summary"
else
  printf 'empty\n'
fi

printf '\nREMOTE LEAN JOBS\n'
mapfile -t pids < <(pgrep -x lean || true)
if ((${#pids[@]} == 0)); then
  printf 'none\n'
  printf '\nDUPLICATE LEAN TARGETS\nnone\n'
  exit 0
fi
for pid in "${pids[@]}"; do
  cwd="$(readlink -f "/proc/$pid/cwd" 2>/dev/null || printf '?')"
  # A verifier can finish in the small window between pgrep and ps.  Status is
  # observational, so skip that vanished process instead of reporting a false
  # infrastructure failure under `set -e`.
  if ! row="$(ps -p "$pid" -o pid=,etimes=,pcpu=,pmem=,rss=,args= 2>/dev/null)"; then
    continue
  fi
  printf '%s cwd=%s\n' "$row" "$cwd"
done

printf '\nDUPLICATE LEAN TARGETS\n'
duplicates="$({
  for pid in "${pids[@]}"; do
    tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null || true
    printf '\n'
  done
} | awk '{target=$NF; if (target ~ /[.]lean$/) count[target]++}
  END {for (target in count) if (count[target] > 1) print count[target], target}' |
  sort -nr)"
if [[ -n "$duplicates" ]]; then
  printf '%s\n' "$duplicates"
else
  printf 'none\n'
fi
REMOTE
