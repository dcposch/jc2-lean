#!/usr/bin/env bash
# Read-only status for the dedicated Lean verifier box.
set -euo pipefail

box_host="${BOX_LEAN_HOST:-ubuntu@54.81.66.156}"
box_key="${BOX_LEAN_KEY:-/Users/dc/.ssh/claude-cli.pem}"
ssh_args=(-i "$box_key" -o BatchMode=yes -o StrictHostKeyChecking=no)

[[ -r "$box_key" ]] || {
  echo "missing SSH key: $box_key" >&2
  exit 2
}

printf 'LOCAL VERIFIER HELPERS\n'
ps -axo pid=,etime=,pcpu=,pmem=,comm=,args= |
  awk '$5 == "bash" && index($0, "bash ./scripts/box_lean_verify.sh") {print}' || true

ssh "${ssh_args[@]}" "$box_host" 'bash -s' <<'REMOTE'
set -euo pipefail
printf '\nREMOTE MEMORY\n'
free -h

printf '\nREMOTE LEAN JOBS\n'
mapfile -t pids < <(pgrep -x lean || true)
if ((${#pids[@]} == 0)); then
  printf 'none\n'
  printf '\nDUPLICATE LEAN TARGETS\nnone\n'
  exit 0
fi
for pid in "${pids[@]}"; do
  cwd="$(readlink -f "/proc/$pid/cwd" 2>/dev/null || printf '?')"
  row="$(ps -p "$pid" -o pid=,etimes=,pcpu=,pmem=,rss=,args=)"
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
