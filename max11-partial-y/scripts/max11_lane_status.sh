#!/usr/bin/env bash
# Concise local/remote dashboard for parallel Max-11 proof lanes.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
show_remote=1

if (($#)); then
  if [[ "$1" == "--local" && $# == 1 ]]; then
    show_remote=0
  else
    echo "usage: $0 [--local]" >&2
    exit 2
  fi
fi

human_age() {
  local seconds="$1"
  if ((seconds < 60)); then
    printf '%ss' "$seconds"
  elif ((seconds < 3600)); then
    printf '%sm' "$((seconds / 60))"
  else
    printf '%sh%02sm' "$((seconds / 3600))" "$(((seconds % 3600) / 60))"
  fi
}

printf 'TRACKED WORKTREE\n'
tracked_status="$(git -C "$project_dir" status --short --untracked-files=no)"
if [[ -n "$tracked_status" ]]; then
  printf '%s\n' "$tracked_status"
else
  printf 'clean\n'
fi

printf '\nMANAGED HEADLESS WORKERS\n'
worker_rows="$(ps -axo pid=,etime=,rss=,command= | awk -v project="$project_dir" '
  index($0, "grok --yolo") && index($0, project) {print}')"
if [[ -z "$worker_rows" ]]; then
  printf 'none\n'
else
  while IFS= read -r row; do
    pid="$(awk '{print $1}' <<<"$row")"
    elapsed="$(awk '{print $2}' <<<"$row")"
    rss_kib="$(awk '{print $3}' <<<"$row")"
    target="$(grep -oE '[A-Za-z0-9_.-]+Scratch[.]lean' <<<"$row" | head -n 1 || true)"
    [[ -n "$target" ]] || target="(target not parsed)"
    printf 'pid=%s elapsed=%s rss_mib=%s target=%s\n' \
      "$pid" "$elapsed" "$((rss_kib / 1024))" "$target"
  done <<<"$worker_rows"
fi

printf '\nRECENT SCRATCH ACTIVITY (3h, newest first)\n'
now="$(date +%s)"
recent_rows="$(find "$project_dir" -maxdepth 1 -type f \
  \( -name 'Grok*Scratch.lean' -o -name 'Sol*Scratch.lean' \) \
  -mmin -180 -exec stat -f '%m|%z|%N' {} + | sort -t '|' -k1,1nr | head -n 16)"
if [[ -z "$recent_rows" ]]; then
  printf 'none\n'
else
  while IFS='|' read -r modified size path; do
    age=$((now - modified))
    printf 'age=%-5s bytes=%-7s %s\n' "$(human_age "$age")" "$size" "${path##*/}"
  done <<<"$recent_rows"
fi

if ((show_remote)); then
  printf '\n'
  "$project_dir/scripts/box_lean_status.sh"
fi
