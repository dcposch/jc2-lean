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
  (index($0, "grok --yolo") ||
   (index($0, "claude ") && index($0, " -p "))) &&
    (index($0, project) || index($0, "LOCAL_LEAN_GUARD=enabled")) {print}')"
if [[ -z "$worker_rows" ]]; then
  printf 'none\n'
else
  while IFS= read -r row; do
    pid="$(awk '{print $1}' <<<"$row")"
    elapsed="$(awk '{print $2}' <<<"$row")"
    rss_kib="$(awk '{print $3}' <<<"$row")"
    engine="grok"
    [[ "$row" == *"claude "*" -p "* ]] && engine="claude"
    # Continuation prompts mention their predecessor before the requested
    # output.  The final scratch filename is therefore the worker target.
    target="$(grep -oE '[A-Za-z0-9_.-]+Scratch[.]lean' <<<"$row" | tail -n 1 || true)"
    [[ -n "$target" ]] || target="(target not parsed)"
    guard="prompt-only"
    [[ "$row" == *"LOCAL_LEAN_GUARD=enabled"* ]] && guard="enforced"
    printf 'pid=%s elapsed=%s rss_mib=%s engine=%s guard=%s target=%s\n' \
      "$pid" "$elapsed" "$((rss_kib / 1024))" "$engine" "$guard" "$target"
  done <<<"$worker_rows"
fi

printf '\nQUEUED FOLLOW-UPS\n'
wait_root="$project_dir/.max11-lanes/waits"
wait_dirs=""
if [[ -d "$wait_root" ]]; then
  wait_dirs="$(find "$wait_root" -mindepth 1 -maxdepth 1 -type d | sort -r)"
fi
if [[ -z "$wait_dirs" ]]; then
  printf 'none\n'
else
  while IFS= read -r wait_dir; do
    state="$(sed -n '1p' "$wait_dir/state" 2>/dev/null || printf '?')"
    predecessor="$(sed -n '1p' "$wait_dir/predecessor" 2>/dev/null || printf '?')"
    engine="$(sed -n '1p' "$wait_dir/engine" 2>/dev/null || printf '?')"
    target="$(sed -n '1p' "$wait_dir/target" 2>/dev/null || printf '?')"
    pid="$(sed -n '1p' "$wait_dir/pid" 2>/dev/null || printf '?')"
    if [[ "$state" == waiting_for_gate || "$state" == waiting_for_capacity ]] &&
        [[ "$pid" =~ ^[0-9]+$ ]] && ! kill -0 "$pid" 2>/dev/null; then
      state="stale"
    fi
    printf 'state=%s pid=%s engine=%s after=%s target=%s\n' \
      "$state" "$pid" "$engine" "$predecessor" "$target"
  done <<<"$wait_dirs"
fi

now="$(date +%s)"
printf '\nDURABLE LANE LEDGER (newest 12)\n'
state_root="$project_dir/.max11-lanes"
ledger_dirs=""
if [[ -d "$state_root" ]]; then
  ledger_dirs="$(find "$state_root" -mindepth 1 -maxdepth 1 -type d \
    ! -name gates ! -name waits | sort -r | head -n 12)"
fi
if [[ -z "$ledger_dirs" ]]; then
  printf 'none (legacy workers predate ledger)\n'
else
  while IFS= read -r job_dir; do
    job="${job_dir##*/}"
    engine="$(sed -n '1p' "$job_dir/engine" 2>/dev/null || printf '?')"
    target="$(sed -n '1p' "$job_dir/target" 2>/dev/null || printf '?')"
    state="$(sed -n '1p' "$job_dir/state" 2>/dev/null || printf '?')"
    pid="$(sed -n '1p' "$job_dir/pid" 2>/dev/null || printf '?')"
    if [[ "$state" == running || "$state" == verifying ]] &&
        [[ "$pid" =~ ^[0-9]+$ ]] &&
        ! kill -0 "$pid" 2>/dev/null; then
      state="stale"
    fi
    started="$(sed -n '1p' "$job_dir/started_epoch" 2>/dev/null || printf '%s' "$now")"
    ended="$(sed -n '1p' "$job_dir/ended_epoch" 2>/dev/null || printf '%s' "$now")"
    [[ "$started" =~ ^[0-9]+$ ]] || started="$now"
    [[ "$ended" =~ ^[0-9]+$ ]] || ended="$now"
    if [[ "$state" == running || "$state" == queued ]]; then
      age=$((now - started))
    else
      age=$((ended - started))
    fi
    verified_sha="$(sed -n '1p' "$job_dir/verified_sha256" 2>/dev/null || true)"
    if [[ "$state" == succeeded && -z "$verified_sha" ]]; then
      state="worker_succeeded_unverified"
    fi
    gate=""
    [[ -z "$verified_sha" ]] || gate=" sha256=$verified_sha"
    printf 'job=%s state=%s elapsed=%s pid=%s engine=%s target=%s%s\n' \
      "$job" "$state" "$(human_age "$age")" "$pid" "$engine" "$target" "$gate"
  done <<<"$ledger_dirs"
fi

printf '\nRECENT SCRATCH ACTIVITY (3h, newest first)\n'
recent_rows="$(find "$project_dir" -maxdepth 1 -type f \
  \( -name 'Grok*Scratch.lean' -o -name 'Sol*Scratch.lean' -o \
     -name 'Fable*Scratch.lean' \) \
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
