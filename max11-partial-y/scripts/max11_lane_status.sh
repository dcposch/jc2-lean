#!/usr/bin/env bash
# Concise local/remote dashboard for parallel Max-11 proof lanes.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
show_remote=1
show_all_waiters=0

while (($#)); do
  case "$1" in
    --local) show_remote=0 ;;
    --all) show_all_waiters=1 ;;
    *) echo "usage: $0 [--local] [--all]" >&2; exit 2 ;;
  esac
  shift
done

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
claude_workers=0
grok_workers=0
if [[ -z "$worker_rows" ]]; then
  printf 'none\n'
else
  while IFS= read -r row; do
    pid="$(awk '{print $1}' <<<"$row")"
    elapsed="$(awk '{print $2}' <<<"$row")"
    rss_kib="$(awk '{print $3}' <<<"$row")"
    engine="grok"
    [[ "$row" == *"claude "*" -p "* ]] && engine="claude"
    if [[ "$engine" == claude ]]; then
      claude_workers=$((claude_workers + 1))
    else
      grok_workers=$((grok_workers + 1))
    fi
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
claude_cap="${MAX11_CLAUDE_CAP:-9}"
grok_cap="${MAX11_GROK_CAP:-4}"
claude_launchable=$((claude_cap - claude_workers))
grok_launchable=$((grok_cap - grok_workers))
for engine in claude grok; do
  set +e
  engine_health="$($project_dir/scripts/max11_engine_health.sh --engine "$engine" 2>&1)"
  engine_health_exit=$?
  set -e
  if ((engine_health_exit == 75)); then
    if [[ "$engine" == claude ]]; then
      claude_launchable=0
      claude_health="$engine_health"
    else
      grok_launchable=0
      grok_health="$engine_health"
    fi
  elif ((engine_health_exit != 0)); then
    if [[ "$engine" == claude ]]; then
      claude_launchable=0
      claude_health="ENGINE=claude STATE=health_check_failed EXIT=$engine_health_exit"
    else
      grok_launchable=0
      grok_health="ENGINE=grok STATE=health_check_failed EXIT=$engine_health_exit"
    fi
  fi
done
printf 'capacity claude=%s/%s launchable=%s grok=%s/%s launchable=%s\n' \
  "$claude_workers" "$claude_cap" "$claude_launchable" \
  "$grok_workers" "$grok_cap" "$grok_launchable"
[[ -z "${claude_health:-}" ]] || printf '%s\n' "$claude_health"
[[ -z "${grok_health:-}" ]] || printf '%s\n' "$grok_health"

printf '\nMANAGED CAS JOBS\n'
cas_root="$project_dir/.max11-lanes/cas"
cas_dirs=""
if [[ -d "$cas_root" ]]; then
  cas_dirs="$(find "$cas_root" -mindepth 1 -maxdepth 1 -type d | sort -r | head -n 8)"
fi
cas_shown=0
if [[ -n "$cas_dirs" ]]; then
  while IFS= read -r cas_dir; do
    cas_state="$(sed -n '1p' "$cas_dir/state" 2>/dev/null || printf '?')"
    cas_pid="$(sed -n '1p' "$cas_dir/pid" 2>/dev/null || printf '?')"
    cas_name="$(sed -n '1p' "$cas_dir/name" 2>/dev/null || printf '?')"
    cas_started="$(sed -n '1p' "$cas_dir/started_epoch" 2>/dev/null || printf '%s' "$(date +%s)")"
    cas_ended="$(sed -n '1p' "$cas_dir/ended_epoch" 2>/dev/null || printf '%s' "$(date +%s)")"
    cas_timeout="$(sed -n '1p' "$cas_dir/timeout_seconds" 2>/dev/null || printf '?')"
    if [[ "$cas_state" == running && "$cas_pid" =~ ^[0-9]+$ ]] &&
        ! kill -0 "$cas_pid" 2>/dev/null; then
      cas_state="stale"
    fi
    [[ "$cas_started" =~ ^[0-9]+$ ]] || cas_started="$(date +%s)"
    [[ "$cas_ended" =~ ^[0-9]+$ ]] || cas_ended="$(date +%s)"
    if [[ "$cas_state" == running ]]; then
      cas_age=$(($(date +%s) - cas_started))
    else
      cas_age=$((cas_ended - cas_started))
    fi
    cas_resources=""
    if [[ -f "$cas_dir/resources.tsv" ]]; then
      cas_last="$(tail -n 1 "$cas_dir/resources.tsv")"
      cas_cpu="$(awk -F '\t' '{print $3}' <<<"$cas_last")"
      cas_rss="$(awk -F '\t' '{print $4}' <<<"$cas_last")"
      [[ "$cas_rss" =~ ^[0-9]+$ ]] &&
        cas_resources=" cpu=${cas_cpu}% rss_mib=$((cas_rss / 1024))"
    fi
    printf 'job=%s state=%s elapsed=%s timeout=%ss pid=%s%s\n' \
      "$cas_name" "$cas_state" "$(human_age "$cas_age")" "$cas_timeout" "$cas_pid" "$cas_resources"
    cas_shown=$((cas_shown + 1))
  done <<<"$cas_dirs"
fi
((cas_shown)) || printf 'none\n'

printf '\nUNMANAGED LONG CAS COMPUTE\n'
"$project_dir/scripts/max11_compute_guard.sh"

printf '\nACTIVE QUEUED FOLLOW-UPS\n'
wait_root="$project_dir/.max11-lanes/waits"
wait_dirs=""
if [[ -d "$wait_root" ]]; then
  wait_dirs="$(find "$wait_root" -mindepth 1 -maxdepth 1 -type d | sort -r)"
fi
waiter_shown=0
if [[ -n "$wait_dirs" ]]; then
  while IFS= read -r wait_dir; do
    state="$(sed -n '1p' "$wait_dir/state" 2>/dev/null || printf '?')"
    predecessor="$(sed -n '1p' "$wait_dir/predecessor" 2>/dev/null || printf '?')"
    engine="$(sed -n '1p' "$wait_dir/engine" 2>/dev/null || printf '?')"
    target="$(sed -n '1p' "$wait_dir/target" 2>/dev/null || printf '?')"
    pid="$(sed -n '1p' "$wait_dir/pid" 2>/dev/null || printf '?')"
    blocked_fingerprint="$(sed -n '1p' "$wait_dir/blocked_gate_fingerprint" 2>/dev/null || true)"
    if [[ "$state" == waiting_for_gate || "$state" == waiting_for_source_repair ||
          "$state" == recovering_predecessor_gate ||
          "$state" == waiting_for_capacity ]] &&
        [[ "$pid" =~ ^[0-9]+$ ]] && ! kill -0 "$pid" 2>/dev/null; then
      state="stale"
    fi
    if ((!show_all_waiters)); then
      case "$state" in
        queued|waiting_for_gate|waiting_for_source_repair|recovering_predecessor_gate|waiting_for_capacity|stale) ;;
        *) continue ;;
      esac
    fi
    blocked_detail=""
    [[ -z "$blocked_fingerprint" ]] || blocked_detail=" blocked_sha256=${blocked_fingerprint:0:12}"
    printf 'state=%s pid=%s engine=%s after=%s target=%s%s\n' \
      "$state" "$pid" "$engine" "$predecessor" "$target" "$blocked_detail"
    waiter_shown=$((waiter_shown + 1))
  done <<<"$wait_dirs"
fi
((waiter_shown)) || printf 'none\n'

printf '\nDURABLE VERIFICATION JOBS (active plus newest 12)\n'
verifier_root="$project_dir/.max11-lanes/verifiers"
verifier_dirs=""
if [[ -d "$verifier_root" ]]; then
  # A long-running verifier can be older than twelve newer, already-finished
  # jobs.  Always retain every active job in the dashboard, then append the
  # recent history without duplicating paths.
  verifier_dirs="$({
    for verifier_dir in "$verifier_root"/*; do
      [[ -d "$verifier_dir" ]] || continue
      verifier_state="$(sed -n '1p' "$verifier_dir/state" 2>/dev/null || true)"
      if [[ "$verifier_state" == queued || "$verifier_state" == running ]]; then
        printf '%s\n' "$verifier_dir"
      fi
    done
    find "$verifier_root" -mindepth 1 -maxdepth 1 -type d |
      sort -r | head -n 12
  } | awk '!seen[$0]++')"
fi
verifier_shown=0
if [[ -n "$verifier_dirs" ]]; then
  while IFS= read -r verifier_dir; do
    state="$(sed -n '1p' "$verifier_dir/state" 2>/dev/null || printf '?')"
    target="$(sed -n '1p' "$verifier_dir/target" 2>/dev/null || printf '?')"
    pid="$(sed -n '1p' "$verifier_dir/pid" 2>/dev/null || printf '?')"
    started="$(sed -n '1p' "$verifier_dir/started_epoch" 2>/dev/null || printf '%s' "$(date +%s)")"
    ended="$(sed -n '1p' "$verifier_dir/ended_epoch" 2>/dev/null || printf '%s' "$(date +%s)")"
    if [[ "$state" == running && "$pid" =~ ^[0-9]+$ ]] &&
        ! kill -0 "$pid" 2>/dev/null; then
      state="stale"
    fi
    [[ "$started" =~ ^[0-9]+$ ]] || started="$(date +%s)"
    [[ "$ended" =~ ^[0-9]+$ ]] || ended="$(date +%s)"
    if [[ "$state" == queued || "$state" == running ]]; then
      age=$(($(date +%s) - started))
    else
      age=$((ended - started))
    fi
    verified_sha="$(sed -n '1p' "$verifier_dir/verified_sha256" 2>/dev/null || true)"
    gate_detail=""
    [[ -z "$verified_sha" ]] || gate_detail=" sha256=$verified_sha"
    if [[ "$state" == failed && -s "$verifier_dir/handoff.txt" ]]; then
      first_error="$(sed -n 's/^FIRST_ERROR=//p' \
        "$verifier_dir/handoff.txt" | head -n 1 | cut -c 1-180)"
      [[ -z "$first_error" ]] || gate_detail=" error=$first_error"
    fi
    printf 'job=%s state=%s elapsed=%s pid=%s target=%s%s\n' \
      "${verifier_dir##*/}" "$state" "$(human_age "$age")" "$pid" \
      "$target" "$gate_detail"
    verifier_shown=$((verifier_shown + 1))
  done <<<"$verifier_dirs"
fi
((verifier_shown)) || printf 'none\n'

printf '\nDURABLE GATE CHAINS (active plus newest 6)\n'
chain_root="$project_dir/.max11-lanes/gate-chains"
chain_dirs=""
if [[ -d "$chain_root" ]]; then
  chain_dirs="$({
    for chain_dir in "$chain_root"/*; do
      [[ -d "$chain_dir" ]] || continue
      chain_state="$(sed -n '1p' "$chain_dir/state" 2>/dev/null || true)"
      if [[ "$chain_state" == queued || "$chain_state" == starting ||
            "$chain_state" == waiting_for_predecessor ||
            "$chain_state" == launching_gate ||
            "$chain_state" == waiting_for_gate ]]; then
        printf '%s\n' "$chain_dir"
      fi
    done
    find "$chain_root" -mindepth 1 -maxdepth 1 -type d |
      sort -r | head -n 6
  } | awk '!seen[$0]++')"
fi
chain_shown=0
if [[ -n "$chain_dirs" ]]; then
  while IFS= read -r chain_dir; do
    state="$(sed -n '1p' "$chain_dir/state" 2>/dev/null || printf '?')"
    pid="$(sed -n '1p' "$chain_dir/pid" 2>/dev/null || printf '?')"
    current="$(sed -n '1p' "$chain_dir/current_target" 2>/dev/null || true)"
    predecessor="$(sed -n '1p' "$chain_dir/predecessor" 2>/dev/null || true)"
    completed_count=0
    target_count=0
    [[ ! -f "$chain_dir/results.tsv" ]] ||
      completed_count="$(wc -l <"$chain_dir/results.tsv" | tr -d '[:space:]')"
    [[ ! -f "$chain_dir/targets" ]] ||
      target_count="$(wc -l <"$chain_dir/targets" | tr -d '[:space:]')"
    case "$state" in
      queued|starting|waiting_for_predecessor|launching_gate|waiting_for_gate)
        if [[ "$pid" =~ ^[0-9]+$ ]] && ! kill -0 "$pid" 2>/dev/null; then
          state="stale"
        fi
        ;;
    esac
    detail=""
    [[ -z "$current" ]] || detail=" current=$current"
    [[ -z "$predecessor" ]] || detail="$detail after=$predecessor"
    printf 'job=%s state=%s pid=%s progress=%s/%s%s\n' \
      "${chain_dir##*/}" "$state" "$pid" "$completed_count" \
      "$target_count" "$detail"
    chain_shown=$((chain_shown + 1))
  done <<<"$chain_dirs"
fi
((chain_shown)) || printf 'none\n'

printf '\nDURABLE GATE BATCHES (active plus newest 6)\n'
batch_root="$project_dir/.max11-lanes/gate-batches"
batch_dirs=""
if [[ -d "$batch_root" ]]; then
  batch_dirs="$({
    for batch_dir in "$batch_root"/*; do
      [[ -d "$batch_dir" ]] || continue
      batch_state="$(sed -n '1p' "$batch_dir/state" 2>/dev/null || true)"
      if [[ "$batch_state" == queued || "$batch_state" == running ]]; then
        printf '%s\n' "$batch_dir"
      fi
    done
    find "$batch_root" -mindepth 1 -maxdepth 1 -type d |
      sort -r | head -n 6
  } | awk '!seen[$0]++')"
fi
batch_shown=0
if [[ -n "$batch_dirs" ]]; then
  while IFS= read -r batch_dir; do
    state="$(sed -n '1p' "$batch_dir/state" 2>/dev/null || printf '?')"
    pid="$(sed -n '1p' "$batch_dir/pid" 2>/dev/null || printf '?')"
    target_count=0
    [[ ! -f "$batch_dir/targets" ]] ||
      target_count="$(wc -l <"$batch_dir/targets" | tr -d '[:space:]')"
    progress="$(sed -n '1p' "$batch_dir/progress" 2>/dev/null || true)"
    if [[ "$state" == queued || "$state" == running ]]; then
      if [[ "$pid" =~ ^[0-9]+$ ]] && ! kill -0 "$pid" 2>/dev/null; then
        state="stale"
      fi
    fi
    detail=""
    [[ -z "$progress" ]] || detail=" $progress"
    printf 'job=%s state=%s pid=%s targets=%s%s\n' \
      "${batch_dir##*/}" "$state" "$pid" "$target_count" "$detail"
    batch_shown=$((batch_shown + 1))
  done <<<"$batch_dirs"
fi
((batch_shown)) || printf 'none\n'

if ((!show_all_waiters)) && [[ -n "$wait_dirs" ]]; then
  printf '\nFOLLOW-UP HISTORY SUMMARY\n'
  for summary_state in launched canceled failed launch_failed; do
    summary_count=0
    while IFS= read -r wait_dir; do
      [[ "$(sed -n '1p' "$wait_dir/state" 2>/dev/null || true)" == "$summary_state" ]] &&
        summary_count=$((summary_count + 1))
    done <<<"$wait_dirs"
    printf '%s=%s%s' "$summary_state" "$summary_count" \
      "$([[ "$summary_state" == launch_failed ]] && printf '\n' || printf ' ')"
  done
fi

now="$(date +%s)"
printf '\nDURABLE LANE LEDGER (newest 12)\n'
state_root="$project_dir/.max11-lanes"
ledger_dirs=""
if [[ -d "$state_root" ]]; then
  ledger_dirs="$(find "$state_root" -mindepth 1 -maxdepth 1 -type d \
    ! -name gates ! -name waits ! -name cas ! -name verifiers \
    ! -name gate-chains ! -name gate-batches |
    sort -r | head -n 12)"
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
  printf '\nACTIVE REMOTE GATE PHASES\n'
  "$project_dir/scripts/max11_gate_phases.sh"
  printf '\n'
  "$project_dir/scripts/box_lean_status.sh"
fi
