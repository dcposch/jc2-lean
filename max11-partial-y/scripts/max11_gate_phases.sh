#!/usr/bin/env bash
# Map each active durable gate to its exact phase on the dedicated Lean box.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
verifier_root="$project_dir/.max11-lanes/verifiers"
box_host="${BOX_LEAN_HOST:-ubuntu@54.81.66.156}"
box_key="${BOX_LEAN_KEY:-/Users/dc/.ssh/claude-cli.pem}"
box_dir="${BOX_LEAN_DIR:-/home/ubuntu/jc2-lean/max11-partial-y}"
box_control_path="${BOX_LEAN_SSH_CONTROL_PATH:-/tmp/box-lean-ssh-%C}"
ssh_args=(-i "$box_key" -o BatchMode=yes -o StrictHostKeyChecking=no
  -o ControlMaster=auto -o ControlPersist=600 -o "ControlPath=$box_control_path")

[[ -r "$box_key" ]] || {
  echo "missing SSH key: $box_key" >&2
  exit 2
}

records_file="$(mktemp -t max11-gate-phases.XXXXXX)"
trap 'rm -f -- "$records_file"' EXIT

if [[ -d "$verifier_root" ]]; then
  for job_dir in "$verifier_root"/*; do
    [[ -d "$job_dir" ]] || continue
    state="$(sed -n '1p' "$job_dir/state" 2>/dev/null || true)"
    case "$state" in queued|running) ;; *) continue ;; esac
    target="$(sed -n '1p' "$job_dir/target" 2>/dev/null || true)"
    started="$(sed -n '1p' "$job_dir/started_epoch" 2>/dev/null || true)"
    workspace="$(sed -nE 's#^SYNC .+ -> [^:]+:(/[^ ]+)$#\1#p' \
      "$job_dir/output.log" 2>/dev/null | tail -n 1)"
    [[ "$target" =~ ^[A-Za-z0-9_.-]+Scratch[.]lean$ ]] || target="?"
    [[ "$started" =~ ^[0-9]+$ ]] || started=0
    if [[ -z "$workspace" ]]; then
      workspace="-"
    else
      remote_parent="${box_dir%/*}"
      suffix="${workspace#"$remote_parent/box-lean-verify."}"
      if [[ "$workspace" != "$remote_parent/box-lean-verify.$suffix" ||
            ! "$suffix" =~ ^[A-Za-z0-9]+$ ]]; then
        workspace="invalid"
      fi
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' \
      "${job_dir##*/}" "$target" "$state" "$started" "$workspace" \
      >>"$records_file"
  done
fi

if [[ ! -s "$records_file" ]]; then
  echo "ACTIVE_GATE_PHASES none"
  exit 0
fi

{
  cat <<'REMOTE_SCRIPT'
set -euo pipefail
box_dir="$1"
now="$(date +%s)"

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

while IFS=$'\t' read -r job target state started workspace; do
  age=0
  ((started > 0 && now >= started)) && age=$((now - started))
  detail=""
  phase="remote_setup"
  case "$workspace" in
    -)
      phase="local_preflight_or_sync"
      ;;
    invalid)
      phase="invalid_workspace"
      ;;
    *)
      remote_parent="${box_dir%/*}"
      suffix="${workspace#"$remote_parent/box-lean-verify."}"
      if [[ "$workspace" != "$remote_parent/box-lean-verify.$suffix" ||
            ! "$suffix" =~ ^[A-Za-z0-9]+$ ]]; then
        phase="invalid_workspace"
      elif [[ ! -d "$workspace" ]]; then
        phase="remote_finished_local_handoff"
      else
        lean_row=""
        flock_row=""
        shell_count=0
        for proc in /proc/[0-9]*; do
          pid="${proc##*/}"
          cwd="$(readlink -f "$proc/cwd" 2>/dev/null || true)"
          case "$cwd" in "$workspace"|"$workspace"/*) ;; *) continue ;; esac
          command="$(tr '\0' ' ' <"$proc/cmdline" 2>/dev/null || true)"
          [[ -n "$command" ]] || continue
          comm="$(sed -n '1p' "$proc/comm" 2>/dev/null || true)"
          if [[ "$comm" == lean ]]; then
            row="$(ps -p "$pid" -o etimes=,pcpu=,rss= 2>/dev/null || true)"
            [[ -n "$row" ]] && lean_row="$pid $row $command"
          elif [[ "$comm" == flock ]]; then
            flock_row="$pid $command"
          elif [[ "$comm" == bash || "$comm" == sh ]]; then
            shell_count=$((shell_count + 1))
          fi
        done
        if [[ -n "$lean_row" ]]; then
          read -r lean_pid lean_elapsed lean_cpu lean_rss _ <<<"$lean_row"
          lean_source="$(grep -oE '[A-Za-z0-9_.-]+[.]lean' <<<"$lean_row" | tail -n 1 || true)"
          phase="compiling"
          detail=" source=${lean_source:-?} lean_pid=$lean_pid compile_age=$(human_age "$lean_elapsed") cpu=${lean_cpu}% rss_mib=$((lean_rss / 1024))"
        elif [[ -n "$flock_row" ]]; then
          cache_key="$(grep -oE '[0-9a-f]{64}[.]olean[.]lock' <<<"$flock_row" | head -n 1 || true)"
          phase="waiting_for_dependency_cache"
          detail=" cache_key=${cache_key%.olean.lock}"
        elif ((shell_count > 0)); then
          phase="remote_setup_or_finishing"
          detail=" shell_processes=$shell_count"
        else
          phase="remote_idle_or_finishing"
        fi
      fi
      ;;
  esac
  printf 'job=%s state=%s age=%s target=%s phase=%s%s\n' \
    "$job" "$state" "$(human_age "$age")" "$target" "$phase" "$detail"
done
REMOTE_SCRIPT
  cat "$records_file"
} | ssh "${ssh_args[@]}" "$box_host" /bin/bash -s -- "$box_dir"
