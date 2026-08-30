#!/usr/bin/env bash
# Find verifier workers whose local owner vanished but whose isolated AWS
# workspace (and often Lean itself) survived.  Dry-run by default.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
verifier_root="$project_dir/.max11-lanes/verifiers"
box_host="${BOX_LEAN_HOST:-ubuntu@54.81.66.156}"
box_key="${BOX_LEAN_KEY:-/Users/dc/.ssh/claude-cli.pem}"
box_dir="${BOX_LEAN_DIR:-/home/ubuntu/jc2-lean/max11-partial-y}"
box_control_path="${BOX_LEAN_SSH_CONTROL_PATH:-/tmp/box-lean-ssh-%C}"
remote_parent="${box_dir%/*}"
apply=0

usage() {
  echo "usage: $0 [--apply]" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --apply) apply=1 ;;
    *) usage ;;
  esac
  shift
done

[[ -r "$box_key" ]] || {
  echo "missing SSH key: $box_key" >&2
  exit 2
}

ssh_args=(-i "$box_key" -o BatchMode=yes -o StrictHostKeyChecking=no
  -o ControlMaster=auto -o ControlPersist=600 -o "ControlPath=$box_control_path")
records_file="$(mktemp -t max11-stale-gates.XXXXXX)"
remote_result="$(mktemp -t max11-stale-gates-remote.XXXXXX)"
trap 'rm -f -- "$records_file" "$remote_result"' EXIT

worker_owned_by_job() {
  local pid="$1" job_dir="$2" command
  [[ "$pid" =~ ^[0-9]+$ ]] && kill -0 "$pid" 2>/dev/null || return 1
  command="$(ps -o command= -p "$pid" 2>/dev/null || true)"
  [[ "$command" == *" --run $job_dir "* ||
     "$command" == *" --run $job_dir" ]]
}

local_candidates=0
if [[ -d "$verifier_root" ]]; then
  for job_dir in "$verifier_root"/*; do
    [[ -d "$job_dir" && -f "$job_dir/state" && -f "$job_dir/target" ]] || continue
    state="$(sed -n '1p' "$job_dir/state" 2>/dev/null || true)"
    target="$(sed -n '1p' "$job_dir/target" 2>/dev/null || true)"
    pid="$(sed -n '1p' "$job_dir/pid" 2>/dev/null || true)"
    [[ "$target" =~ ^[A-Za-z0-9_.-]+Scratch[.]lean$ &&
        "$target" == "${target##*/}" ]] || continue

    own_worker=0
    worker_owned_by_job "$pid" "$job_dir" && own_worker=1
    # A validated local owner may be in the short state-write/EXIT-cleanup
    # window.  It is not stale; let its verifier trap finish normally.
    ((own_worker == 0)) || continue
    case "$state" in
      queued|running)
        # A reused PID is deliberately not trusted: only the command tied to
        # this immutable ledger counts as a live owner.
        ;;
      *) ;;
    esac

    sync_destination="$(sed -nE 's#^SYNC .+ -> ([^ ]+)$#\1#p' \
      "$job_dir/output.log" 2>/dev/null | tail -n 1)"
    [[ -n "$sync_destination" ]] || {
      # A dead worker can disappear during local preflight, before allocating
      # any remote workspace.  Still surface an active stale ledger below.
      case "$state" in
        queued|running)
          printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
            "${job_dir##*/}" "$target" "$state" "$pid" "$own_worker" "-" \
            >>"$records_file"
          local_candidates=$((local_candidates + 1))
          ;;
      esac
      continue
    }
    sync_host="${sync_destination%%:*}"
    remote_work_dir="${sync_destination#*:}"
    remote_suffix="${remote_work_dir#"$remote_parent/box-lean-verify."}"
    [[ "$sync_host" == "$box_host" &&
        "$remote_work_dir" == "$remote_parent/box-lean-verify.$remote_suffix" &&
        "$remote_suffix" =~ ^[A-Za-z0-9]+$ ]] || {
      echo "SKIP job=${job_dir##*/} reason=unvalidated_remote_destination destination=$sync_destination" >&2
      continue
    }
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
      "${job_dir##*/}" "$target" "$state" "$pid" "$own_worker" \
      "$remote_work_dir" >>"$records_file"
    local_candidates=$((local_candidates + 1))
  done
fi

if ((local_candidates == 0)); then
  echo "STALE_GATE_SUMMARY candidates=0 remote_found=0 reaped=0 apply=$apply"
  exit 0
fi

# Send all candidates over one SSH connection.  The remote side acts only on
# validated mktemp workspaces below the dedicated box directory and kills
# processes by their exact cwd, never by executable name or user.
{
  printf '%s\n' 'set -euo pipefail'
  cat <<'REMOTE_HELPER'
remote_parent="$1"
apply="$2"
remote_found=0
reaped=0
while IFS=$'\t' read -r job target state pid own_worker remote_work_dir; do
  [[ "$remote_work_dir" != "-" ]] || continue
  remote_suffix="${remote_work_dir#"$remote_parent/box-lean-verify."}"
  [[ "$remote_work_dir" == "$remote_parent/box-lean-verify.$remote_suffix" &&
      "$remote_suffix" =~ ^[A-Za-z0-9]+$ ]] || {
    printf 'REMOTE_SKIP job=%s reason=unsafe_workspace path=%s\n' \
      "$job" "$remote_work_dir" >&2
    continue
  }
  [[ -d "$remote_work_dir" ]] || continue
  process_count=0
  for proc in /proc/[0-9]*; do
    cwd="$(readlink "$proc/cwd" 2>/dev/null || true)"
    case "$cwd" in
      "$remote_work_dir"|"$remote_work_dir"/*)
        process_count=$((process_count + 1))
        ;;
    esac
  done
  remote_found=$((remote_found + 1))
  if ((apply == 0)); then
    printf 'STALE_GATE job=%s target=%s state=%s pid=%s workspace=%s remote_processes=%s\n' \
      "$job" "$target" "$state" "$pid" "$remote_work_dir" "$process_count"
    continue
  fi
  for signal in TERM KILL; do
    for proc in /proc/[0-9]*; do
      cwd="$(readlink "$proc/cwd" 2>/dev/null || true)"
      case "$cwd" in
        "$remote_work_dir"|"$remote_work_dir"/*)
          kill -"$signal" "${proc##*/}" 2>/dev/null || true
          ;;
      esac
    done
    [[ "$signal" == TERM ]] && sleep 1
  done
  rm -rf -- "$remote_work_dir"
  [[ ! -e "$remote_work_dir" ]] || {
    printf 'REMOTE_SKIP job=%s reason=workspace_survived path=%s\n' \
      "$job" "$remote_work_dir" >&2
    continue
  }
  printf 'REAPED_STALE_GATE job=%s target=%s prior_state=%s workspace=%s remote_processes=%s\n' \
    "$job" "$target" "$state" "$remote_work_dir" "$process_count"
  reaped=$((reaped + 1))
done <<'REMOTE_RECORDS'
REMOTE_HELPER
  cat "$records_file"
  cat <<'REMOTE_TAIL'
REMOTE_RECORDS
printf 'REMOTE_STALE_GATE_SUMMARY remote_found=%s reaped=%s apply=%s\n' \
  "$remote_found" "$reaped" "$apply"
REMOTE_TAIL
} | ssh "${ssh_args[@]}" "$box_host" /bin/bash -s -- \
    "$remote_parent" "$apply" >"$remote_result"
cat "$remote_result"

# A vanished local owner cannot ever complete its durable handoff.  Mark an
# active stale ledger terminal so gate chains fail promptly instead of waiting
# forever, even if it died before remote workspace allocation.
active_stale=0
if ((apply)); then
  while IFS=$'\t' read -r job target state pid own_worker remote_work_dir; do
    case "$state" in queued|running) ;; *) continue ;; esac
    job_dir="$verifier_root/$job"
    current_state="$(sed -n '1p' "$job_dir/state" 2>/dev/null || true)"
    case "$current_state" in queued|running) ;; *) continue ;; esac
    printf '%s\n' failed_stale_worker >"$job_dir/state"
    printf '%s\n' "$(date +%s)" >"$job_dir/ended_epoch"
    {
      printf 'HANDOFF_VERSION=1\nRESULT=failed\nTARGET=%s\n' "$target"
      printf 'REASON=local_verifier_owner_vanished\n'
    } >"$job_dir/handoff.txt"
    active_stale=$((active_stale + 1))
  done <"$records_file"
fi

remote_found="$(sed -nE \
  's/^REMOTE_STALE_GATE_SUMMARY remote_found=([0-9]+).*/\1/p' \
  "$remote_result" | tail -n 1)"
reaped="$(sed -nE \
  's/^REMOTE_STALE_GATE_SUMMARY .* reaped=([0-9]+).*/\1/p' \
  "$remote_result" | tail -n 1)"
printf 'STALE_GATE_SUMMARY candidates=%s remote_found=%s reaped=%s active_marked_failed=%s apply=%s\n' \
  "$local_candidates" "${remote_found:-0}" "${reaped:-0}" "$active_stale" "$apply"
