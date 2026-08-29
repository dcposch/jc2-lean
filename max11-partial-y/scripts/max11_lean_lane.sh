#!/usr/bin/env bash
# Launch a durable, guarded Max-11 CLI proof lane.
set -euo pipefail

usage() {
  cat >&2 <<'EOF'
usage: max11_lean_lane.sh --engine claude|grok --target FILE.lean -- INSTRUCTION...
       max11_lean_lane.sh --check
EOF
  exit 2
}

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
script_path="$project_dir/scripts/max11_lean_lane.sh"
guard_dir="$project_dir/scripts/no-local-lean"
state_root="$project_dir/.max11-lanes"

if [[ "${1:-}" == "--run" ]]; then
  (($# == 5)) || usage
  job_dir="$2"
  engine="$3"
  target="$4"
  instruction="$5"
  case "$job_dir" in
    "$state_root"/*) ;;
    *) echo "unsafe lane state directory: $job_dir" >&2; exit 2 ;;
  esac
  printf '%s\n' "$$" >"$job_dir/pid"
  printf '%s\n' "$(date +%s)" >"$job_dir/started_epoch"
  printf '%s\n' running >"$job_dir/state"

  finish_lane() {
    exit_code=$?
    printf '%s\n' "$exit_code" >"$job_dir/exit_code"
    printf '%s\n' "$(date +%s)" >"$job_dir/ended_epoch"
    current_state="$(sed -n '1p' "$job_dir/state" 2>/dev/null || true)"
    if [[ "$current_state" == running || "$current_state" == queued || \
          "$current_state" == verifying ]]; then
      if ((exit_code == 0)); then
        printf '%s\n' succeeded >"$job_dir/state"
      else
        printf '%s\n' failed >"$job_dir/state"
      fi
    fi
  }
  trap finish_lane EXIT

  contract="Work autonomously in $project_dir. Create only the untracked target $target. No tracked/helper edits, sorry, new axioms, finite-root shortcuts, or closure overclaims. Do not invoke local Lean or Lake; the guarded PATH intentionally disables them. Use ./scripts/box_lean_verify.sh --file $target for every Lean compilation/check. Finish only after literal BUILD_EXIT=0 ERROR_COUNT=0 SORRYAX_COUNT=0, and report recursive SHA-256 hashes, exact gain, next unused row, and residual. LOCAL_LEAN_GUARD=enabled."
  set +e
  if [[ "$engine" == claude ]]; then
    # This machine uses the Claude login.  A stale API-key override can mask
    # that working credential and fail every detached worker with HTTP 401.
    env -u ANTHROPIC_API_KEY PATH="$guard_dir:$PATH" LOCAL_LEAN_GUARD=enabled \
      claude --dangerously-skip-permissions -p "$instruction $contract" \
      2>&1 | tee "$job_dir/output.log"
    exit_code=${PIPESTATUS[0]}
  else
    env PATH="$guard_dir:$PATH" LOCAL_LEAN_GUARD=enabled \
      grok --yolo --output-format plain -p "$instruction $contract" \
      2>&1 | tee "$job_dir/output.log"
    exit_code=${PIPESTATUS[0]}
  fi
  set -e
  if ((exit_code != 0)); then
    exit "$exit_code"
  fi

  if [[ ! -f "$project_dir/$target" ]]; then
    echo "worker exited successfully without creating $target" | tee "$job_dir/verify.log" >&2
    printf '%s\n' verification_failed >"$job_dir/state"
    exit 66
  fi

  # Convert a model-process success into a proof success.  If the worker's own
  # AWS check already produced an exact content/environment receipt, this is
  # instant.  Otherwise perform the independent gate here.  Waiting on the
  # per-target lock also handles CLIs that return before an async tool call.
  printf '%s\n' verifying >"$job_dir/state"
  : >"$job_dir/verify.log"
  if "$project_dir/scripts/box_lean_verify.sh" --file "$target" --receipt-only \
      >>"$job_dir/verify.log" 2>&1; then
    verify_exit=0
  else
    set +e
    "$project_dir/scripts/box_lean_verify.sh" --file "$target" --wait-lock 900 \
      >>"$job_dir/verify.log" 2>&1
    verify_exit=$?
    set -e
  fi
  if ((verify_exit != 0)); then
    printf '%s\n' verification_failed >"$job_dir/state"
    tail -n 30 "$job_dir/verify.log"
    exit "$verify_exit"
  fi
  LC_ALL=C shasum -a 256 "$project_dir/$target" | awk '{print $1}' \
    >"$job_dir/verified_sha256"
  printf '%s\n' "$(date +%s)" >"$job_dir/verified_epoch"
  printf '%s\n' verified >"$job_dir/state"
  tail -n 10 "$job_dir/verify.log"
  exit 0
fi

if [[ "${1:-}" == "--check" && $# == 1 ]]; then
  [[ -x "$guard_dir/lake" && -x "$guard_dir/lean" ]] || {
    echo "missing local Lean guards in $guard_dir" >&2
    exit 69
  }
  command -v claude >/dev/null || {
    echo "claude is not available" >&2
    exit 69
  }
  command -v grok >/dev/null || {
    echo "grok is not available" >&2
    exit 69
  }
  command -v screen >/dev/null || {
    echo "screen is not available" >&2
    exit 69
  }
  # GNU Screen reports its version but exits 1 on this macOS build.
  screen_version="$(screen --version 2>&1 || true)"
  screen_version="${screen_version%%$'\n'*}"
  screen_version="${screen_version//$'\r'/}"
  echo "LANE_CHECK=ok SCREEN=$screen_version CLAUDE=$(claude --version | head -n 1) GROK=$(grok --version | head -n 1)"
  exit 0
fi

engine=""
target=""
while (($#)); do
  case "$1" in
    --engine)
      shift
      (($#)) || usage
      engine="$1"
      ;;
    --target)
      shift
      (($#)) || usage
      target="$1"
      ;;
    --)
      shift
      break
      ;;
    *) usage ;;
  esac
  shift
done
(($#)) || usage
instruction="$*"

[[ "$engine" == claude || "$engine" == grok ]] || usage
if [[ "$engine" == claude ]]; then
  [[ "$target" =~ ^Fable[A-Za-z0-9_.-]*Scratch\.lean$ ]] || {
    echo "invalid Claude/Fable scratch target: $target" >&2
    exit 2
  }
  engine_cap="${MAX11_CLAUDE_CAP:-6}"
else
  [[ "$target" =~ ^Grok[A-Za-z0-9_.-]*Scratch\.lean$ ]] || {
    echo "invalid Grok scratch target: $target" >&2
    exit 2
  }
  engine_cap="${MAX11_GROK_CAP:-4}"
fi
[[ "$target" == "${target##*/}" ]] || usage
[[ "$engine_cap" =~ ^[1-9][0-9]*$ ]] || {
  echo "invalid worker cap: $engine_cap" >&2
  exit 2
}

if git -C "$project_dir" ls-files --error-unmatch -- "$target" >/dev/null 2>&1; then
  echo "refusing tracked target: $target" >&2
  exit 65
fi
[[ -x "$guard_dir/lake" && -x "$guard_dir/lean" ]] || {
  echo "missing local Lean guards in $guard_dir" >&2
  exit 69
}
command -v "$engine" >/dev/null || {
  echo "$engine is not available" >&2
  exit 69
}
command -v screen >/dev/null || {
  echo "screen is not available" >&2
  exit 69
}

worker_rows="$(ps -axo pid=,comm=,args= | awk -v project="$project_dir" -v engine="$engine" '
  $2 == engine &&
    ((engine == "grok" && index($0, "--yolo")) ||
     (engine == "claude" && index($0, " -p "))) &&
    (index($0, project) || index($0, "LOCAL_LEAN_GUARD=enabled")) {print}')"
worker_count=0
if [[ -n "$worker_rows" ]]; then
  worker_count="$(wc -l <<<"$worker_rows" | tr -d ' ')"
  if grep -Fq "$target" <<<"$worker_rows"; then
    echo "a managed worker already mentions target: $target" >&2
    exit 75
  fi
fi
if ((worker_count >= engine_cap)); then
  echo "managed $engine worker cap reached: $worker_count/$engine_cap" >&2
  exit 75
fi

mkdir -p "$state_root"
job_id="$(date -u +%Y%m%dT%H%M%SZ)-${target%.lean}-$RANDOM"
job_dir="$state_root/$job_id"
mkdir "$job_dir"
printf '%s\n' "$engine" >"$job_dir/engine"
printf '%s\n' "$target" >"$job_dir/target"
printf '%s\n' "$instruction" >"$job_dir/instruction"
printf '%s\n' queued >"$job_dir/state"
screen_name="max11-${engine}-${RANDOM}-$$"
printf '%s\n' "$screen_name" >"$job_dir/screen_session"
screen -dmS "$screen_name" "$script_path" --run \
  "$job_dir" "$engine" "$target" "$instruction"

# The detached runner records its own PID.  Wait briefly so the launch receipt
# and dashboard do not report an avoidable unknown PID.
for _ in {1..20}; do
  [[ -s "$job_dir/pid" ]] && break
  sleep 0.05
done
pid="$(sed -n '1p' "$job_dir/pid" 2>/dev/null || printf '?')"
printf 'JOB=%s PID=%s SCREEN=%s ENGINE=%s TARGET=%s LOG=%s\n' \
  "$job_id" "$pid" "$screen_name" "$engine" "$target" "$job_dir/output.log"
