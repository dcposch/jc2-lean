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
guard_dir="$project_dir/scripts/no-local-lean"
state_root="$project_dir/.max11-lanes"

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
  echo "LANE_CHECK=ok CLAUDE=$(claude --version | head -n 1) GROK=$(grok --version | head -n 1)"
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
printf '%s\n' "$$" >"$job_dir/pid"
printf '%s\n' "$(date +%s)" >"$job_dir/started_epoch"
printf '%s\n' running >"$job_dir/state"
printf 'JOB=%s PID=%s ENGINE=%s TARGET=%s LOG=%s\n' \
  "$job_id" "$$" "$engine" "$target" "$job_dir/output.log"

finish_lane() {
  exit_code=$?
  printf '%s\n' "$exit_code" >"$job_dir/exit_code"
  printf '%s\n' "$(date +%s)" >"$job_dir/ended_epoch"
  if ((exit_code == 0)); then
    printf '%s\n' succeeded >"$job_dir/state"
  else
    printf '%s\n' failed >"$job_dir/state"
  fi
}
trap finish_lane EXIT

contract="Work autonomously in $project_dir. Create only the untracked target $target. No tracked/helper edits, sorry, new axioms, finite-root shortcuts, or closure overclaims. Do not invoke local Lean or Lake; the guarded PATH intentionally disables them. Use ./scripts/box_lean_verify.sh --file $target for every Lean compilation/check. Finish only after literal BUILD_EXIT=0 ERROR_COUNT=0 SORRYAX_COUNT=0, and report recursive SHA-256 hashes, exact gain, next unused row, and residual. LOCAL_LEAN_GUARD=enabled."
set +e
if [[ "$engine" == claude ]]; then
  env PATH="$guard_dir:$PATH" LOCAL_LEAN_GUARD=enabled \
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
exit "$exit_code"
