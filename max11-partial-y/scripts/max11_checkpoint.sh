#!/usr/bin/env bash
# Compact, source-exact checkpoint for one Max-11 scratch lane.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"

usage() {
  echo "usage: $0 FILE.lean" >&2
  exit 2
}

[[ $# -eq 1 ]] || usage
target="$1"
[[ "$target" =~ ^[A-Za-z0-9_.-]+Scratch[.]lean$ &&
    "$target" == "${target##*/}" && -f "$project_dir/$target" ]] || usage

source_sha="$(openssl dgst -sha256 -r "$project_dir/$target")"
source_sha="${source_sha%% *}"
printf 'TARGET=%s\nSOURCE_SHA256=%s\n' "$target" "$source_sha"

# One receipt query checks the target against its complete recursive scratch
# closure and tracked environment, but report only the facts needed at a lane
# boundary instead of echoing the often very large verifier manifest.
receipt_log="$(mktemp -t max11-checkpoint-receipt.XXXXXX)"
imports_log="$(mktemp -t max11-checkpoint-imports.XXXXXX)"
trap 'rm -f -- "$receipt_log" "$imports_log"' EXIT
set +e
"$project_dir/scripts/box_lean_verify.sh" --file "$target" --receipt-only \
  >"$receipt_log" 2>&1
receipt_exit=$?
set -e
if ((receipt_exit == 0)); then
  receipt_fingerprint="$(sed -nE \
    's/^GATE_RECEIPT_SHA256=([0-9a-f]{64})$/\1/p' \
    "$receipt_log" | tail -n 1)"
  verified_sha="$(sed -nE \
    "s/^VERIFIED_SHA256=([0-9a-f]{64}) FILE=${target//./[.]}$/\\1/p" \
    "$receipt_log" | tail -n 1)"
  printf 'RECEIPT=verified GATE_FINGERPRINT=%s VERIFIED_SHA256=%s\n' \
    "${receipt_fingerprint:-unknown}" "${verified_sha:-unknown}"
else
  missing_fingerprint="$(sed -nE \
    's/^GATE_RECEIPT_MISSING SHA256=([0-9a-f]{64})$/\1/p' \
    "$receipt_log" | tail -n 1)"
  printf 'RECEIPT=missing GATE_FINGERPRINT=%s\n' \
    "${missing_fingerprint:-unknown}"
fi

printf 'DIRECT_SCRATCH_IMPORTS\n'
set +e
"$project_dir/scripts/max11_verified_imports.sh" "$target" \
  >"$imports_log" 2>&1
imports_exit=$?
set -e
sed -nE \
  '/^(VERIFIED_IMPORT|UNVERIFIED_IMPORT|VERIFIED_IMPORTS_OK|Refusing )/p' \
  "$imports_log"
printf 'DIRECT_IMPORT_GATE=%s\n' \
  "$([[ $imports_exit -eq 0 ]] && printf ready || printf blocked)"

latest_job=""
verifier_root="$project_dir/.max11-lanes/verifiers"
if [[ -d "$verifier_root" ]]; then
  for job_dir in "$verifier_root"/*; do
    [[ -d "$job_dir" ]] || continue
    [[ "$(sed -n '1p' "$job_dir/target" 2>/dev/null || true)" == "$target" ]] || continue
    if [[ -z "$latest_job" || "${job_dir##*/}" > "${latest_job##*/}" ]]; then
      latest_job="$job_dir"
    fi
  done
fi
if [[ -n "$latest_job" ]]; then
  job_state="$(sed -n '1p' "$latest_job/state" 2>/dev/null || printf '?')"
  job_pid="$(sed -n '1p' "$latest_job/pid" 2>/dev/null || printf '?')"
  printf 'LATEST_GATE_JOB=%s STATE=%s PID=%s\n' \
    "${latest_job##*/}" "$job_state" "$job_pid"
  first_error="$(grep -m 1 -E \
    '^[^[:space:]]+[.]lean:[0-9]+:[0-9]+: error:|^[^[:space:]]+[.]lean:[0-9]+:[0-9]+: error\(|^LEAN_COMPILE_TIMEOUT ' \
    "$latest_job/output.log" 2>/dev/null || true)"
  [[ -z "$first_error" ]] || printf 'LATEST_GATE_ERROR=%.400s\n' "$first_error"
else
  printf 'LATEST_GATE_JOB=none\n'
fi

printf 'RECENT_DECLARATIONS\n'
rg -n --no-heading \
  '^(private |protected )?(noncomputable )?(theorem|lemma|def|abbrev) ' \
  "$project_dir/$target" 2>/dev/null | tail -n 8 | cut -c 1-400 || true
