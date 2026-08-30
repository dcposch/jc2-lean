#!/usr/bin/env bash
# Emit one fail-closed, paste-ready semantic handoff for a verified scratch leaf.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"

usage() {
  echo "usage: $0 --file FILE.lean --next 'one-line residual or next row'" >&2
  exit 2
}

target=""
next=""
while (($#)); do
  case "$1" in
    --file)
      shift
      (($#)) || usage
      target="$1"
      ;;
    --next)
      shift
      (($#)) || usage
      next="$1"
      ;;
    *) usage ;;
  esac
  shift
done

[[ "$target" =~ ^[A-Za-z0-9_.-]+Scratch[.]lean$ &&
    "$target" == "${target##*/}" && -f "$project_dir/$target" ]] || usage
[[ -n "$next" && "$next" != *$'\n'* && "$next" != *$'\r'* ]] || usage

checkpoint_log="$(mktemp -t max11-handoff-checkpoint.XXXXXX)"
trap 'rm -f -- "$checkpoint_log"' EXIT

set +e
"$project_dir/scripts/max11_checkpoint.sh" "$target" >"$checkpoint_log" 2>&1
checkpoint_exit=$?
set -e

blocked() {
  printf 'HANDOFF_VERSION=1\nHANDOFF=blocked\nTARGET=%s\nREASON=%s\n' \
    "$target" "$1" >&2
  exit 1
}

((checkpoint_exit == 0)) || blocked "checkpoint_exit_$checkpoint_exit"

source_sha="$(sed -nE 's/^SOURCE_SHA256=([0-9a-f]{64})$/\1/p' \
  "$checkpoint_log" | tail -n 1)"
receipt_line="$(sed -nE \
  's/^RECEIPT=verified GATE_FINGERPRINT=([0-9a-f]{64}) VERIFIED_SHA256=([0-9a-f]{64})$/\1 \2/p' \
  "$checkpoint_log" | tail -n 1)"
gate_fingerprint="${receipt_line%% *}"
verified_sha="${receipt_line##* }"
import_gate="$(sed -nE 's/^DIRECT_IMPORT_GATE=(ready|blocked)$/\1/p' \
  "$checkpoint_log" | tail -n 1)"

[[ "$source_sha" =~ ^[0-9a-f]{64}$ ]] || blocked missing_source_sha
[[ "$gate_fingerprint" =~ ^[0-9a-f]{64}$ &&
   "$verified_sha" =~ ^[0-9a-f]{64}$ ]] || blocked missing_verified_receipt
[[ "$source_sha" == "$verified_sha" ]] || blocked source_receipt_sha_mismatch
[[ "$import_gate" == ready ]] || blocked direct_import_gate_blocked

receipt_file="$project_dir/.max11-lanes/gates/$gate_fingerprint.receipt"
[[ -f "$receipt_file" ]] || blocked missing_receipt_file
grep -Fxq 'BUILD_EXIT=0 ERROR_COUNT=0 SORRYAX_COUNT=0' "$receipt_file" ||
  blocked nonzero_gate_counts
grep -Fxq "VERIFIED_SHA256=$verified_sha FILE=$target" "$receipt_file" ||
  blocked receipt_leaf_mismatch

printf 'HANDOFF_VERSION=1\nHANDOFF=verified\nTARGET=%s\n' "$target"
printf 'SOURCE_SHA256=%s\nGATE_FINGERPRINT=%s\n' \
  "$source_sha" "$gate_fingerprint"
printf 'BUILD_EXIT=0 ERROR_COUNT=0 SORRYAX_COUNT=0\n'
printf 'DIRECT_IMPORT_GATE=ready\n'
printf 'NEXT_UNUSED_ROW_OR_RESIDUAL=%s\n' "$next"
