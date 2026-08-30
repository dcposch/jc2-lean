#!/usr/bin/env bash
# Fail fast unless every direct local scratch import has an exact gate receipt.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
quiet=0
targets=()

usage() {
  echo "usage: $0 [--quiet] FILE.lean [FILE.lean ...]" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --quiet) quiet=1 ;;
    -*) usage ;;
    *) targets+=("$1") ;;
  esac
  shift
done
((${#targets[@]})) || usage

tmp_log="$(mktemp -t max11-verified-imports.XXXXXX)"
trap 'rm -f -- "$tmp_log"' EXIT

declare_status=0
checked=()
for target in "${targets[@]}"; do
  [[ "$target" =~ ^[A-Za-z0-9_.-]+[.]lean$ &&
      "$target" == "${target##*/}" && -f "$project_dir/$target" ]] || usage
  while IFS= read -r module; do
    [[ "$module" =~ ^[A-Za-z0-9_.]+$ ]] || continue
    dependency="${module//./\/}.lean"
    [[ -f "$project_dir/$dependency" ]] || continue

    # Tracked library imports are covered by TRACKED_ENV_SHA256.  Local
    # scratch imports need their own exact recursive source receipt.
    if [[ "$dependency" != *Scratch.lean ]] &&
        git -C "$project_dir" ls-files --error-unmatch -- \
          "$dependency" >/dev/null 2>&1; then
      continue
    fi
    already_checked=0
    for known in ${checked[@]+"${checked[@]}"}; do
      [[ "$known" == "$dependency" ]] && already_checked=1
    done
    ((already_checked == 0)) || continue
    checked+=("$dependency")

    if "$project_dir/scripts/box_lean_verify.sh" --file "$dependency" \
        --receipt-only >"$tmp_log" 2>&1; then
      if ((quiet == 0)); then
        fingerprint="$(sed -nE \
          's/^GATE_RECEIPT_SHA256=([0-9a-f]{64})$/\1/p' \
          "$tmp_log" | tail -1)"
        printf 'VERIFIED_IMPORT target=%s dependency=%s receipt=%s\n' \
          "$target" "$dependency" "${fingerprint:-unknown}"
      fi
    else
      declare_status=1
      fingerprint="$(sed -nE \
        's/^GATE_RECEIPT_MISSING SHA256=([0-9a-f]{64})$/\1/p' \
        "$tmp_log" | tail -1)"
      printf 'UNVERIFIED_IMPORT target=%s dependency=%s fingerprint=%s\n' \
        "$target" "$dependency" "${fingerprint:-unknown}" >&2
      grep -m 1 -E \
        'GATE_FAILURE_KNOWN|PREFLIGHT_FAIL|error:|error\(' \
        "$tmp_log" >&2 || true
    fi
  done < <(sed -nE \
    's/^import[[:space:]]+([A-Za-z0-9_.]+)[[:space:]]*$/\1/p' \
    "$project_dir/$target")
done

if ((declare_status != 0)); then
  echo "Refusing an expensive successor gate until each direct scratch import has an exact success receipt." >&2
  exit 1
fi
((quiet == 1)) || printf 'VERIFIED_IMPORTS_OK targets=%s dependencies=%s\n' \
  "${#targets[@]}" "${#checked[@]}"
