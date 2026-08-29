#!/usr/bin/env bash
# Queue a linear sequence of delegated proof leaves behind exact gate receipts.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
engine=""
predecessor=""
dry_run=0
targets=()

usage() {
  cat >&2 <<'EOF'
usage: max11_lean_chain.sh --engine claude|grok --after FILE.lean \
         --target FILE.lean [--target FILE.lean ...] [--dry-run] -- INSTRUCTION...

The instruction may contain @PREDECESSOR@, @TARGET@, and @INDEX@ placeholders.
Every edge is delegated through max11_lean_after.sh, so a successor starts only
after the exact recursive-source/environment receipt for its predecessor exists.
EOF
  exit 2
}

while (($#)); do
  case "$1" in
    --engine)
      shift
      (($#)) || usage
      engine="$1"
      ;;
    --after)
      shift
      (($#)) || usage
      predecessor="$1"
      ;;
    --target)
      shift
      (($#)) || usage
      targets+=("$1")
      ;;
    --dry-run)
      dry_run=1
      ;;
    --)
      shift
      break
      ;;
    *) usage ;;
  esac
  shift
done
(($# && ${#targets[@]})) || usage
instruction_template="$*"

[[ "$engine" == claude || "$engine" == grok ]] || usage
[[ "$predecessor" =~ ^[A-Za-z0-9_.-]+Scratch\.lean$ &&
   "$predecessor" == "${predecessor##*/}" ]] || usage

seen_files=("$predecessor")
for target in "${targets[@]}"; do
  if [[ "$engine" == claude ]]; then
    [[ "$target" =~ ^Fable[A-Za-z0-9_.-]*Scratch\.lean$ ]] || usage
  else
    [[ "$target" =~ ^Grok[A-Za-z0-9_.-]*Scratch\.lean$ ]] || usage
  fi
  [[ "$target" == "${target##*/}" ]] || usage
  for seen_file in "${seen_files[@]}"; do
    if [[ "$target" == "$seen_file" ]]; then
      echo "cycle or duplicate chain target: $target" >&2
      exit 65
    fi
  done
  seen_files+=("$target")
done

index=1
for target in "${targets[@]}"; do
  instruction="${instruction_template//@PREDECESSOR@/$predecessor}"
  instruction="${instruction//@TARGET@/$target}"
  instruction="${instruction//@INDEX@/$index}"
  if ((dry_run)); then
    printf 'EDGE=%s AFTER=%s ENGINE=%s TARGET=%s INSTRUCTION=%q\n' \
      "$index" "$predecessor" "$engine" "$target" "$instruction"
  else
    "$project_dir/scripts/max11_lean_after.sh" \
      --after "$predecessor" --engine "$engine" --target "$target" -- \
      "$instruction"
  fi
  predecessor="$target"
  index=$((index + 1))
done
