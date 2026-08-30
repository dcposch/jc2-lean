#!/usr/bin/env bash
# Report whether a delegated proof engine is worth launching right now.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"
state_root="$project_dir/.max11-lanes"

usage() {
  echo "usage: $0 --engine claude|grok" >&2
  exit 2
}

engine=""
while (($#)); do
  case "$1" in
    --engine)
      shift
      (($#)) || usage
      engine="$1"
      ;;
    *) usage ;;
  esac
  shift
done

case "$engine" in
  claude)
    limit_pattern="You've hit your monthly spend limit"
    cooldown_seconds="${MAX11_CLAUDE_USAGE_COOLDOWN_SECONDS:-86400}"
    ;;
  grok)
    limit_pattern="Grok Build usage balance exhausted"
    cooldown_seconds="${MAX11_GROK_USAGE_COOLDOWN_SECONDS:-86400}"
    ;;
  *) usage ;;
esac
[[ "$cooldown_seconds" =~ ^[0-9]+$ ]] || {
  echo "invalid $engine usage cooldown: $cooldown_seconds" >&2
  exit 2
}

latest_epoch=0
latest_job=""
for output_log in "$state_root"/*/output.log; do
  [[ -f "$output_log" ]] || continue
  grep -Fq "$limit_pattern" "$output_log" || continue
  modified_epoch="$(stat -f %m "$output_log")"
  if ((modified_epoch > latest_epoch)); then
    latest_epoch="$modified_epoch"
    latest_job="$(basename "$(dirname "$output_log")")"
  fi
done

now="$(date +%s)"
age=$((now - latest_epoch))
if ((latest_epoch > 0 && age < cooldown_seconds)); then
  remaining=$((cooldown_seconds - age))
  printf 'ENGINE=%s STATE=usage_cooldown AGE_SECONDS=%s REMAINING_SECONDS=%s SOURCE_JOB=%s\n' \
    "$engine" "$age" "$remaining" "$latest_job"
  exit 75
fi

printf 'ENGINE=%s STATE=healthy\n' "$engine"
