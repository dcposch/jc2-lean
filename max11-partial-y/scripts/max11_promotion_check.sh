#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 MODULE" >&2
  exit 64
fi

module="$1"
source_file="${module}.lean"

if [[ ! -f "$source_file" ]]; then
  echo "missing canonical source: $source_file" >&2
  exit 66
fi

count_occurrences() {
  local needle="$1"
  local file="$2"
  local matches
  matches="$(rg -F -o "$needle" "$file" 2>/dev/null || true)"
  if [[ -z "$matches" ]]; then
    echo 0
  else
    printf '%s\n' "$matches" | wc -l | tr -d ' '
  fi
}

check_count() {
  local file="$1"
  local expected="$2"
  local actual
  actual="$(count_occurrences "$module" "$file")"
  if [[ "$actual" -ne "$expected" ]]; then
    echo "$file: expected $expected references to $module, found $actual" >&2
    exit 65
  fi
  echo "$file references=$actual"
}

# lakefile.toml carries the module once in defaultTargets and once in the
# library roots.  The other registries carry it once each.
check_count lakefile.toml 2
check_count scripts/check_axioms.sh 1
check_count README.md 1

git diff --check -- "$source_file" README.md lakefile.toml scripts/check_axioms.sh

echo "source_sha256=$(sha256sum "$source_file" | awk '{print $1}')"
echo "PROMOTION_PREFLIGHT=0"
