#!/usr/bin/env bash
# Reject recursive local import closures that declare the same global name.
set -euo pipefail

project_dir="$(cd "$(dirname "$0")/.." && pwd)"

usage() {
  echo "usage: $0 FILE.lean" >&2
  exit 2
}

[[ $# -eq 1 ]] || usage
target="$1"
[[ "$target" =~ ^[A-Za-z0-9_.-]+[.]lean$ &&
    "$target" == "${target##*/}" && -f "$project_dir/$target" ]] || usage

closure=()
collect_imports() {
  local source="$1" known module dependency
  for known in ${closure[@]+"${closure[@]}"}; do
    [[ "$known" == "$source" ]] && return
  done
  closure+=("$source")
  while IFS= read -r module; do
    [[ "$module" =~ ^[A-Za-z0-9_.]+$ ]] || continue
    dependency="${module//./\/}.lean"
    [[ -f "$project_dir/$dependency" ]] || continue
    collect_imports "$dependency"
  done < <(sed -nE \
    's/^import[[:space:]]+([A-Za-z0-9_.]+)[[:space:]]*$/\1/p' \
    "$project_dir/$source")
}
collect_imports "$target"

declarations="$(mktemp -t max11-import-declarations.XXXXXX)"
duplicates="$(mktemp -t max11-import-duplicates.XXXXXX)"
trap 'rm -f -- "$declarations" "$duplicates"' EXIT

for source in ${closure[@]+"${closure[@]}"}; do
  LC_ALL=C awk -v source="$source" '
    function strip_comments(line, output, i, pair, character) {
      output = ""
      for (i = 1; i <= length(line); i++) {
        pair = substr(line, i, 2)
        if (block_depth > 0) {
          if (pair == "/-") {
            block_depth++
            i++
          } else if (pair == "-/") {
            block_depth--
            i++
          }
          continue
        }
        if (pair == "/-") {
          block_depth++
          i++
          continue
        }
        if (pair == "--")
          break
        character = substr(line, i, 1)
        output = output character
      }
      return output
    }
    function push_namespace(name) {
      if (namespace_name == "")
        namespace_name = name
      else
        namespace_name = namespace_name "." name
    }
    function pop_named_namespace(name, suffix, keep) {
      if (namespace_name == name) {
        namespace_name = ""
        return
      }
      suffix = "." name
      if (length(namespace_name) > length(suffix) &&
          substr(namespace_name, length(namespace_name) - length(suffix) + 1) == suffix) {
        keep = length(namespace_name) - length(suffix)
        namespace_name = substr(namespace_name, 1, keep)
      }
    }
    {
      line = strip_comments($0)
      if (line ~ /^[[:space:]]*namespace[[:space:]]+[A-Za-z0-9_.]+[[:space:]]*$/) {
        name = line
        sub(/^[[:space:]]*namespace[[:space:]]+/, "", name)
        sub(/[[:space:]]*$/, "", name)
        push_namespace(name)
        next
      }
      if (line ~ /^[[:space:]]*end[[:space:]]+[A-Za-z0-9_.]+[[:space:]]*$/) {
        name = line
        sub(/^[[:space:]]*end[[:space:]]+/, "", name)
        sub(/[[:space:]]*$/, "", name)
        pop_named_namespace(name)
        next
      }
      text = line
      sub(/^[[:space:]]*/, "", text)
      if (text ~ /^private[[:space:]]+/)
        next
      while (text ~ /^(noncomputable|protected)[[:space:]]+/)
        sub(/^(noncomputable|protected)[[:space:]]+/, "", text)
      if (text !~ /^(theorem|lemma|def|abbrev|axiom|opaque|structure|class|inductive)[[:space:]]+[A-Za-z0-9_.]+/)
        next
      sub(/^(theorem|lemma|def|abbrev|axiom|opaque|structure|class|inductive)[[:space:]]+/, "", text)
      name = text
      sub(/[^A-Za-z0-9_.].*$/, "", name)
      if (name == "")
        next
      full_name = name
      if (namespace_name != "" && name !~ /[.]/)
        full_name = namespace_name "." name
      printf "%s\t%s\t%d\n", full_name, source, FNR
    }
  ' "$project_dir/$source" >>"$declarations"
done

LC_ALL=C sort -t $'\t' -k1,1 "$declarations" | awk -F '\t' '
  function emit() {
    if (count > 1)
      printf "%s\t%s\n", previous, locations
  }
  {
    if ($1 != previous) {
      emit()
      previous = $1
      locations = $2 ":" $3
      count = 1
    } else {
      locations = locations "," $2 ":" $3
      count++
    }
  }
  END { emit() }
' >"$duplicates"

if [[ -s "$duplicates" ]]; then
  while IFS=$'\t' read -r declaration locations; do
    printf 'PREFLIGHT_ERROR file=%s kind=import_declaration_collision declaration=%s locations=%s\n' \
      "$target" "$declaration" "$locations" >&2
  done <"$duplicates"
  exit 1
fi

printf 'IMPORT_COLLISION_LINT_OK file=%s closure_files=%s\n' \
  "$target" "${#closure[@]}"
