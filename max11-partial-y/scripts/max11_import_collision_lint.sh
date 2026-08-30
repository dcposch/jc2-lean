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
pending=("$target")
# Deep scratch towers can exceed one hundred modules.  A recursive Bash DFS
# consumes the shell's small native stack and has intermittently aborted before
# an otherwise valid AWS gate.  Declaration collisions do not depend on walk
# order, so traverse the same graph with an explicit worklist.
while ((${#pending[@]})); do
  pending_index=$((${#pending[@]} - 1))
  source="${pending[$pending_index]}"
  unset 'pending[$pending_index]'
  already_seen=0
  for known in ${closure[@]+"${closure[@]}"}; do
    [[ "$known" == "$source" ]] && already_seen=1
  done
  ((already_seen == 0)) || continue
  closure+=("$source")
  while IFS= read -r module; do
    [[ "$module" =~ ^[A-Za-z0-9_.]+$ ]] || continue
    dependency="${module//./\/}.lean"
    [[ -f "$project_dir/$dependency" ]] || continue
    pending+=("$dependency")
  done < <(sed -nE \
    's/^import[[:space:]]+([A-Za-z0-9_.]+)[[:space:]]*$/\1/p' \
    "$project_dir/$source")
done

declarations="$(mktemp -t max11-import-declarations.XXXXXX)"
duplicates="$(mktemp -t max11-import-duplicates.XXXXXX)"
trap 'rm -f -- "$declarations" "$duplicates"' EXIT

for source in ${closure[@]+"${closure[@]}"}; do
  source_origin="scratch"
  if git -C "$project_dir" ls-files --error-unmatch -- \
      "$source" >/dev/null 2>&1; then
    source_origin="tracked"
  fi
  LC_ALL=C awk -v source="$source" -v source_origin="$source_origin" '
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
      if (text !~ /^(theorem|lemma|def|abbrev|axiom|opaque|structure|class|inductive)[[:space:]]+[^[:space:]]+/)
        next
      sub(/^(theorem|lemma|def|abbrev|axiom|opaque|structure|class|inductive)[[:space:]]+/, "", text)
      name = text
      sub(/[[:space:]].*$/, "", name)
      sub(/[({:].*$/, "", name)
      if (name == "")
        next
      full_name = name
      if (namespace_name != "" && name !~ /[.]/)
        full_name = namespace_name "." name
      printf "%s\t%s\t%d\t%s\n", full_name, source, FNR, source_origin
    }
  ' "$project_dir/$source" >>"$declarations"
done

LC_ALL=C sort -t $'\t' -k1,1 "$declarations" | awk -F '\t' '
  function emit() {
    # The tracked project contains a few deliberately repeated compatibility
    # declarations that Lean already accepts when their modules meet.  The
    # costly failures this guard targets arise when a scratch route redeclares
    # a tracked/global name, so fail only when the collision includes fresh
    # scratch source.
    if (count > 1 && has_scratch)
      printf "%s\t%s\n", previous, locations
  }
  {
    if ($1 != previous) {
      emit()
      previous = $1
      locations = $2 ":" $3
      count = 1
      has_scratch = ($4 == "scratch")
    } else {
      locations = locations "," $2 ":" $3
      count++
      if ($4 == "scratch")
        has_scratch = 1
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
