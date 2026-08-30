#!/usr/bin/env bash
# Cheap checks that catch common generated-Lean failures before an AWS gate.
set -euo pipefail

strict=0
line_threshold="${MAX11_DECL_LINE_THRESHOLD:-80}"
script_dir="$(cd "$(dirname "$0")" && pwd)"

usage() {
  echo "usage: $0 [--strict] FILE.lean [FILE.lean ...]" >&2
  exit 2
}

if [[ "${1:-}" == --strict ]]; then
  strict=1
  shift
fi
(($#)) || usage
[[ "$line_threshold" =~ ^[1-9][0-9]*$ ]] || {
  echo "invalid MAX11_DECL_LINE_THRESHOLD: $line_threshold" >&2
  exit 2
}

# Two individually valid proof routes can still be impossible to import
# together when they export the same fully qualified declaration.  Detect the
# collision from the recursive local source DAG before starting an AWS gate.
for source in "$@"; do
  "$script_dir/max11_import_collision_lint.sh" "$source"
done

warning_count=0
strict_failure_count=0
for source in "$@"; do
  [[ "$source" =~ ^[A-Za-z0-9_.-]+[.]lean$ && "$source" == "${source##*/}" ]] || usage
  [[ -f "$source" ]] || {
    echo "missing Lean source: $source" >&2
    exit 2
  }

  if LC_ALL=C grep -nE \
      '^[[:space:]]*(sorry|admit)([[:space:]]|$)|[[:space:]]by[[:space:]]+(sorry|admit)([[:space:]]|$)|:=[[:space:]]*(sorry|admit)([[:space:]]|$)' \
      "$source"; then
    echo "PREFLIGHT_ERROR file=$source kind=forbidden_placeholder" >&2
    exit 1
  fi

  # Lean quite correctly accepts a theorem whose hypotheses are impossible.
  # Catch the common generated-proof regression `h₁ : A < B`, `h₂ : A = B`
  # before paying for a remote elaboration that proves only a vacuous branch.
  if ! LC_ALL=C awk -f "$script_dir/max11_hypothesis_lint.awk" "$source"; then
    exit 1
  fi

  # `open MvPolynomial Polynomial` makes constructors such as `X`, `C` and
  # simp lemmas such as `eval_mul` share the same unqualified names.  Lean can
  # sometimes infer the intended namespace, but failures otherwise cost a
  # full remote gate.  Keep this advisory because expected types do resolve
  # some uses; the warning is enough to prompt cheap qualification.
  namespace_warnings="$(LC_ALL=C awk -f \
    "$script_dir/max11_namespace_lint.awk" "$source")"
  if [[ -n "$namespace_warnings" ]]; then
    printf '%s\n' "$namespace_warnings" >&2
    namespace_warning_count="$(wc -l <<<"$namespace_warnings" | tr -d ' ')"
    warning_count=$((warning_count + namespace_warning_count))
  fi

  # A doc comment attaches to the following declaration.  Placing a scoped
  # option between them is a parse error; the option must precede the comment.
  misplaced_option_lines="$(awk '
    /\/--/ { in_doc = 1 }
    in_doc && /-\// { in_doc = 0; doc_pending = 1; next }
    doc_pending && /^[[:space:]]*$/ { next }
    doc_pending {
      if ($0 ~ /^[[:space:]]*set_option[[:space:]]+maxHeartbeats[[:space:]]+[0-9]+[[:space:]]+in[[:space:]]*$/)
        print NR
      doc_pending = 0
    }
  ' "$source")"
  if [[ -n "$misplaced_option_lines" ]]; then
    while IFS= read -r misplaced_line; do
      echo "PREFLIGHT_ERROR file=$source kind=option_after_doc_comment line=$misplaced_line" >&2
    done <<<"$misplaced_option_lines"
    exit 1
  fi

  bytes="$(stat -f '%z' "$source")"
  if ((bytes > 65536)); then
    echo "PREFLIGHT_WARN file=$source kind=large_file bytes=$bytes" >&2
    warning_count=$((warning_count + 1))
  fi

  # Generated algebra often places a very large expression directly in a
  # declaration.  Lean elaborates the declaration before any later theorem's
  # heartbeat override applies.  Flag long declarations unless their command
  # is immediately guarded by `set_option maxHeartbeats ... in`.
  while IFS='|' read -r start_line end_line declaration guarded; do
    [[ -n "$start_line" ]] || continue
    span=$((end_line - start_line + 1))
    if ((span >= line_threshold)) && [[ "$guarded" != 1 ]]; then
      printf 'PREFLIGHT_WARN file=%s kind=unguarded_large_declaration line=%s lines=%s declaration=%s\n' \
        "$source" "$start_line" "$span" "$declaration" >&2
      warning_count=$((warning_count + 1))
      strict_failure_count=$((strict_failure_count + 1))
    fi
  done < <(awk '
    function emit(end_line) {
      if (start_line > 0 && eligible)
        print start_line "|" end_line "|" declaration "|" guarded
    }
    /^[[:space:]]*set_option[[:space:]]+maxHeartbeats[[:space:]]+[0-9]+[[:space:]]+in[[:space:]]*$/ {
      heartbeat_pending = 1
      next
    }
    /^(private[[:space:]]+|noncomputable[[:space:]]+)?(def|abbrev|theorem|lemma)[[:space:]]+/ {
      emit(NR - 1)
      start_line = NR
      declaration = $0
      sub(/[[:space:]]*(:=|where).*$/, "", declaration)
      eligible = (declaration ~ /^(private[[:space:]]+|noncomputable[[:space:]]+)?(def|abbrev)[[:space:]]+/)
      guarded = heartbeat_pending
      heartbeat_pending = 0
    }
    END { emit(NR) }
  ' "$source")
done

echo "PREFLIGHT_OK files=$# warnings=$warning_count strict_failures=$strict_failure_count strict=$strict"
if ((strict && strict_failure_count)); then
  exit 1
fi
