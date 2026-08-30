# Detect the especially costly generated-proof mistake where one declaration
# assumes both equality and a strict inequality between the same expressions.
# This is deliberately a narrow, low-false-positive lint: it considers named,
# parenthesized binders whose relation is written at top level with spaces.

function compact(s, t) {
  t = s
  gsub(/[[:space:]]/, "", t)
  return t
}

function relation_key(lhs, rhs) {
  return compact(lhs) SUBSEP compact(rhs)
}

function clear_decl(  key) {
  for (key in equality_line) delete equality_line[key]
  for (key in strict_line) delete strict_line[key]
  declaration = "<unknown>"
}

function report_pair(kind, key, first_line, second_line) {
  printf "PREFLIGHT_ERROR file=%s kind=%s declaration=%s lines=%s,%s\n", \
    FILENAME, kind, declaration, first_line, second_line > "/dev/stderr"
  errors++
}

function inspect_binder(text, line_no, body, pos, lhs, rhs, key, reverse) {
  body = text
  # The final binder can share its line with the theorem conclusion.
  sub(/\)[[:space:]]*:[[:space:]].*$/, ")", body)
  sub(/^[[:space:]]*\([A-Za-z_][A-Za-z0-9_']*[[:space:]]*:[[:space:]]*/, "", body)
  sub(/[[:space:]]*\)[[:space:]]*$/, "", body)
  gsub(/[\r\n]+/, " ", body)
  gsub(/[[:space:]]+/, " ", body)

  pos = index(body, " < ")
  if (pos == 0) pos = index(body, " > ")
  if (pos > 0) {
    lhs = substr(body, 1, pos - 1)
    rhs = substr(body, pos + 3)
    if (index(body, " > ") == pos) {
      key = relation_key(rhs, lhs)
    } else {
      key = relation_key(lhs, rhs)
    }
    reverse = relation_key(rhs, lhs)
    if (key in equality_line)
      report_pair("contradictory_equality_and_strict_inequality", key,
        equality_line[key], line_no)
    else if (reverse in equality_line)
      report_pair("contradictory_equality_and_strict_inequality", reverse,
        equality_line[reverse], line_no)
    strict_line[key] = line_no
    return
  }

  pos = index(body, " = ")
  if (pos > 0) {
    lhs = substr(body, 1, pos - 1)
    rhs = substr(body, pos + 3)
    key = relation_key(lhs, rhs)
    reverse = relation_key(rhs, lhs)
    if (key in strict_line)
      report_pair("contradictory_equality_and_strict_inequality", key,
        strict_line[key], line_no)
    else if (reverse in strict_line)
      report_pair("contradictory_equality_and_strict_inequality", reverse,
        strict_line[reverse], line_no)
    equality_line[key] = line_no
    equality_line[reverse] = line_no
  }
}

BEGIN {
  errors = 0
  in_binder = 0
  clear_decl()
}

FNR == 1 {
  clear_decl()
}

/^(private[[:space:]]+|noncomputable[[:space:]]+)?(def|abbrev|theorem|lemma)[[:space:]]+/ {
  clear_decl()
  declaration = $0
  sub(/^(private[[:space:]]+|noncomputable[[:space:]]+)?(def|abbrev|theorem|lemma)[[:space:]]+/, "", declaration)
  sub(/[[:space:](].*$/, "", declaration)
}

in_binder {
  binder = binder "\n" $0
  opens = $0
  closes = $0
  gsub(/[^(]/, "", opens)
  gsub(/[^)]/, "", closes)
  depth += length(opens) - length(closes)
  if (depth <= 0) {
    inspect_binder(binder, binder_line)
    in_binder = 0
  }
  next
}

/^[[:space:]]*\([A-Za-z_][A-Za-z0-9_']*[[:space:]]*:/ {
  binder = $0
  binder_line = FNR
  opens = $0
  closes = $0
  gsub(/[^(]/, "", opens)
  gsub(/[^)]/, "", closes)
  depth = length(opens) - length(closes)
  if (depth <= 0)
    inspect_binder(binder, binder_line)
  else
    in_binder = 1
}

END {
  if (errors > 0) exit 1
}
