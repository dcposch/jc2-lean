# Warn about identifiers that become ambiguous when both polynomial namespaces
# are opened.  This is advisory: elaboration context resolves some occurrences,
# while the risky forms below have repeatedly wasted full AWS gates.

function code_without_comments(line, start, rest, finish, prefix) {
  if (in_block_comment) {
    finish = index(line, "-/")
    if (!finish)
      return ""
    line = substr(line, finish + 2)
    in_block_comment = 0
  }
  while ((start = index(line, "/-")) > 0) {
    prefix = substr(line, 1, start - 1)
    rest = substr(line, start + 2)
    finish = index(rest, "-/")
    if (!finish) {
      in_block_comment = 1
      line = prefix
      break
    }
    line = prefix substr(rest, finish + 2)
  }
  sub(/--.*/, "", line)
  return line
}

{
  line = code_without_comments($0)
  code[NR] = line
  if (line ~ /^[[:space:]]*open([[:space:]]|$)/) {
    if (line ~ /(^|[[:space:]])MvPolynomial([[:space:]]|$)/)
      have_mv = 1
    if (line ~ /(^|[[:space:]])Polynomial([[:space:]]|$)/)
      have_poly = 1
  }
}

END {
  if (!(have_mv && have_poly))
    exit 0
  overlap = "eval_add|eval_sub|eval_neg|eval_mul|eval_pow|eval_C|eval_X|eval_ofNat|eval_zero|derivative_add|derivative_sub|derivative_mul|derivative_pow|derivative_C|derivative_X|derivative_zero"
  for (n = 1; n <= NR; n++) {
    line = code[n]
    if (line ~ /^[[:space:]]*(open|namespace|end)([[:space:]]|$)/)
      continue
    risky = 0
    kind = ""
    if (line ~ ("(^|[^.[:alnum:]_])(" overlap ")([^[:alnum:]_]|$)")) {
      risky = 1
      kind = "overlapping_lemma"
    } else if (line ~ /(^|[^.[:alnum:]_])X[[:space:]]*[-+*^]/ ||
               line ~ /(^|[^.[:alnum:]_])C[[:space:]]+[[:alnum:]_(]/) {
      risky = 1
      kind = "overlapping_constructor"
    }
    if (risky)
      printf "PREFLIGHT_WARN file=%s kind=namespace_ambiguity_risk line=%d form=%s\n", FILENAME, n, kind
  }
}
