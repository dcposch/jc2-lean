#!/bin/sh
# Verify that the Solution theorems depend only on the three permitted axioms:
#   propext, Classical.choice, Quot.sound
# (in particular: no sorryAx, no Lean.ofReduceBool / Lean.trustCompiler,
# no custom axioms).  Run from the repository root after `lake build`.
set -eu
cd "$(dirname "$0")/.."

OUT="$(printf 'import Solution\n#print axioms TheoremA\n#print axioms TheoremA_charP\n' \
  | lake env lean --stdin 2>&1)" || {
  echo "$OUT"
  echo "FAIL: could not elaborate the probe (build first: lake build)"
  exit 1
}
echo "$OUT"

for thm in TheoremA TheoremA_charP; do
  LINE="$(echo "$OUT" | grep "'$thm' depends on axioms" || true)"
  if [ -z "$LINE" ]; then
    echo "FAIL: no axiom report for $thm"
    exit 1
  fi
  BAD="$(echo "$LINE" | sed -e "s/.*axioms: \\[//" -e "s/\\]//" -e "s/,/\\n/g" \
    | tr -d ' ' | grep -v -E '^(propext|Classical\.choice|Quot\.sound)$' || true)"
  if [ -n "$BAD" ]; then
    echo "FAIL: $thm depends on non-permitted axioms: $BAD"
    exit 1
  fi
done
echo "OK: TheoremA and TheoremA_charP depend only on permitted axioms."
