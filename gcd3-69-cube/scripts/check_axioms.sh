#!/bin/sh
set -eu
cd "$(dirname "$0")/.."

THEOREM="GCD369PolynomialCubeSourceExclusion"
OUT="$(printf 'import GCD369Cube\n#print axioms %s\n' "$THEOREM" |
  lake env lean --stdin 2>&1)" || {
  echo "$OUT"
  echo "FAIL: could not elaborate the axiom probe (build first: lake build)"
  exit 1
}
echo "$OUT"

BLOCK="$(echo "$OUT" | sed -n "/'$THEOREM' depends on axioms/,/]/p" | head -20)"
if [ -z "$BLOCK" ]; then
  echo "FAIL: no axiom report for $THEOREM"
  exit 1
fi
BAD="$(echo "$BLOCK" | tr '\n' ' ' | sed -e 's/.*axioms: \[//' -e 's/\].*//' -e 's/,/\n/g' |
  tr -d ' ' | grep -v -E '^(propext|Classical\.choice|Quot\.sound)$' || true)"
if [ -n "$BAD" ]; then
  echo "FAIL: $THEOREM depends on non-permitted axioms: $BAD"
  exit 1
fi
echo "OK: $THEOREM uses only permitted axioms."
