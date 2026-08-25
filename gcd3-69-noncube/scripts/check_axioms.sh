#!/bin/sh
# Verify that every Solution theorem uses only Palomar's permitted axioms.
set -eu
cd "$(dirname "$0")/.."

THEOREMS="GCD369InvariantFibreDichotomy GCD369ZeroBracketSheet GCD369EllipticSheetEquation GCD369EllipticTerminalForm GCD369ForbiddenNumerator GCD369EllipticNonzeroExclusion GCD369SpecialFibreDichotomy GCD369ShiftedDSBracket GCD369ShiftedDSTerminalDescent GCD369DSInfinitySupport GCD369DSOneRootCube"
PROBE="import Solution\n"
for thm in $THEOREMS; do
  PROBE="${PROBE}#print axioms ${thm}\n"
done

OUT="$(printf '%b' "$PROBE" | lake env lean --stdin 2>&1)" || {
  echo "$OUT"
  echo "FAIL: could not elaborate the axiom probe (build first: lake build)"
  exit 1
}
echo "$OUT"

for thm in $THEOREMS; do
  LINE="$(echo "$OUT" | grep "'$thm' depends on axioms" || true)"
  if [ -z "$LINE" ]; then
    echo "FAIL: no axiom report for $thm"
    exit 1
  fi
  BAD="$(echo "$LINE" | sed -e 's/.*axioms: \[//' -e 's/\]//' -e 's/,/\n/g' \
    | tr -d ' ' | grep -v -E '^(propext|Classical\.choice|Quot\.sound)$' || true)"
  if [ -n "$BAD" ]; then
    echo "FAIL: $thm depends on non-permitted axioms: $BAD"
    exit 1
  fi
done
echo "OK: all eleven gcd3-69-noncube theorems use only permitted axioms."
