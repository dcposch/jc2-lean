#!/bin/sh
# Verify that every proved theorem uses only Palomar's permitted axioms.
set -eu
cd "$(dirname "$0")/.."

BASE_THEOREMS="$(sed -n 's/^theorem \([^ ]*\).*/\1/p' Max11Core.lean)"
ROUTE_THEOREMS="$(sed -n 's/^theorem \([^ ]*\).*/Max11ClassicalRoutes.\1/p' ClassicalRoutes.lean)"
DEGREE_THEOREMS="$(sed -n 's/^theorem \([^ ]*\).*/Max11DegreeRoutes.\1/p' DegreeRoutes.lean)"
HISTORY_THEOREMS="$(sed -n 's/^theorem \([^ ]*\).*/Max11DegreeRoutes.\1/p' HistoryRoute.lean)"
HISTORY_DEGREE_THEOREMS="$(sed -n 's/^theorem \([^ ]*\).*/Max11DegreeRoutes.\1/p' HistoryDegree.lean)"
TOTAL_DEGREE_THEOREMS="$(sed -n 's/^theorem \([^ ]*\).*/Max11DegreeRoutes.\1/p' TotalDegreeRoutes.lean)"
COPRIME_DEGREE_THEOREMS="$(sed -n 's/^theorem \([^ ]*\).*/Max11DegreeRoutes.\1/p' CoprimeDegreeRoute.lean)"
ENDPOINT_GCD_THEOREMS="$(sed -n 's/^theorem \([^ ]*\).*/Max11DegreeRoutes.\1/p' EndpointGCDRoute.lean)"
LOW_SCALE_THEOREMS="$(sed -n 's/^theorem \([^ ]*\).*/Max11DegreeRoutes.\1/p' LowScaleCore.lean)"
ASSEMBLY_THEOREMS="$(sed -n 's/^theorem \([^ ]*\).*/Max11DegreeRoutes.\1/p' Max11Assembly.lean)"
THEOREMS="$BASE_THEOREMS $ROUTE_THEOREMS $DEGREE_THEOREMS $HISTORY_THEOREMS $HISTORY_DEGREE_THEOREMS $TOTAL_DEGREE_THEOREMS $COPRIME_DEGREE_THEOREMS $ENDPOINT_GCD_THEOREMS $LOW_SCALE_THEOREMS $ASSEMBLY_THEOREMS"
PROBE="import Max11Assembly\n"
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
  BLOCK="$(echo "$OUT" | sed -n "/'$thm' depends on axioms/,/]/p" | head -20)"
  if [ -z "$BLOCK" ]; then
    echo "FAIL: no axiom report for $thm"
    exit 1
  fi
  BAD="$(echo "$BLOCK" | tr '\n' ' ' | sed -e 's/.*axioms: \[//' -e 's/\].*//' -e 's/,/\n/g' \
    | tr -d ' ' | grep -v -E '^(propext|Classical\.choice|Quot\.sound)$' || true)"
  if [ -n "$BAD" ]; then
    echo "FAIL: $thm depends on non-permitted axioms: $BAD"
    exit 1
  fi
done
COUNT="$(printf '%s\n' $THEOREMS | wc -l | tr -d ' ')"
echo "OK: all $COUNT max11-partial-y theorems use only permitted axioms."
