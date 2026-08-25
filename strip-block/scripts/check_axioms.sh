#!/bin/sh
# Verify that the four Solution theorems use only Mathlib's permitted logical
# axioms.  In particular, reject sorryAx, custom axioms, native_decide, and
# other trust escapes.  Run from this project after `lake build`.
set -eu
cd "$(dirname "$0")/.."

THEOREMS="BlockToODEBridge InnerBlockRigidity OuterResidueIdentity LogResidueBlockVariety"
PROBE="import Solution\n"
for thm in $THEOREMS; do
  PROBE="${PROBE}#print axioms ${thm}\n"
done

OUT="$(printf '%b' "$PROBE" | lake env lean --stdin 2>&1)" || {
  echo "$OUT"
  echo "FAIL: could not elaborate the probe (build first: lake build)"
  exit 1
}
echo "$OUT"

for thm in $THEOREMS; do
  LINE="$(echo "$OUT" | grep "'$thm' depends on axioms" || true)"
  if [ -z "$LINE" ]; then
    echo "FAIL: no axiom report for $thm"
    exit 1
  fi
  BAD="$(echo "$LINE" | sed -e "s/.*axioms: \\[//" -e "s/\\]//" -e "s/,/\n/g" \
    | tr -d ' ' | grep -v -E '^(propext|Classical\.choice|Quot\.sound)$' || true)"
  if [ -n "$BAD" ]; then
    echo "FAIL: $thm depends on non-permitted axioms: $BAD"
    exit 1
  fi
done

echo "OK: all strip-block theorems depend only on permitted axioms."
