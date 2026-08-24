#!/bin/sh
# Audit the proved coefficient/setup lemmas.  The verdict-dependent witness
# theorem does not exist yet; HasDepthWitness is only a definition.
set -eu
cd "$(dirname "$0")/.."

NAMES="
JC72108.DepthWitness.windowPrime_prime
JC72108.DepthWitness.sqrtThree_sq
JC72108.DepthWitness.zeta42_pow
JC72108.DepthWitness.zeta42_primitive
JC72108.DepthWitness.etaB_seventh
JC72108.DepthWitness.fLead_value
JC72108.DepthWitness.gLead_value
JC72108.DepthWitness.lead_tower_relation
"

PROBE="import Solution\n"
for name in $NAMES; do
  PROBE="${PROBE}#print axioms ${name}\n"
done

OUT="$(printf '%b' "$PROBE" | lake env lean --stdin 2>&1)" || {
  echo "$OUT"
  echo "FAIL: could not elaborate the axiom probe (build first: lake build)"
  exit 1
}
echo "$OUT"

if echo "$OUT" | grep -E 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler' >/dev/null; then
  echo "FAIL: forbidden axiom or native-code trust boundary detected"
  exit 1
fi

for name in $NAMES; do
  LINE="$(echo "$OUT" | grep "'${name}' depends on axioms" || true)"
  if [ -z "$LINE" ]; then
    echo "FAIL: no axiom report for ${name}"
    exit 1
  fi
  BAD="$(echo "$LINE" | sed -e 's/.*axioms: \[//' -e 's/\]//' -e 's/,/\n/g' \
    | tr -d ' ' | grep -v -E '^(propext|Classical\.choice|Quot\.sound)$' || true)"
  if [ -n "$BAD" ]; then
    echo "FAIL: ${name} depends on non-permitted axioms: ${BAD}"
    exit 1
  fi
done

echo "OK: all depth-witness setup lemmas depend only on permitted axioms."
