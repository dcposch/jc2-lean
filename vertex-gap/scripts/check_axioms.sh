#!/bin/sh
# Verify that the Solution theorems depend only on the three permitted axioms:
#   propext, Classical.choice, Quot.sound
# (in particular: no sorryAx, no Lean.ofReduceBool / Lean.trustCompiler,
# no custom axioms).  Run from the repository root after `lake build`.
set -eu
cd "$(dirname "$0")/.."

OUT="$(printf 'import Solution\n#print axioms CornerEnumeration\n#print axioms GapConditionSideSymm\n#print axioms VertexGap22\n#print axioms VertexGap22_swapped\n' \
  | lake env lean --stdin 2>&1)" || {
  echo "$OUT"
  echo "FAIL: could not elaborate the probe (build first: lake build)"
  exit 1
}
echo "$OUT"

for thm in CornerEnumeration GapConditionSideSymm VertexGap22 VertexGap22_swapped; do
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
echo "OK: CornerEnumeration, GapConditionSideSymm, VertexGap22, VertexGap22_swapped depend only on permitted axioms."
