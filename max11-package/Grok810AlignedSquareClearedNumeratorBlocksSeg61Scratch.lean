import Grok810AlignedSquareClearedNumeratorBlocksSeg60Scratch

/-! Part 61 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareCompactBlocks810

variable {K : Type*} [CommRing K]


/-- Compact block `21` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock21_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (31457280 : K) * C0 ^ 3 * S0
    + (113246208 : K) * C0 ^ 2 * D0 * R
    + (132120576 : K) * C0 ^ 2 * E0 * Q
    + (150994944 : K) * C0 ^ 2 * F0 * P
    - (16777216 : K) * C0 ^ 2 * W0
    + (132120576 : K) * C0 * D0 ^ 2 * Q
    + (301989888 : K) * C0 * D0 * E0 * P
    + (377487360 : K) * C0 * D0 * G0
    - (67108864 : K) * C0 * D0 * V0


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
