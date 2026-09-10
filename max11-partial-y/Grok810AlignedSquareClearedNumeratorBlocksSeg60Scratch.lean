import Grok810AlignedSquareClearedNumeratorBlocksSeg59Scratch

/-! Part 60 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `20` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock20_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (301989888 : K) * B * D0 * F0 * P
    - (33554432 : K) * B * D0 * W0
    + (150994944 : K) * B * E0 ^ 2 * P
    + (377487360 : K) * B * E0 * G0
    - (67108864 : K) * B * E0 * V0
    + (188743680 : K) * B * F0 ^ 2
    - (100663296 : K) * B * F0 * U0
    - (134217728 : K) * B * G0 * T0
    - (133693440 : K) * C0 ^ 3 * D0


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
