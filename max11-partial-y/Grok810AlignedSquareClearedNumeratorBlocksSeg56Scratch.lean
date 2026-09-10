import Grok810AlignedSquareClearedNumeratorBlocksSeg55Scratch

/-! Part 56 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `16` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock16_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (264241152 : K) * A * D0 * F0 * Q
    + (301989888 : K) * A * D0 * G0 * P
    + (132120576 : K) * A * E0 ^ 2 * Q
    + (301989888 : K) * A * E0 * F0 * P
    - (33554432 : K) * A * E0 * W0
    + (377487360 : K) * A * F0 * G0
    - (67108864 : K) * A * F0 * V0
    - (100663296 : K) * A * G0 * U0
    + (16711680 : K) * B ^ 5 * P


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
