import Grok810AlignedSquareClearedNumeratorBlocksSeg57Scratch

/-! Part 58 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `18` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock18_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (320864256 : K) * B ^ 2 * C0 * D0 * P
    - (401080320 : K) * B ^ 2 * C0 * F0
    + (56623104 : K) * B ^ 2 * C0 * U0
    - (401080320 : K) * B ^ 2 * D0 * E0
    + (75497472 : K) * B ^ 2 * D0 * T0
    + (94371840 : K) * B ^ 2 * E0 * S0
    + (113246208 : K) * B ^ 2 * F0 * R
    + (132120576 : K) * B ^ 2 * G0 * Q
    - (106954752 : K) * B * C0 ^ 3 * P


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
