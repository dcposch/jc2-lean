import Grok810AlignedSquareClearedNumeratorBlocksSeg52Scratch

/-! Part 53 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `13` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock13_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (320864256 : K) * A * B ^ 2 * F0 * P
    + (18874368 : K) * A * B ^ 2 * W0
    + (417792000 : K) * A * B * C0 ^ 3
    - (240648192 : K) * A * B * C0 ^ 2 * R
    - (561512448 : K) * A * B * C0 * D0 * Q
    - (641728512 : K) * A * B * C0 * E0 * P
    - (802160640 : K) * A * B * C0 * G0
    + (75497472 : K) * A * B * C0 * V0
    - (320864256 : K) * A * B * D0 ^ 2 * P


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
