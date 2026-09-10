import Grok810AlignedSquareClearedNumeratorBlocksSeg53Scratch

/-! Part 54 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `14` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock14_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (802160640 : K) * A * B * D0 * F0
    + (113246208 : K) * A * B * D0 * U0
    - (401080320 : K) * A * B * E0 ^ 2
    + (150994944 : K) * A * B * E0 * T0
    + (188743680 : K) * A * B * F0 * S0
    + (226492416 : K) * A * B * G0 * R
    - (93585408 : K) * A * C0 ^ 3 * Q
    - (320864256 : K) * A * C0 ^ 2 * D0 * P
    - (401080320 : K) * A * C0 ^ 2 * F0


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
