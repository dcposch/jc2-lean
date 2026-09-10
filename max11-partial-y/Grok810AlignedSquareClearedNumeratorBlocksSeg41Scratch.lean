import Grok810AlignedSquareClearedNumeratorBlocksSeg40Scratch

/-! Part 41 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `1` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock1_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (376012800 : K) * L * A ^ 3 * C0 * E0
    + (188006400 : K) * L * A ^ 3 * D0 ^ 2
    - (193881600 : K) * L * A ^ 2 * B ^ 4
    + (564019200 : K) * L * A ^ 2 * B ^ 2 * E0
    + (1128038400 : K) * L * A ^ 2 * B * C0 * D0
    + (188006400 : K) * L * A ^ 2 * C0 ^ 3
    - (360972288 : K) * L * A ^ 2 * C0 * G0
    - (360972288 : K) * L * A ^ 2 * D0 * F0
    - (180486144 : K) * L * A ^ 2 * E0 ^ 2


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
