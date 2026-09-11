import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 48 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `8` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock8_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (334233600 : K) * A ^ 3 * C0 * D0 * P
    + (417792000 : K) * A ^ 3 * C0 * F0
    - (40108032 : K) * A ^ 3 * C0 * U0
    + (417792000 : K) * A ^ 3 * D0 * E0
    - (53477376 : K) * A ^ 3 * D0 * T0
    - (66846720 : K) * A ^ 3 * E0 * S0
    - (80216064 : K) * A ^ 3 * F0 * R
    - (93585408 : K) * A ^ 3 * G0 * Q
    - (861696000 : K) * A ^ 2 * B ^ 3 * C0


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
