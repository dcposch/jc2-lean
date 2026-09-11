import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 47 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `7` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock7_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (861696000 : K) * A ^ 3 * B ^ 2 * D0
    + (104448000 : K) * A ^ 3 * B ^ 2 * S0
    - (861696000 : K) * A ^ 3 * B * C0 ^ 2
    + (250675200 : K) * A ^ 3 * B * C0 * R
    + (292454400 : K) * A ^ 3 * B * D0 * Q
    + (334233600 : K) * A ^ 3 * B * E0 * P
    + (417792000 : K) * A ^ 3 * B * G0
    - (26738688 : K) * A ^ 3 * B * V0
    + (146227200 : K) * A ^ 3 * C0 ^ 2 * Q


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
