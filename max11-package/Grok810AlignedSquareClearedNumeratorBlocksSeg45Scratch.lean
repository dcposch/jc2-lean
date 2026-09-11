import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 45 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `5` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock5_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (441619200 : K) * A ^ 5 * B * C0
    - (51701760 : K) * A ^ 5 * B * R
    - (60318720 : K) * A ^ 5 * C0 * Q
    - (68935680 : K) * A ^ 5 * D0 * P
    - (86169600 : K) * A ^ 5 * F0
    + (6266880 : K) * A ^ 5 * U0
    + (368016000 : K) * A ^ 4 * B ^ 3
    - (150796800 : K) * A ^ 4 * B ^ 2 * Q
    - (344678400 : K) * A ^ 4 * B * C0 * P


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
