import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 44 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `4` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock4_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (339738624 : K) * L * C0 * D0 * F0
    + (169869312 : K) * L * C0 * E0 ^ 2
    + (169869312 : K) * L * D0 ^ 2 * E0
    - (150994944 : K) * L * G0 ^ 2
    - (64402800 : K) * A ^ 7 * B
    + (7360320 : K) * A ^ 7 * Q
    + (58882560 : K) * A ^ 6 * B * P
    + (73603200 : K) * A ^ 6 * D0
    - (7180800 : K) * A ^ 6 * S0


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
