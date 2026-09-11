import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 55 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `15` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock15_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (56623104 : K) * A * C0 ^ 2 * U0
    - (802160640 : K) * A * C0 * D0 * E0
    + (150994944 : K) * A * C0 * D0 * T0
    + (188743680 : K) * A * C0 * E0 * S0
    + (226492416 : K) * A * C0 * F0 * R
    + (264241152 : K) * A * C0 * G0 * Q
    - (133693440 : K) * A * D0 ^ 3
    + (94371840 : K) * A * D0 ^ 2 * S0
    + (226492416 : K) * A * D0 * E0 * R


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
