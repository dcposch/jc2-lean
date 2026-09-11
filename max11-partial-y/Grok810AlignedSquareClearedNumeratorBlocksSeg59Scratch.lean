import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 59 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `19` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock19_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (401080320 : K) * B * C0 ^ 2 * E0
    + (75497472 : K) * B * C0 ^ 2 * T0
    - (401080320 : K) * B * C0 * D0 ^ 2
    + (188743680 : K) * B * C0 * D0 * S0
    + (226492416 : K) * B * C0 * E0 * R
    + (264241152 : K) * B * C0 * F0 * Q
    + (301989888 : K) * B * C0 * G0 * P
    + (113246208 : K) * B * D0 ^ 2 * R
    + (264241152 : K) * B * D0 * E0 * Q


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
