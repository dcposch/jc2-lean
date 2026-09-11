import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 49 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `9` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock9_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (125337600 : K) * A ^ 2 * B ^ 3 * R
    + (438681600 : K) * A ^ 2 * B ^ 2 * C0 * Q
    + (501350400 : K) * A ^ 2 * B ^ 2 * D0 * P
    + (626688000 : K) * A ^ 2 * B ^ 2 * F0
    - (60162048 : K) * A ^ 2 * B ^ 2 * U0
    + (501350400 : K) * A ^ 2 * B * C0 ^ 2 * P
    + (1253376000 : K) * A ^ 2 * B * C0 * E0
    - (160432128 : K) * A ^ 2 * B * C0 * T0
    + (626688000 : K) * A ^ 2 * B * D0 ^ 2


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
