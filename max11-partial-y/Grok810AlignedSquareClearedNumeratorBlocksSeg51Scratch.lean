import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 51 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `11` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock11_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (18874368 : K) * A ^ 2 * C0 * W0
    - (140378112 : K) * A ^ 2 * D0 ^ 2 * Q
    - (320864256 : K) * A ^ 2 * D0 * E0 * P
    - (401080320 : K) * A ^ 2 * D0 * G0
    + (37748736 : K) * A ^ 2 * D0 * V0
    - (401080320 : K) * A ^ 2 * E0 * F0
    + (56623104 : K) * A ^ 2 * E0 * U0
    + (75497472 : K) * A ^ 2 * F0 * T0
    + (94371840 : K) * A ^ 2 * G0 * S0


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
