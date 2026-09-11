import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 57 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `17` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock17_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (104448000 : K) * B ^ 4 * D0
    - (16711680 : K) * B ^ 4 * S0
    + (208896000 : K) * B ^ 3 * C0 ^ 2
    - (80216064 : K) * B ^ 3 * C0 * R
    - (93585408 : K) * B ^ 3 * D0 * Q
    - (106954752 : K) * B ^ 3 * E0 * P
    - (133693440 : K) * B ^ 3 * G0
    + (12582912 : K) * B ^ 3 * V0
    - (140378112 : K) * B ^ 2 * C0 ^ 2 * Q


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
