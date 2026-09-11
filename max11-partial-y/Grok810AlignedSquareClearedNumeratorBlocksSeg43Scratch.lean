import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 43 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `3` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock3_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    (94003200 : K) * L * B ^ 4 * C0
    - (120324096 : K) * L * B ^ 3 * F0
    - (360972288 : K) * L * B ^ 2 * C0 * E0
    - (180486144 : K) * L * B ^ 2 * D0 ^ 2
    - (360972288 : K) * L * B * C0 ^ 2 * D0
    + (339738624 : K) * L * B * D0 * G0
    + (339738624 : K) * L * B * E0 * F0
    - (30081024 : K) * L * C0 ^ 4
    + (169869312 : K) * L * C0 ^ 2 * G0


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
