import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 46 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


/-- Compact block `6` of `degreeZeroClearedCompact810`. -/
def alignedSquareCompactBlock6_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) : K :=
    - (430848000 : K) * A ^ 4 * B * E0
    + (41779200 : K) * A ^ 4 * B * T0
    - (430848000 : K) * A ^ 4 * C0 * D0
    + (52224000 : K) * A ^ 4 * C0 * S0
    + (62668800 : K) * A ^ 4 * D0 * R
    + (73113600 : K) * A ^ 4 * E0 * Q
    + (83558400 : K) * A ^ 4 * F0 * P
    - (3342336 : K) * A ^ 4 * W0
    - (229785600 : K) * A ^ 3 * B ^ 3 * P


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
