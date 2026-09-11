import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 11 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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

section AlignedSquareBars810

variable {R : Type*} [CommRing R]


def alignedSquareCBar810 (h a7 a6 a5 a4 : R) : R :=
  (2048 : R) * a4 * h ^ 24 - (1280 : R) * a5 * a7 * h ^ 16 +
    (480 : R) * a6 * a7 ^ 2 * h ^ 8 - (105 : R) * a7 ^ 4


end AlignedSquareBars810
end Max11DegreeRoutes
end
