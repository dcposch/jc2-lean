import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 18 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


def alignedSquareRBar810 (h a7 b8 b7 b6 : R) : R :=
  -(315 : R) * a7 ^ 4 + (896 : R) * a7 ^ 2 * b8 * h ^ 6 -
    (1792 : R) * a7 * b7 * h ^ 14 + (2048 : R) * b6 * h ^ 22


end AlignedSquareBars810
end Max11DegreeRoutes
end
