import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 22 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


def alignedSquareVBar810 (h a7 b8 b7 b6 b5 b4 b3 b2 : R) : R :=
  -(315 : R) * a7 ^ 8 + (1792 : R) * a7 ^ 6 * b8 * h ^ 6 -
    (10752 : R) * a7 ^ 5 * b7 * h ^ 14 +
    (61440 : R) * a7 ^ 4 * b6 * h ^ 22 -
    (327680 : R) * a7 ^ 3 * b5 * h ^ 30 +
    (1572864 : R) * a7 ^ 2 * b4 * h ^ 38 -
    (6291456 : R) * a7 * b3 * h ^ 46 + (16777216 : R) * b2 * h ^ 54


end AlignedSquareBars810
end Max11DegreeRoutes
end
