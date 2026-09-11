import Grok810SpeedValLibScratch
import Grok810DegreeZeroPoleAndClearingScratch

/-! Part 14 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


def alignedSquareFBar810 (h a7 a6 a5 a4 a3 a2 a1 : R) : R :=
  (131072 : R) * a1 * h ^ 48 - (32768 : R) * a2 * a7 * h ^ 40 +
    (6144 : R) * a3 * a7 ^ 2 * h ^ 32 - (1024 : R) * a4 * a7 ^ 3 * h ^ 24 +
    (160 : R) * a5 * a7 ^ 4 * h ^ 16 - (24 : R) * a6 * a7 ^ 5 * h ^ 8 +
    (3 : R) * a7 ^ 7


end AlignedSquareBars810
end Max11DegreeRoutes
end
