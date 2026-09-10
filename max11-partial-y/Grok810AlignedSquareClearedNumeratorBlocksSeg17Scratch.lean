import Grok810AlignedSquareClearedNumeratorBlocksSeg16Scratch

/-! Part 17 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


def alignedSquareQBar810 (h a7 b8 b7 : R) : R :=
  (64 : R) * b7 * h ^ 14 - (64 : R) * a7 * b8 * h ^ 6 +
    (30 : R) * a7 ^ 3


end AlignedSquareBars810
end Max11DegreeRoutes
end
