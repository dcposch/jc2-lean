import Grok810AlignedSquareClearedNumeratorBlocksSeg20Scratch

/-! Part 21 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


def alignedSquareUBar810 (h a7 b8 b7 b6 b5 b4 b3 : R) : R :=
  (90 : R) * a7 ^ 7 - (448 : R) * a7 ^ 5 * b8 * h ^ 6 +
    (2240 : R) * a7 ^ 4 * b7 * h ^ 14 - (10240 : R) * a7 ^ 3 * b6 * h ^ 22 +
    (40960 : R) * a7 ^ 2 * b5 * h ^ 30 - (131072 : R) * a7 * b4 * h ^ 38 +
    (262144 : R) * b3 * h ^ 46


end AlignedSquareBars810
end Max11DegreeRoutes
end
