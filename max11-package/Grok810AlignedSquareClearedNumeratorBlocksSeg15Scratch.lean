import Grok810AlignedSquareClearedNumeratorBlocksSeg14Scratch

/-! Part 15 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


def alignedSquareGBar810 (h a7 a6 a5 a4 a3 a2 a1 a0 : R) : R :=
  (16777216 : R) * a0 * h ^ 56 - (2097152 : R) * a1 * a7 * h ^ 48 +
    (262144 : R) * a2 * a7 ^ 2 * h ^ 40 -
    (32768 : R) * a3 * a7 ^ 3 * h ^ 32 +
    (4096 : R) * a4 * a7 ^ 4 * h ^ 24 - (512 : R) * a5 * a7 ^ 5 * h ^ 16 +
    (64 : R) * a6 * a7 ^ 6 * h ^ 8 - (7 : R) * a7 ^ 8


end AlignedSquareBars810
end Max11DegreeRoutes
end
