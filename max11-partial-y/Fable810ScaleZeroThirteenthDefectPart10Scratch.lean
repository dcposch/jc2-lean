import Fable810ScaleZeroThirteenthDefectPart09Scratch

/-! Part 10 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section Depression810FourteenthClearing

variable {F : Type*} [Field F] [CharZero F]


def localClearedFourteenthDefectBlock7_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4058744094720 : R) * h ^ 71 * a7 ^ 2 * a5 * a4 ^ 2 * lambda
    - (2705829396480 : R) * h ^ 71 * a7 * a6 ^ 3 * a2 * lambda
    - (8117488189440 : R) * h ^ 71 * a7 * a6 ^ 2 * a5 * a3 * lambda
    - (4058744094720 : R) * h ^ 71 * a7 * a6 ^ 2 * a4 ^ 2 * lambda
    - (8117488189440 : R) * h ^ 71 * a7 * a6 * a5 ^ 2 * a4 * lambda
    - (676457349120 : R) * h ^ 71 * a7 * a5 ^ 4 * lambda
    - (676457349120 : R) * h ^ 71 * a6 ^ 4 * a3 * lambda
    - (2705829396480 : R) * h ^ 71 * a6 ^ 3 * a5 * a4 * lambda
    - (1352914698240 : R) * h ^ 71 * a6 ^ 2 * a5 ^ 3 * lambda
    + (429496729600 : R) * h ^ 72 * a7 ^ 3 * a5 * a0
    + (429496729600 : R) * h ^ 72 * a7 ^ 3 * a4 * a1
    + (429496729600 : R) * h ^ 72 * a7 ^ 3 * a3 * a2
    + (6442450944000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 2 * a0
    + (12884901888000 : R) * h ^ 72 * a7 ^ 2 * a6 * a5 * a1
    + (12884901888000 : R) * h ^ 72 * a7 ^ 2 * a6 * a4 * a2
    + (6442450944000 : R) * h ^ 72 * a7 ^ 2 * a6 * a3 ^ 2
    + (6442450944000 : R) * h ^ 72 * a7 ^ 2 * a5 ^ 2 * a2
    + (12884901888000 : R) * h ^ 72 * a7 ^ 2 * a5 * a4 * a3
    + (2147483648000 : R) * h ^ 72 * a7 ^ 2 * a4 ^ 3
    + (8160437862400 : R) * h ^ 72 * a7 * a6 ^ 3 * a1
    + (24481313587200 : R) * h ^ 72 * a7 * a6 ^ 2 * a5 * a2
    + (24481313587200 : R) * h ^ 72 * a7 * a6 ^ 2 * a4 * a3
    + (24481313587200 : R) * h ^ 72 * a7 * a6 * a5 ^ 2 * a3
    + (24481313587200 : R) * h ^ 72 * a7 * a6 * a5 * a4 ^ 2
    + (8160437862400 : R) * h ^ 72 * a7 * a5 ^ 3 * a4
    + (3006477107200 : R) * h ^ 72 * a6 ^ 4 * a2
    + (12025908428800 : R) * h ^ 72 * a6 ^ 3 * a5 * a3
    + (6012954214400 : R) * h ^ 72 * a6 ^ 3 * a4 ^ 2
    + (18038862643200 : R) * h ^ 72 * a6 ^ 2 * a5 ^ 2 * a4
    + (3006477107200 : R) * h ^ 72 * a6 * a5 ^ 4
    + (412316860416 : R) * h ^ 78 * a7 ^ 2 * a5 * b1
    + (824633720832 : R) * h ^ 78 * a7 ^ 2 * a4 * b2
    + (1236950581248 : R) * h ^ 78 * a7 ^ 2 * a3 * b3
    + (1649267441664 : R) * h ^ 78 * a7 ^ 2 * a2 * b4
    + (2061584302080 : R) * h ^ 78 * a7 ^ 2 * a1 * b5
    + (2473901162496 : R) * h ^ 78 * a7 ^ 2 * a0 * b6
    + (412316860416 : R) * h ^ 78 * a7 * a6 ^ 2 * b1
    + (1649267441664 : R) * h ^ 78 * a7 * a6 * a5 * b2
    + (2473901162496 : R) * h ^ 78 * a7 * a6 * a4 * b3
    + (3298534883328 : R) * h ^ 78 * a7 * a6 * a3 * b4


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
