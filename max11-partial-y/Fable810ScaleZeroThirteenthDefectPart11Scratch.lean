import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 11 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFourteenthDefectBlock8_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (4123168604160 : R) * h ^ 78 * a7 * a6 * a2 * b5
    + (4947802324992 : R) * h ^ 78 * a7 * a6 * a1 * b6
    + (5772436045824 : R) * h ^ 78 * a7 * a6 * a0 * b7
    + (1236950581248 : R) * h ^ 78 * a7 * a5 ^ 2 * b3
    + (3298534883328 : R) * h ^ 78 * a7 * a5 * a4 * b4
    + (4123168604160 : R) * h ^ 78 * a7 * a5 * a3 * b5
    + (4947802324992 : R) * h ^ 78 * a7 * a5 * a2 * b6
    + (5772436045824 : R) * h ^ 78 * a7 * a5 * a1 * b7
    + (6597069766656 : R) * h ^ 78 * a7 * a5 * a0 * b8
    + (2061584302080 : R) * h ^ 78 * a7 * a4 ^ 2 * b5
    + (4947802324992 : R) * h ^ 78 * a7 * a4 * a3 * b6
    + (5772436045824 : R) * h ^ 78 * a7 * a4 * a2 * b7
    + (6597069766656 : R) * h ^ 78 * a7 * a4 * a1 * b8
    + (2886218022912 : R) * h ^ 78 * a7 * a3 ^ 2 * b7
    + (6597069766656 : R) * h ^ 78 * a7 * a3 * a2 * b8
    + (274877906944 : R) * h ^ 78 * a6 ^ 3 * b2
    + (1236950581248 : R) * h ^ 78 * a6 ^ 2 * a5 * b3
    + (1649267441664 : R) * h ^ 78 * a6 ^ 2 * a4 * b4
    + (2061584302080 : R) * h ^ 78 * a6 ^ 2 * a3 * b5
    + (2473901162496 : R) * h ^ 78 * a6 ^ 2 * a2 * b6
    + (2886218022912 : R) * h ^ 78 * a6 ^ 2 * a1 * b7
    + (3298534883328 : R) * h ^ 78 * a6 ^ 2 * a0 * b8
    + (1649267441664 : R) * h ^ 78 * a6 * a5 ^ 2 * b4
    + (4123168604160 : R) * h ^ 78 * a6 * a5 * a4 * b5
    + (4947802324992 : R) * h ^ 78 * a6 * a5 * a3 * b6
    + (5772436045824 : R) * h ^ 78 * a6 * a5 * a2 * b7
    + (6597069766656 : R) * h ^ 78 * a6 * a5 * a1 * b8
    + (2473901162496 : R) * h ^ 78 * a6 * a4 ^ 2 * b6
    + (5772436045824 : R) * h ^ 78 * a6 * a4 * a3 * b7
    + (6597069766656 : R) * h ^ 78 * a6 * a4 * a2 * b8
    + (3298534883328 : R) * h ^ 78 * a6 * a3 ^ 2 * b8
    + (687194767360 : R) * h ^ 78 * a5 ^ 3 * b5
    + (2473901162496 : R) * h ^ 78 * a5 ^ 2 * a4 * b6
    + (2886218022912 : R) * h ^ 78 * a5 ^ 2 * a3 * b7
    + (3298534883328 : R) * h ^ 78 * a5 ^ 2 * a2 * b8
    + (2886218022912 : R) * h ^ 78 * a5 * a4 ^ 2 * b7
    + (6597069766656 : R) * h ^ 78 * a5 * a4 * a3 * b8
    + (1099511627776 : R) * h ^ 78 * a4 ^ 3 * b8
    + (2319282339840 : R) * h ^ 79 * a7 ^ 2 * a5 * a0 * lambda
    + (2319282339840 : R) * h ^ 79 * a7 ^ 2 * a4 * a1 * lambda


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
