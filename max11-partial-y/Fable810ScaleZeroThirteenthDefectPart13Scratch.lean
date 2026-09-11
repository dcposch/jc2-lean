import Fable810ScaleZeroThirteenthDefectPart12Scratch

/-! Part 13 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFourteenthDefectBlock10_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1649267441664 : R) * h ^ 86 * a6 * a3 * b3
    - (2199023255552 : R) * h ^ 86 * a6 * a2 * b4
    - (2748779069440 : R) * h ^ 86 * a6 * a1 * b5
    - (3298534883328 : R) * h ^ 86 * a6 * a0 * b6
    - (549755813888 : R) * h ^ 86 * a5 ^ 2 * b2
    - (1649267441664 : R) * h ^ 86 * a5 * a4 * b3
    - (2199023255552 : R) * h ^ 86 * a5 * a3 * b4
    - (2748779069440 : R) * h ^ 86 * a5 * a2 * b5
    - (3298534883328 : R) * h ^ 86 * a5 * a1 * b6
    - (3848290697216 : R) * h ^ 86 * a5 * a0 * b7
    - (1099511627776 : R) * h ^ 86 * a4 ^ 2 * b4
    - (2748779069440 : R) * h ^ 86 * a4 * a3 * b5
    - (3298534883328 : R) * h ^ 86 * a4 * a2 * b6
    - (3848290697216 : R) * h ^ 86 * a4 * a1 * b7
    - (4398046511104 : R) * h ^ 86 * a4 * a0 * b8
    - (1649267441664 : R) * h ^ 86 * a3 ^ 2 * b6
    - (3848290697216 : R) * h ^ 86 * a3 * a2 * b7
    - (4398046511104 : R) * h ^ 86 * a3 * a1 * b8
    - (2199023255552 : R) * h ^ 86 * a2 ^ 2 * b8
    - (1855425871872 : R) * h ^ 87 * a7 * a4 * a0 * lambda
    - (1855425871872 : R) * h ^ 87 * a7 * a3 * a1 * lambda
    - (927712935936 : R) * h ^ 87 * a7 * a2 ^ 2 * lambda
    - (1855425871872 : R) * h ^ 87 * a6 * a5 * a0 * lambda
    - (1855425871872 : R) * h ^ 87 * a6 * a4 * a1 * lambda
    - (1855425871872 : R) * h ^ 87 * a6 * a3 * a2 * lambda
    - (927712935936 : R) * h ^ 87 * a5 ^ 2 * a1 * lambda
    - (1855425871872 : R) * h ^ 87 * a5 * a4 * a2 * lambda
    - (927712935936 : R) * h ^ 87 * a5 * a3 ^ 2 * lambda
    - (927712935936 : R) * h ^ 87 * a4 ^ 2 * a3 * lambda
    + (2061584302080 : R) * h ^ 88 * a7 * a3 * a0
    + (2061584302080 : R) * h ^ 88 * a7 * a2 * a1
    + (8246337208320 : R) * h ^ 88 * a6 * a4 * a0
    + (8246337208320 : R) * h ^ 88 * a6 * a3 * a1
    + (4123168604160 : R) * h ^ 88 * a6 * a2 ^ 2
    + (4123168604160 : R) * h ^ 88 * a5 ^ 2 * a0
    + (8246337208320 : R) * h ^ 88 * a5 * a4 * a1
    + (8246337208320 : R) * h ^ 88 * a5 * a3 * a2
    + (4123168604160 : R) * h ^ 88 * a4 ^ 2 * a2
    + (4123168604160 : R) * h ^ 88 * a4 * a3 ^ 2
    + (1099511627776 : R) * h ^ 94 * a3 * b1


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
