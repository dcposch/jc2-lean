import Fable810ScaleZeroThirteenthDefectPart07Scratch

/-! Part 8 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFourteenthDefectBlock5_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6088116142080 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 3 * a3 * lambda
    + (18264348426240 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * lambda
    + (6088116142080 : R) * h ^ 63 * a7 ^ 2 * a6 * a5 ^ 3 * lambda
    + (3044058071040 : R) * h ^ 63 * a7 * a6 ^ 4 * a4 * lambda
    + (6088116142080 : R) * h ^ 63 * a7 * a6 ^ 3 * a5 ^ 2 * lambda
    + (608811614208 : R) * h ^ 63 * a6 ^ 5 * a5 * lambda
    - (6764573491200 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 2 * a1
    - (13529146982400 : R) * h ^ 64 * a7 ^ 3 * a6 * a5 * a2
    - (13529146982400 : R) * h ^ 64 * a7 ^ 3 * a6 * a4 * a3
    - (6764573491200 : R) * h ^ 64 * a7 ^ 3 * a5 ^ 2 * a3
    - (6764573491200 : R) * h ^ 64 * a7 ^ 3 * a5 * a4 ^ 2
    - (13529146982400 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 3 * a2
    - (40587440947200 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 2 * a5 * a3
    - (20293720473600 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2
    - (40587440947200 : R) * h ^ 64 * a7 ^ 2 * a6 * a5 ^ 2 * a4
    - (3382286745600 : R) * h ^ 64 * a7 ^ 2 * a5 ^ 4
    - (10146860236800 : R) * h ^ 64 * a7 * a6 ^ 4 * a3
    - (40587440947200 : R) * h ^ 64 * a7 * a6 ^ 3 * a5 * a4
    - (20293720473600 : R) * h ^ 64 * a7 * a6 ^ 2 * a5 ^ 3
    - (2705829396480 : R) * h ^ 64 * a6 ^ 5 * a4
    - (6764573491200 : R) * h ^ 64 * a6 ^ 4 * a5 ^ 2
    - (343597383680 : R) * h ^ 70 * a7 ^ 3 * a6 * b1
    - (687194767360 : R) * h ^ 70 * a7 ^ 3 * a5 * b2
    - (1030792151040 : R) * h ^ 70 * a7 ^ 3 * a4 * b3
    - (1374389534720 : R) * h ^ 70 * a7 ^ 3 * a3 * b4
    - (1717986918400 : R) * h ^ 70 * a7 ^ 3 * a2 * b5
    - (2061584302080 : R) * h ^ 70 * a7 ^ 3 * a1 * b6
    - (2405181685760 : R) * h ^ 70 * a7 ^ 3 * a0 * b7
    - (1030792151040 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * b2
    - (3092376453120 : R) * h ^ 70 * a7 ^ 2 * a6 * a5 * b3
    - (4123168604160 : R) * h ^ 70 * a7 ^ 2 * a6 * a4 * b4
    - (5153960755200 : R) * h ^ 70 * a7 ^ 2 * a6 * a3 * b5
    - (6184752906240 : R) * h ^ 70 * a7 ^ 2 * a6 * a2 * b6
    - (7215545057280 : R) * h ^ 70 * a7 ^ 2 * a6 * a1 * b7
    - (8246337208320 : R) * h ^ 70 * a7 ^ 2 * a6 * a0 * b8
    - (2061584302080 : R) * h ^ 70 * a7 ^ 2 * a5 ^ 2 * b4
    - (5153960755200 : R) * h ^ 70 * a7 ^ 2 * a5 * a4 * b5
    - (6184752906240 : R) * h ^ 70 * a7 ^ 2 * a5 * a3 * b6
    - (7215545057280 : R) * h ^ 70 * a7 ^ 2 * a5 * a2 * b7
    - (8246337208320 : R) * h ^ 70 * a7 ^ 2 * a5 * a1 * b8


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
