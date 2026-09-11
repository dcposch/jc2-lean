import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 9 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFourteenthDefectBlock6_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (3092376453120 : R) * h ^ 70 * a7 ^ 2 * a4 ^ 2 * b6
    - (7215545057280 : R) * h ^ 70 * a7 ^ 2 * a4 * a3 * b7
    - (8246337208320 : R) * h ^ 70 * a7 ^ 2 * a4 * a2 * b8
    - (4123168604160 : R) * h ^ 70 * a7 ^ 2 * a3 ^ 2 * b8
    - (1030792151040 : R) * h ^ 70 * a7 * a6 ^ 3 * b3
    - (4123168604160 : R) * h ^ 70 * a7 * a6 ^ 2 * a5 * b4
    - (5153960755200 : R) * h ^ 70 * a7 * a6 ^ 2 * a4 * b5
    - (6184752906240 : R) * h ^ 70 * a7 * a6 ^ 2 * a3 * b6
    - (7215545057280 : R) * h ^ 70 * a7 * a6 ^ 2 * a2 * b7
    - (8246337208320 : R) * h ^ 70 * a7 * a6 ^ 2 * a1 * b8
    - (5153960755200 : R) * h ^ 70 * a7 * a6 * a5 ^ 2 * b5
    - (12369505812480 : R) * h ^ 70 * a7 * a6 * a5 * a4 * b6
    - (14431090114560 : R) * h ^ 70 * a7 * a6 * a5 * a3 * b7
    - (16492674416640 : R) * h ^ 70 * a7 * a6 * a5 * a2 * b8
    - (7215545057280 : R) * h ^ 70 * a7 * a6 * a4 ^ 2 * b7
    - (16492674416640 : R) * h ^ 70 * a7 * a6 * a4 * a3 * b8
    - (2061584302080 : R) * h ^ 70 * a7 * a5 ^ 3 * b6
    - (7215545057280 : R) * h ^ 70 * a7 * a5 ^ 2 * a4 * b7
    - (8246337208320 : R) * h ^ 70 * a7 * a5 ^ 2 * a3 * b8
    - (8246337208320 : R) * h ^ 70 * a7 * a5 * a4 ^ 2 * b8
    - (343597383680 : R) * h ^ 70 * a6 ^ 4 * b4
    - (1717986918400 : R) * h ^ 70 * a6 ^ 3 * a5 * b5
    - (2061584302080 : R) * h ^ 70 * a6 ^ 3 * a4 * b6
    - (2405181685760 : R) * h ^ 70 * a6 ^ 3 * a3 * b7
    - (2748779069440 : R) * h ^ 70 * a6 ^ 3 * a2 * b8
    - (3092376453120 : R) * h ^ 70 * a6 ^ 2 * a5 ^ 2 * b6
    - (7215545057280 : R) * h ^ 70 * a6 ^ 2 * a5 * a4 * b7
    - (8246337208320 : R) * h ^ 70 * a6 ^ 2 * a5 * a3 * b8
    - (4123168604160 : R) * h ^ 70 * a6 ^ 2 * a4 ^ 2 * b8
    - (2405181685760 : R) * h ^ 70 * a6 * a5 ^ 3 * b7
    - (8246337208320 : R) * h ^ 70 * a6 * a5 ^ 2 * a4 * b8
    - (687194767360 : R) * h ^ 70 * a5 ^ 4 * b8
    - (2705829396480 : R) * h ^ 71 * a7 ^ 3 * a6 * a0 * lambda
    - (2705829396480 : R) * h ^ 71 * a7 ^ 3 * a5 * a1 * lambda
    - (2705829396480 : R) * h ^ 71 * a7 ^ 3 * a4 * a2 * lambda
    - (1352914698240 : R) * h ^ 71 * a7 ^ 3 * a3 ^ 2 * lambda
    - (4058744094720 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 2 * a1 * lambda
    - (8117488189440 : R) * h ^ 71 * a7 ^ 2 * a6 * a5 * a2 * lambda
    - (8117488189440 : R) * h ^ 71 * a7 ^ 2 * a6 * a4 * a3 * lambda
    - (4058744094720 : R) * h ^ 71 * a7 ^ 2 * a5 ^ 2 * a3 * lambda


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
