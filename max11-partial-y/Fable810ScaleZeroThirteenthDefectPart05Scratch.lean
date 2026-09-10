import Fable810ScaleZeroThirteenthDefectPart04Scratch

/-! Part 5 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFourteenthDefectBlock2_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (10882507603968 : R) * h ^ 47 * a7 ^ 5 * a6 * a5 ^ 2 * lambda
    + (18137512673280 : R) * h ^ 47 * a7 ^ 4 * a6 ^ 3 * a5 * lambda
    + (3627502534656 : R) * h ^ 47 * a7 ^ 3 * a6 ^ 5 * lambda
    + (487210352640 : R) * h ^ 48 * a7 ^ 7 * a1
    + (620085903360 : R) * h ^ 48 * a7 ^ 6 * a6 * a2
    + (620085903360 : R) * h ^ 48 * a7 ^ 6 * a5 * a3
    + (310042951680 : R) * h ^ 48 * a7 ^ 6 * a4 ^ 2
    - (6510901985280 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 2 * a3
    - (13021803970560 : R) * h ^ 48 * a7 ^ 5 * a6 * a5 * a4
    - (2170300661760 : R) * h ^ 48 * a7 ^ 5 * a5 ^ 3
    - (24803436134400 : R) * h ^ 48 * a7 ^ 4 * a6 ^ 3 * a4
    - (37205154201600 : R) * h ^ 48 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2
    - (38755368960000 : R) * h ^ 48 * a7 ^ 3 * a6 ^ 4 * a5
    - (5270730178560 : R) * h ^ 48 * a7 ^ 2 * a6 ^ 6
    - (90194313216 : R) * h ^ 54 * a7 ^ 6 * b2
    - (811748818944 : R) * h ^ 54 * a7 ^ 5 * a6 * b3
    - (1082331758592 : R) * h ^ 54 * a7 ^ 5 * a5 * b4
    - (1352914698240 : R) * h ^ 54 * a7 ^ 5 * a4 * b5
    - (1623497637888 : R) * h ^ 54 * a7 ^ 5 * a3 * b6
    - (1894080577536 : R) * h ^ 54 * a7 ^ 5 * a2 * b7
    - (2164663517184 : R) * h ^ 54 * a7 ^ 5 * a1 * b8
    - (2705829396480 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 2 * b4
    - (6764573491200 : R) * h ^ 54 * a7 ^ 4 * a6 * a5 * b5
    - (8117488189440 : R) * h ^ 54 * a7 ^ 4 * a6 * a4 * b6
    - (9470402887680 : R) * h ^ 54 * a7 ^ 4 * a6 * a3 * b7
    - (10823317585920 : R) * h ^ 54 * a7 ^ 4 * a6 * a2 * b8
    - (4058744094720 : R) * h ^ 54 * a7 ^ 4 * a5 ^ 2 * b6
    - (9470402887680 : R) * h ^ 54 * a7 ^ 4 * a5 * a4 * b7
    - (10823317585920 : R) * h ^ 54 * a7 ^ 4 * a5 * a3 * b8
    - (5411658792960 : R) * h ^ 54 * a7 ^ 4 * a4 ^ 2 * b8
    - (4509715660800 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 3 * b5
    - (16234976378880 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 2 * a5 * b6
    - (18940805775360 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 2 * a4 * b7
    - (21646635171840 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 2 * a3 * b8
    - (18940805775360 : R) * h ^ 54 * a7 ^ 3 * a6 * a5 ^ 2 * b7
    - (43293270343680 : R) * h ^ 54 * a7 ^ 3 * a6 * a5 * a4 * b8
    - (7215545057280 : R) * h ^ 54 * a7 ^ 3 * a5 ^ 3 * b8
    - (4058744094720 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 4 * b6
    - (18940805775360 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 3 * a5 * b7
    - (21646635171840 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 3 * a4 * b8


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
