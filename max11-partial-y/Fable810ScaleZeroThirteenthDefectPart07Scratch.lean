import Fable810ScaleZeroThirteenthDefectPart06Scratch

/-! Part 7 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFourteenthDefectBlock4_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6012954214400 : R) * h ^ 62 * a7 ^ 3 * a6 * a4 * b5
    + (7215545057280 : R) * h ^ 62 * a7 ^ 3 * a6 * a3 * b6
    + (8418135900160 : R) * h ^ 62 * a7 ^ 3 * a6 * a2 * b7
    + (9620726743040 : R) * h ^ 62 * a7 ^ 3 * a6 * a1 * b8
    + (3006477107200 : R) * h ^ 62 * a7 ^ 3 * a5 ^ 2 * b5
    + (7215545057280 : R) * h ^ 62 * a7 ^ 3 * a5 * a4 * b6
    + (8418135900160 : R) * h ^ 62 * a7 ^ 3 * a5 * a3 * b7
    + (9620726743040 : R) * h ^ 62 * a7 ^ 3 * a5 * a2 * b8
    + (4209067950080 : R) * h ^ 62 * a7 ^ 3 * a4 ^ 2 * b7
    + (9620726743040 : R) * h ^ 62 * a7 ^ 3 * a4 * a3 * b8
    + (2405181685760 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 3 * b4
    + (9019431321600 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a5 * b5
    + (10823317585920 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a4 * b6
    + (12627203850240 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a3 * b7
    + (14431090114560 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a2 * b8
    + (10823317585920 : R) * h ^ 62 * a7 ^ 2 * a6 * a5 ^ 2 * b6
    + (25254407700480 : R) * h ^ 62 * a7 ^ 2 * a6 * a5 * a4 * b7
    + (28862180229120 : R) * h ^ 62 * a7 ^ 2 * a6 * a5 * a3 * b8
    + (14431090114560 : R) * h ^ 62 * a7 ^ 2 * a6 * a4 ^ 2 * b8
    + (4209067950080 : R) * h ^ 62 * a7 ^ 2 * a5 ^ 3 * b7
    + (14431090114560 : R) * h ^ 62 * a7 ^ 2 * a5 ^ 2 * a4 * b8
    + (1503238553600 : R) * h ^ 62 * a7 * a6 ^ 4 * b5
    + (7215545057280 : R) * h ^ 62 * a7 * a6 ^ 3 * a5 * b6
    + (8418135900160 : R) * h ^ 62 * a7 * a6 ^ 3 * a4 * b7
    + (9620726743040 : R) * h ^ 62 * a7 * a6 ^ 3 * a3 * b8
    + (12627203850240 : R) * h ^ 62 * a7 * a6 ^ 2 * a5 ^ 2 * b7
    + (28862180229120 : R) * h ^ 62 * a7 * a6 ^ 2 * a5 * a4 * b8
    + (9620726743040 : R) * h ^ 62 * a7 * a6 * a5 ^ 3 * b8
    + (360777252864 : R) * h ^ 62 * a6 ^ 5 * b6
    + (2104533975040 : R) * h ^ 62 * a6 ^ 4 * a5 * b7
    + (2405181685760 : R) * h ^ 62 * a6 ^ 4 * a4 * b8
    + (4810363371520 : R) * h ^ 62 * a6 ^ 3 * a5 ^ 2 * b8
    + (608811614208 : R) * h ^ 63 * a7 ^ 5 * a0 * lambda
    + (3044058071040 : R) * h ^ 63 * a7 ^ 4 * a6 * a1 * lambda
    + (3044058071040 : R) * h ^ 63 * a7 ^ 4 * a5 * a2 * lambda
    + (3044058071040 : R) * h ^ 63 * a7 ^ 4 * a4 * a3 * lambda
    + (6088116142080 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 2 * a2 * lambda
    + (12176232284160 : R) * h ^ 63 * a7 ^ 3 * a6 * a5 * a3 * lambda
    + (6088116142080 : R) * h ^ 63 * a7 ^ 3 * a6 * a4 ^ 2 * lambda
    + (6088116142080 : R) * h ^ 63 * a7 ^ 3 * a5 ^ 2 * a4 * lambda


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
