import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 6 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFourteenthDefectBlock3_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (32469952757760 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b8
    - (1894080577536 : R) * h ^ 54 * a7 * a6 ^ 5 * b7
    - (10823317585920 : R) * h ^ 54 * a7 * a6 ^ 4 * a5 * b8
    - (360777252864 : R) * h ^ 54 * a6 ^ 6 * b8
    - (558077313024 : R) * h ^ 55 * a7 ^ 6 * a1 * lambda
    - (3348463878144 : R) * h ^ 55 * a7 ^ 5 * a6 * a2 * lambda
    - (3348463878144 : R) * h ^ 55 * a7 ^ 5 * a5 * a3 * lambda
    - (1674231939072 : R) * h ^ 55 * a7 ^ 5 * a4 ^ 2 * lambda
    - (8371159695360 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 2 * a3 * lambda
    - (16742319390720 : R) * h ^ 55 * a7 ^ 4 * a6 * a5 * a4 * lambda
    - (2790386565120 : R) * h ^ 55 * a7 ^ 4 * a5 ^ 3 * lambda
    - (11161546260480 : R) * h ^ 55 * a7 ^ 3 * a6 ^ 3 * a4 * lambda
    - (16742319390720 : R) * h ^ 55 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * lambda
    - (8371159695360 : R) * h ^ 55 * a7 ^ 2 * a6 ^ 4 * a5 * lambda
    - (558077313024 : R) * h ^ 55 * a7 * a6 ^ 6 * lambda
    - (563714457600 : R) * h ^ 56 * a7 ^ 6 * a0
    - (338228674560 : R) * h ^ 56 * a7 ^ 5 * a6 * a1
    - (338228674560 : R) * h ^ 56 * a7 ^ 5 * a5 * a2
    - (338228674560 : R) * h ^ 56 * a7 ^ 5 * a4 * a3
    + (6764573491200 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 2 * a2
    + (13529146982400 : R) * h ^ 56 * a7 ^ 4 * a6 * a5 * a3
    + (6764573491200 : R) * h ^ 56 * a7 ^ 4 * a6 * a4 ^ 2
    + (6764573491200 : R) * h ^ 56 * a7 ^ 4 * a5 ^ 2 * a4
    + (19166291558400 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 3 * a3
    + (57498874675200 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 2 * a5 * a4
    + (19166291558400 : R) * h ^ 56 * a7 ^ 3 * a6 * a5 ^ 3
    + (21984863846400 : R) * h ^ 56 * a7 ^ 2 * a6 ^ 4 * a4
    + (43969727692800 : R) * h ^ 56 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2
    + (11838003609600 : R) * h ^ 56 * a7 * a6 ^ 5 * a5
    + (354334801920 : R) * h ^ 56 * a6 ^ 7
    + (60129542144 : R) * h ^ 62 * a7 ^ 5 * b1
    + (601295421440 : R) * h ^ 62 * a7 ^ 4 * a6 * b2
    + (901943132160 : R) * h ^ 62 * a7 ^ 4 * a5 * b3
    + (1202590842880 : R) * h ^ 62 * a7 ^ 4 * a4 * b4
    + (1503238553600 : R) * h ^ 62 * a7 ^ 4 * a3 * b5
    + (1803886264320 : R) * h ^ 62 * a7 ^ 4 * a2 * b6
    + (2104533975040 : R) * h ^ 62 * a7 ^ 4 * a1 * b7
    + (2405181685760 : R) * h ^ 62 * a7 ^ 4 * a0 * b8
    + (1803886264320 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 2 * b3
    + (4810363371520 : R) * h ^ 62 * a7 ^ 3 * a6 * a5 * b4


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
