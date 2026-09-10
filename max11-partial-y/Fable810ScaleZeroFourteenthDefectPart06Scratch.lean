import Fable810ScaleZeroFourteenthDefectPart05Scratch

/-! Part 6 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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

section Depression810FifteenthClearing

variable {F : Type*} [Field F] [CharZero F]


def localClearedFifteenthDefectBlock3_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (145903732716994560 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b8
    + (12766576612737024 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 5 * b7
    + (72951866358497280 : R) * h ^ 54 * a7 ^ 2 * a6 ^ 4 * a5 * b8
    + (4863457757233152 : R) * h ^ 54 * a7 * a6 ^ 6 * b8
    + (1245718253666304 : R) * h ^ 55 * a7 ^ 7 * a1 * lambda
    + (8720027775664128 : R) * h ^ 55 * a7 ^ 6 * a6 * a2 * lambda
    + (8720027775664128 : R) * h ^ 55 * a7 ^ 6 * a5 * a3 * lambda
    + (4360013887832064 : R) * h ^ 55 * a7 ^ 6 * a4 ^ 2 * lambda
    + (26160083326992384 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 2 * a3 * lambda
    + (52320166653984768 : R) * h ^ 55 * a7 ^ 5 * a6 * a5 * a4 * lambda
    + (8720027775664128 : R) * h ^ 55 * a7 ^ 5 * a5 ^ 3 * lambda
    + (43600138878320640 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 3 * a4 * lambda
    + (65400208317480960 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * lambda
    + (43600138878320640 : R) * h ^ 55 * a7 ^ 3 * a6 ^ 4 * a5 * lambda
    + (4360013887832064 : R) * h ^ 55 * a7 ^ 2 * a6 ^ 6 * lambda
    + (1302711899258880 : R) * h ^ 56 * a7 ^ 7 * a0
    + (2279745823703040 : R) * h ^ 56 * a7 ^ 6 * a6 * a1
    + (2279745823703040 : R) * h ^ 56 * a7 ^ 6 * a5 * a2
    + (2279745823703040 : R) * h ^ 56 * a7 ^ 6 * a4 * a3
    - (13678474942218240 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 2 * a2
    - (27356949884436480 : R) * h ^ 56 * a7 ^ 5 * a6 * a5 * a3
    - (13678474942218240 : R) * h ^ 56 * a7 ^ 5 * a6 * a4 ^ 2
    - (13678474942218240 : R) * h ^ 56 * a7 ^ 5 * a5 ^ 2 * a4
    - (56993645592576000 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 3 * a3
    - (170980936777728000 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 2 * a5 * a4
    - (56993645592576000 : R) * h ^ 56 * a7 ^ 4 * a6 * a5 ^ 3
    - (91189832948121600 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 4 * a4
    - (182379665896243200 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2
    - (75231612182200320 : R) * h ^ 56 * a7 ^ 2 * a6 ^ 5 * a5
    - (4559491647406080 : R) * h ^ 56 * a7 * a6 ^ 7
    - (113103668772864 : R) * h ^ 62 * a7 ^ 6 * b1
    - (1357244025274368 : R) * h ^ 62 * a7 ^ 5 * a6 * b2
    - (2035866037911552 : R) * h ^ 62 * a7 ^ 5 * a5 * b3
    - (2714488050548736 : R) * h ^ 62 * a7 ^ 5 * a4 * b4
    - (3393110063185920 : R) * h ^ 62 * a7 ^ 5 * a3 * b5
    - (4071732075823104 : R) * h ^ 62 * a7 ^ 5 * a2 * b6
    - (4750354088460288 : R) * h ^ 62 * a7 ^ 5 * a1 * b7
    - (5428976101097472 : R) * h ^ 62 * a7 ^ 5 * a0 * b8
    - (5089665094778880 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * b3
    - (13572440252743680 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 * b4


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
