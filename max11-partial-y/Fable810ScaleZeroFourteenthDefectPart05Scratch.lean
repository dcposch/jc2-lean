import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 5 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock2_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (32155102422761472 : R) * h ^ 47 * a7 ^ 6 * a6 * a5 ^ 2 * lambda
    - (64310204845522944 : R) * h ^ 47 * a7 ^ 5 * a6 ^ 3 * a5 * lambda
    - (16077551211380736 : R) * h ^ 47 * a7 ^ 4 * a6 ^ 5 * lambda
    - (1124606756782080 : R) * h ^ 48 * a7 ^ 8 * a1
    - (2768262785925120 : R) * h ^ 48 * a7 ^ 7 * a6 * a2
    - (2768262785925120 : R) * h ^ 48 * a7 ^ 7 * a5 * a3
    - (1384131392962560 : R) * h ^ 48 * a7 ^ 7 * a4 ^ 2
    + (12111149688422400 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 2 * a3
    + (24222299376844800 : R) * h ^ 48 * a7 ^ 6 * a6 * a5 * a4
    + (4037049896140800 : R) * h ^ 48 * a7 ^ 6 * a5 ^ 3
    + (67822438255165440 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 3 * a4
    + (101733657382748160 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2
    + (139278221416857600 : R) * h ^ 48 * a7 ^ 4 * a6 ^ 4 * a5
    + (25837119335301120 : R) * h ^ 48 * a7 ^ 3 * a6 ^ 6
    + (173694919901184 : R) * h ^ 54 * a7 ^ 7 * b2
    + (1823796658962432 : R) * h ^ 54 * a7 ^ 6 * a6 * b3
    + (2431728878616576 : R) * h ^ 54 * a7 ^ 6 * a5 * b4
    + (3039661098270720 : R) * h ^ 54 * a7 ^ 6 * a4 * b5
    + (3647593317924864 : R) * h ^ 54 * a7 ^ 6 * a3 * b6
    + (4255525537579008 : R) * h ^ 54 * a7 ^ 6 * a2 * b7
    + (4863457757233152 : R) * h ^ 54 * a7 ^ 6 * a1 * b8
    + (7295186635849728 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * b4
    + (18237966589624320 : R) * h ^ 54 * a7 ^ 5 * a6 * a5 * b5
    + (21885559907549184 : R) * h ^ 54 * a7 ^ 5 * a6 * a4 * b6
    + (25533153225474048 : R) * h ^ 54 * a7 ^ 5 * a6 * a3 * b7
    + (29180746543398912 : R) * h ^ 54 * a7 ^ 5 * a6 * a2 * b8
    + (10942779953774592 : R) * h ^ 54 * a7 ^ 5 * a5 ^ 2 * b6
    + (25533153225474048 : R) * h ^ 54 * a7 ^ 5 * a5 * a4 * b7
    + (29180746543398912 : R) * h ^ 54 * a7 ^ 5 * a5 * a3 * b8
    + (14590373271699456 : R) * h ^ 54 * a7 ^ 5 * a4 ^ 2 * b8
    + (15198305491353600 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 3 * b5
    + (54713899768872960 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 2 * a5 * b6
    + (63832883063685120 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 2 * a4 * b7
    + (72951866358497280 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 2 * a3 * b8
    + (63832883063685120 : R) * h ^ 54 * a7 ^ 4 * a6 * a5 ^ 2 * b7
    + (145903732716994560 : R) * h ^ 54 * a7 ^ 4 * a6 * a5 * a4 * b8
    + (24317288786165760 : R) * h ^ 54 * a7 ^ 4 * a5 ^ 3 * b8
    + (18237966589624320 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 4 * b6
    + (85110510751580160 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 3 * a5 * b7
    + (97269155144663040 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 3 * a4 * b8


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
