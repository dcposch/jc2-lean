import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 8 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock5_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (20517712413327360 : R) * h ^ 63 * a7 ^ 4 * a6 * a4 ^ 2 * lambda
    - (20517712413327360 : R) * h ^ 63 * a7 ^ 4 * a5 ^ 2 * a4 * lambda
    - (27356949884436480 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 3 * a3 * lambda
    - (82070849653309440 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * lambda
    - (27356949884436480 : R) * h ^ 63 * a7 ^ 3 * a6 * a5 ^ 3 * lambda
    - (20517712413327360 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 4 * a4 * lambda
    - (41035424826654720 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2 * lambda
    - (8207084965330944 : R) * h ^ 63 * a7 * a6 ^ 5 * a5 * lambda
    - (195406784888832 : R) * h ^ 63 * a6 ^ 7 * lambda
    - (1696555031592960 : R) * h ^ 64 * a7 ^ 5 * a6 * a0
    - (1696555031592960 : R) * h ^ 64 * a7 ^ 5 * a5 * a1
    - (1696555031592960 : R) * h ^ 64 * a7 ^ 5 * a4 * a2
    - (848277515796480 : R) * h ^ 64 * a7 ^ 5 * a3 ^ 2
    + (14844856526438400 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a1
    + (29689713052876800 : R) * h ^ 64 * a7 ^ 4 * a6 * a5 * a2
    + (29689713052876800 : R) * h ^ 64 * a7 ^ 4 * a6 * a4 * a3
    + (14844856526438400 : R) * h ^ 64 * a7 ^ 4 * a5 ^ 2 * a3
    + (14844856526438400 : R) * h ^ 64 * a7 ^ 4 * a5 * a4 ^ 2
    + (45241467509145600 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 3 * a2
    + (135724402527436800 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 2 * a5 * a3
    + (67862201263718400 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2
    + (135724402527436800 : R) * h ^ 64 * a7 ^ 3 * a6 * a5 ^ 2 * a4
    + (11310366877286400 : R) * h ^ 64 * a7 ^ 3 * a5 ^ 4
    + (53017344737280000 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 4 * a3
    + (212069378949120000 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 3 * a5 * a4
    + (106034689474560000 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 2 * a5 ^ 3
    + (28841435537080320 : R) * h ^ 64 * a7 * a6 ^ 5 * a4
    + (72103588842700800 : R) * h ^ 64 * a7 * a6 ^ 4 * a5 ^ 2
    + (6079322196541440 : R) * h ^ 64 * a6 ^ 6 * a5
    + (775568014442496 : R) * h ^ 70 * a7 ^ 4 * a6 * b1
    + (1551136028884992 : R) * h ^ 70 * a7 ^ 4 * a5 * b2
    + (2326704043327488 : R) * h ^ 70 * a7 ^ 4 * a4 * b3
    + (3102272057769984 : R) * h ^ 70 * a7 ^ 4 * a3 * b4
    + (3877840072212480 : R) * h ^ 70 * a7 ^ 4 * a2 * b5
    + (4653408086654976 : R) * h ^ 70 * a7 ^ 4 * a1 * b6
    + (5428976101097472 : R) * h ^ 70 * a7 ^ 4 * a0 * b7
    + (3102272057769984 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * b2
    + (9306816173309952 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 * b3
    + (12409088231079936 : R) * h ^ 70 * a7 ^ 3 * a6 * a4 * b4
    + (15511360288849920 : R) * h ^ 70 * a7 ^ 3 * a6 * a3 * b5


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
