import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 7 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock4_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (16965550315929600 : R) * h ^ 62 * a7 ^ 4 * a6 * a4 * b5
    - (20358660379115520 : R) * h ^ 62 * a7 ^ 4 * a6 * a3 * b6
    - (23751770442301440 : R) * h ^ 62 * a7 ^ 4 * a6 * a2 * b7
    - (27144880505487360 : R) * h ^ 62 * a7 ^ 4 * a6 * a1 * b8
    - (8482775157964800 : R) * h ^ 62 * a7 ^ 4 * a5 ^ 2 * b5
    - (20358660379115520 : R) * h ^ 62 * a7 ^ 4 * a5 * a4 * b6
    - (23751770442301440 : R) * h ^ 62 * a7 ^ 4 * a5 * a3 * b7
    - (27144880505487360 : R) * h ^ 62 * a7 ^ 4 * a5 * a2 * b8
    - (11875885221150720 : R) * h ^ 62 * a7 ^ 4 * a4 ^ 2 * b7
    - (27144880505487360 : R) * h ^ 62 * a7 ^ 4 * a4 * a3 * b8
    - (9048293501829120 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * b4
    - (33931100631859200 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 2 * a5 * b5
    - (40717320758231040 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 2 * a4 * b6
    - (47503540884602880 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 2 * a3 * b7
    - (54289761010974720 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 2 * a2 * b8
    - (40717320758231040 : R) * h ^ 62 * a7 ^ 3 * a6 * a5 ^ 2 * b6
    - (95007081769205760 : R) * h ^ 62 * a7 ^ 3 * a6 * a5 * a4 * b7
    - (108579522021949440 : R) * h ^ 62 * a7 ^ 3 * a6 * a5 * a3 * b8
    - (54289761010974720 : R) * h ^ 62 * a7 ^ 3 * a6 * a4 ^ 2 * b8
    - (15834513628200960 : R) * h ^ 62 * a7 ^ 3 * a5 ^ 3 * b7
    - (54289761010974720 : R) * h ^ 62 * a7 ^ 3 * a5 ^ 2 * a4 * b8
    - (8482775157964800 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 4 * b5
    - (40717320758231040 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 3 * a5 * b6
    - (47503540884602880 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 3 * a4 * b7
    - (54289761010974720 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 3 * a3 * b8
    - (71255311326904320 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b7
    - (162869283032924160 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b8
    - (54289761010974720 : R) * h ^ 62 * a7 ^ 2 * a6 * a5 ^ 3 * b8
    - (4071732075823104 : R) * h ^ 62 * a7 * a6 ^ 5 * b6
    - (23751770442301440 : R) * h ^ 62 * a7 * a6 ^ 4 * a5 * b7
    - (27144880505487360 : R) * h ^ 62 * a7 * a6 ^ 4 * a4 * b8
    - (54289761010974720 : R) * h ^ 62 * a7 * a6 ^ 3 * a5 ^ 2 * b8
    - (791725681410048 : R) * h ^ 62 * a6 ^ 6 * b7
    - (5428976101097472 : R) * h ^ 62 * a6 ^ 5 * a5 * b8
    - (1367847494221824 : R) * h ^ 63 * a7 ^ 6 * a0 * lambda
    - (8207084965330944 : R) * h ^ 63 * a7 ^ 5 * a6 * a1 * lambda
    - (8207084965330944 : R) * h ^ 63 * a7 ^ 5 * a5 * a2 * lambda
    - (8207084965330944 : R) * h ^ 63 * a7 ^ 5 * a4 * a3 * lambda
    - (20517712413327360 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 2 * a2 * lambda
    - (41035424826654720 : R) * h ^ 63 * a7 ^ 4 * a6 * a5 * a3 * lambda


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
