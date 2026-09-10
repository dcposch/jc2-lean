import Fable810ScaleZeroFourteenthDefectPart09Scratch

/-! Part 10 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock7_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (775568014442496 : R) * h ^ 70 * a6 ^ 5 * b5
    + (4653408086654976 : R) * h ^ 70 * a6 ^ 4 * a5 * b6
    + (5428976101097472 : R) * h ^ 70 * a6 ^ 4 * a4 * b7
    + (6204544115539968 : R) * h ^ 70 * a6 ^ 4 * a3 * b8
    + (10857952202194944 : R) * h ^ 70 * a6 ^ 3 * a5 ^ 2 * b7
    + (24818176462159872 : R) * h ^ 70 * a6 ^ 3 * a5 * a4 * b8
    + (12409088231079936 : R) * h ^ 70 * a6 ^ 2 * a5 ^ 3 * b8
    + (7634497642168320 : R) * h ^ 71 * a7 ^ 4 * a6 * a0 * lambda
    + (7634497642168320 : R) * h ^ 71 * a7 ^ 4 * a5 * a1 * lambda
    + (7634497642168320 : R) * h ^ 71 * a7 ^ 4 * a4 * a2 * lambda
    + (3817248821084160 : R) * h ^ 71 * a7 ^ 4 * a3 ^ 2 * lambda
    + (15268995284336640 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a1 * lambda
    + (30537990568673280 : R) * h ^ 71 * a7 ^ 3 * a6 * a5 * a2 * lambda
    + (30537990568673280 : R) * h ^ 71 * a7 ^ 3 * a6 * a4 * a3 * lambda
    + (15268995284336640 : R) * h ^ 71 * a7 ^ 3 * a5 ^ 2 * a3 * lambda
    + (15268995284336640 : R) * h ^ 71 * a7 ^ 3 * a5 * a4 ^ 2 * lambda
    + (15268995284336640 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 3 * a2 * lambda
    + (45806985853009920 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * lambda
    + (22903492926504960 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * lambda
    + (45806985853009920 : R) * h ^ 71 * a7 ^ 2 * a6 * a5 ^ 2 * a4 * lambda
    + (3817248821084160 : R) * h ^ 71 * a7 ^ 2 * a5 ^ 4 * lambda
    + (7634497642168320 : R) * h ^ 71 * a7 * a6 ^ 4 * a3 * lambda
    + (30537990568673280 : R) * h ^ 71 * a7 * a6 ^ 3 * a5 * a4 * lambda
    + (15268995284336640 : R) * h ^ 71 * a7 * a6 ^ 2 * a5 ^ 3 * lambda
    + (1526899528433664 : R) * h ^ 71 * a6 ^ 5 * a4 * lambda
    + (3817248821084160 : R) * h ^ 71 * a6 ^ 4 * a5 ^ 2 * lambda
    + (969460018053120 : R) * h ^ 72 * a7 ^ 4 * a5 * a0
    + (969460018053120 : R) * h ^ 72 * a7 ^ 4 * a4 * a1
    + (969460018053120 : R) * h ^ 72 * a7 ^ 4 * a3 * a2
    - (15511360288849920 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a0
    - (31022720577699840 : R) * h ^ 72 * a7 ^ 3 * a6 * a5 * a1
    - (31022720577699840 : R) * h ^ 72 * a7 ^ 3 * a6 * a4 * a2
    - (15511360288849920 : R) * h ^ 72 * a7 ^ 3 * a6 * a3 ^ 2
    - (15511360288849920 : R) * h ^ 72 * a7 ^ 3 * a5 ^ 2 * a2
    - (31022720577699840 : R) * h ^ 72 * a7 ^ 3 * a5 * a4 * a3
    - (5170453429616640 : R) * h ^ 72 * a7 ^ 3 * a4 ^ 3
    - (32961640613806080 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 3 * a1
    - (98884921841418240 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 2 * a5 * a2
    - (98884921841418240 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 2 * a4 * a3
    - (98884921841418240 : R) * h ^ 72 * a7 ^ 2 * a6 * a5 ^ 2 * a3


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
