import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 13 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock10_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (20940336389947392 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 * a1 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 ^ 2 * a6 * a4 * a2 * lambda
    - (10470168194973696 : R) * h ^ 79 * a7 ^ 2 * a6 * a3 ^ 2 * lambda
    - (10470168194973696 : R) * h ^ 79 * a7 ^ 2 * a5 ^ 2 * a2 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 ^ 2 * a5 * a4 * a3 * lambda
    - (3490056064991232 : R) * h ^ 79 * a7 ^ 2 * a4 ^ 3 * lambda
    - (6980112129982464 : R) * h ^ 79 * a7 * a6 ^ 3 * a1 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 * a6 ^ 2 * a5 * a2 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 * a6 ^ 2 * a4 * a3 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 * a6 * a5 ^ 2 * a3 * lambda
    - (20940336389947392 : R) * h ^ 79 * a7 * a6 * a5 * a4 ^ 2 * lambda
    - (6980112129982464 : R) * h ^ 79 * a7 * a5 ^ 3 * a4 * lambda
    - (1745028032495616 : R) * h ^ 79 * a6 ^ 4 * a2 * lambda
    - (6980112129982464 : R) * h ^ 79 * a6 ^ 3 * a5 * a3 * lambda
    - (3490056064991232 : R) * h ^ 79 * a6 ^ 3 * a4 ^ 2 * lambda
    - (10470168194973696 : R) * h ^ 79 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (1745028032495616 : R) * h ^ 79 * a6 * a5 ^ 4 * lambda
    + (31022720577699840 : R) * h ^ 80 * a7 ^ 2 * a6 * a5 * a0
    + (31022720577699840 : R) * h ^ 80 * a7 ^ 2 * a6 * a4 * a1
    + (31022720577699840 : R) * h ^ 80 * a7 ^ 2 * a6 * a3 * a2
    + (15511360288849920 : R) * h ^ 80 * a7 ^ 2 * a5 ^ 2 * a1
    + (31022720577699840 : R) * h ^ 80 * a7 ^ 2 * a5 * a4 * a2
    + (15511360288849920 : R) * h ^ 80 * a7 ^ 2 * a5 * a3 ^ 2
    + (15511360288849920 : R) * h ^ 80 * a7 ^ 2 * a4 ^ 2 * a3
    + (20681813718466560 : R) * h ^ 80 * a7 * a6 ^ 3 * a0
    + (62045441155399680 : R) * h ^ 80 * a7 * a6 ^ 2 * a5 * a1
    + (62045441155399680 : R) * h ^ 80 * a7 * a6 ^ 2 * a4 * a2
    + (31022720577699840 : R) * h ^ 80 * a7 * a6 ^ 2 * a3 ^ 2
    + (62045441155399680 : R) * h ^ 80 * a7 * a6 * a5 ^ 2 * a2
    + (124090882310799360 : R) * h ^ 80 * a7 * a6 * a5 * a4 * a3
    + (20681813718466560 : R) * h ^ 80 * a7 * a6 * a4 ^ 3
    + (20681813718466560 : R) * h ^ 80 * a7 * a5 ^ 3 * a3
    + (31022720577699840 : R) * h ^ 80 * a7 * a5 ^ 2 * a4 ^ 2
    + (7755680144424960 : R) * h ^ 80 * a6 ^ 4 * a1
    + (31022720577699840 : R) * h ^ 80 * a6 ^ 3 * a5 * a2
    + (31022720577699840 : R) * h ^ 80 * a6 ^ 3 * a4 * a3
    + (46534080866549760 : R) * h ^ 80 * a6 ^ 2 * a5 ^ 2 * a3
    + (46534080866549760 : R) * h ^ 80 * a6 ^ 2 * a5 * a4 ^ 2
    + (31022720577699840 : R) * h ^ 80 * a6 * a5 ^ 3 * a4
    + (1551136028884992 : R) * h ^ 80 * a5 ^ 5


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
