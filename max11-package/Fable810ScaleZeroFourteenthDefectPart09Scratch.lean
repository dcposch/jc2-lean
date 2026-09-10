import Fable810ScaleZeroFourteenthDefectPart08Scratch

/-! Part 9 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock6_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (18613632346619904 : R) * h ^ 70 * a7 ^ 3 * a6 * a2 * b6
    + (21715904404389888 : R) * h ^ 70 * a7 ^ 3 * a6 * a1 * b7
    + (24818176462159872 : R) * h ^ 70 * a7 ^ 3 * a6 * a0 * b8
    + (6204544115539968 : R) * h ^ 70 * a7 ^ 3 * a5 ^ 2 * b4
    + (15511360288849920 : R) * h ^ 70 * a7 ^ 3 * a5 * a4 * b5
    + (18613632346619904 : R) * h ^ 70 * a7 ^ 3 * a5 * a3 * b6
    + (21715904404389888 : R) * h ^ 70 * a7 ^ 3 * a5 * a2 * b7
    + (24818176462159872 : R) * h ^ 70 * a7 ^ 3 * a5 * a1 * b8
    + (9306816173309952 : R) * h ^ 70 * a7 ^ 3 * a4 ^ 2 * b6
    + (21715904404389888 : R) * h ^ 70 * a7 ^ 3 * a4 * a3 * b7
    + (24818176462159872 : R) * h ^ 70 * a7 ^ 3 * a4 * a2 * b8
    + (12409088231079936 : R) * h ^ 70 * a7 ^ 3 * a3 ^ 2 * b8
    + (4653408086654976 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * b3
    + (18613632346619904 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a5 * b4
    + (23267040433274880 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a4 * b5
    + (27920448519929856 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a3 * b6
    + (32573856606584832 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a2 * b7
    + (37227264693239808 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a1 * b8
    + (23267040433274880 : R) * h ^ 70 * a7 ^ 2 * a6 * a5 ^ 2 * b5
    + (55840897039859712 : R) * h ^ 70 * a7 ^ 2 * a6 * a5 * a4 * b6
    + (65147713213169664 : R) * h ^ 70 * a7 ^ 2 * a6 * a5 * a3 * b7
    + (74454529386479616 : R) * h ^ 70 * a7 ^ 2 * a6 * a5 * a2 * b8
    + (32573856606584832 : R) * h ^ 70 * a7 ^ 2 * a6 * a4 ^ 2 * b7
    + (74454529386479616 : R) * h ^ 70 * a7 ^ 2 * a6 * a4 * a3 * b8
    + (9306816173309952 : R) * h ^ 70 * a7 ^ 2 * a5 ^ 3 * b6
    + (32573856606584832 : R) * h ^ 70 * a7 ^ 2 * a5 ^ 2 * a4 * b7
    + (37227264693239808 : R) * h ^ 70 * a7 ^ 2 * a5 ^ 2 * a3 * b8
    + (37227264693239808 : R) * h ^ 70 * a7 ^ 2 * a5 * a4 ^ 2 * b8
    + (3102272057769984 : R) * h ^ 70 * a7 * a6 ^ 4 * b4
    + (15511360288849920 : R) * h ^ 70 * a7 * a6 ^ 3 * a5 * b5
    + (18613632346619904 : R) * h ^ 70 * a7 * a6 ^ 3 * a4 * b6
    + (21715904404389888 : R) * h ^ 70 * a7 * a6 ^ 3 * a3 * b7
    + (24818176462159872 : R) * h ^ 70 * a7 * a6 ^ 3 * a2 * b8
    + (27920448519929856 : R) * h ^ 70 * a7 * a6 ^ 2 * a5 ^ 2 * b6
    + (65147713213169664 : R) * h ^ 70 * a7 * a6 ^ 2 * a5 * a4 * b7
    + (74454529386479616 : R) * h ^ 70 * a7 * a6 ^ 2 * a5 * a3 * b8
    + (37227264693239808 : R) * h ^ 70 * a7 * a6 ^ 2 * a4 ^ 2 * b8
    + (21715904404389888 : R) * h ^ 70 * a7 * a6 * a5 ^ 3 * b7
    + (74454529386479616 : R) * h ^ 70 * a7 * a6 * a5 ^ 2 * a4 * b8
    + (6204544115539968 : R) * h ^ 70 * a7 * a5 ^ 4 * b8


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
