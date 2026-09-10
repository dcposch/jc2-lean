import Fable810ScaleZeroFourteenthDefectPart03Scratch

/-! Part 4 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock1_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (32665500873916416 : R) * h ^ 38 * a7 ^ 7 * a6 * a4 * b8
    + (16332750436958208 : R) * h ^ 38 * a7 ^ 7 * a5 ^ 2 * b8
    + (33346032142123008 : R) * h ^ 38 * a7 ^ 6 * a6 ^ 3 * b7
    + (114329253058707456 : R) * h ^ 38 * a7 ^ 6 * a6 ^ 2 * a5 * b8
    + (57164626529353728 : R) * h ^ 38 * a7 ^ 5 * a6 ^ 4 * b8
    + (1068646757105664 : R) * h ^ 39 * a7 ^ 9 * a3 * lambda
    + (9617820813950976 : R) * h ^ 39 * a7 ^ 8 * a6 * a4 * lambda
    + (4808910406975488 : R) * h ^ 39 * a7 ^ 8 * a5 ^ 2 * lambda
    + (38471283255803904 : R) * h ^ 39 * a7 ^ 7 * a6 ^ 2 * a5 * lambda
    + (22441581899218944 : R) * h ^ 39 * a7 ^ 6 * a6 ^ 4 * lambda
    + (992441432801280 : R) * h ^ 40 * a7 ^ 9 * a2
    + (3189990319718400 : R) * h ^ 40 * a7 ^ 8 * a6 * a3
    + (3189990319718400 : R) * h ^ 40 * a7 ^ 8 * a5 * a4
    - (10207969023098880 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 2 * a4
    - (10207969023098880 : R) * h ^ 40 * a7 ^ 7 * a6 * a5 ^ 2
    - (77410431758499840 : R) * h ^ 40 * a7 ^ 6 * a6 ^ 3 * a5
    - (39300680738930688 : R) * h ^ 40 * a7 ^ 5 * a6 ^ 5
    - (207619708944384 : R) * h ^ 46 * a7 ^ 8 * b3
    - (2214610228740096 : R) * h ^ 46 * a7 ^ 7 * a6 * b4
    - (2768262785925120 : R) * h ^ 46 * a7 ^ 7 * a5 * b5
    - (3321915343110144 : R) * h ^ 46 * a7 ^ 7 * a4 * b6
    - (3875567900295168 : R) * h ^ 46 * a7 ^ 7 * a3 * b7
    - (4429220457480192 : R) * h ^ 46 * a7 ^ 7 * a2 * b8
    - (9688919750737920 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 2 * b5
    - (23253407401771008 : R) * h ^ 46 * a7 ^ 6 * a6 * a5 * b6
    - (27128975302066176 : R) * h ^ 46 * a7 ^ 6 * a6 * a4 * b7
    - (31004543202361344 : R) * h ^ 46 * a7 ^ 6 * a6 * a3 * b8
    - (13564487651033088 : R) * h ^ 46 * a7 ^ 6 * a5 ^ 2 * b7
    - (31004543202361344 : R) * h ^ 46 * a7 ^ 6 * a5 * a4 * b8
    - (23253407401771008 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 3 * b6
    - (81386925906198528 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 2 * a5 * b7
    - (93013629607084032 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 2 * a4 * b8
    - (93013629607084032 : R) * h ^ 46 * a7 ^ 5 * a6 * a5 ^ 2 * b8
    - (33911219127582720 : R) * h ^ 46 * a7 ^ 4 * a6 ^ 4 * b7
    - (155022716011806720 : R) * h ^ 46 * a7 ^ 4 * a6 ^ 3 * a5 * b8
    - (31004543202361344 : R) * h ^ 46 * a7 ^ 3 * a6 ^ 5 * b8
    - (1148396515098624 : R) * h ^ 47 * a7 ^ 8 * a2 * lambda
    - (9187172120788992 : R) * h ^ 47 * a7 ^ 7 * a6 * a3 * lambda
    - (9187172120788992 : R) * h ^ 47 * a7 ^ 7 * a5 * a4 * lambda
    - (32155102422761472 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 2 * a4 * lambda


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
