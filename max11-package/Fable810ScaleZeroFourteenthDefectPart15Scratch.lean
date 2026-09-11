import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 15 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock12_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (13933011347177472 : R) * h ^ 86 * a6 * a4 * a3 * b6
    + (16255179905040384 : R) * h ^ 86 * a6 * a4 * a2 * b7
    + (18577348462903296 : R) * h ^ 86 * a6 * a4 * a1 * b8
    + (8127589952520192 : R) * h ^ 86 * a6 * a3 ^ 2 * b7
    + (18577348462903296 : R) * h ^ 86 * a6 * a3 * a2 * b8
    + (1548112371908608 : R) * h ^ 86 * a5 ^ 3 * b4
    + (5805421394657280 : R) * h ^ 86 * a5 ^ 2 * a4 * b5
    + (6966505673588736 : R) * h ^ 86 * a5 ^ 2 * a3 * b6
    + (8127589952520192 : R) * h ^ 86 * a5 ^ 2 * a2 * b7
    + (9288674231451648 : R) * h ^ 86 * a5 ^ 2 * a1 * b8
    + (6966505673588736 : R) * h ^ 86 * a5 * a4 ^ 2 * b6
    + (16255179905040384 : R) * h ^ 86 * a5 * a4 * a3 * b7
    + (18577348462903296 : R) * h ^ 86 * a5 * a4 * a2 * b8
    + (9288674231451648 : R) * h ^ 86 * a5 * a3 ^ 2 * b8
    + (2709196650840064 : R) * h ^ 86 * a4 ^ 3 * b7
    + (9288674231451648 : R) * h ^ 86 * a4 ^ 2 * a3 * b8
    + (6204544115539968 : R) * h ^ 87 * a7 ^ 2 * a4 * a0 * lambda
    + (6204544115539968 : R) * h ^ 87 * a7 ^ 2 * a3 * a1 * lambda
    + (3102272057769984 : R) * h ^ 87 * a7 ^ 2 * a2 ^ 2 * lambda
    + (12409088231079936 : R) * h ^ 87 * a7 * a6 * a5 * a0 * lambda
    + (12409088231079936 : R) * h ^ 87 * a7 * a6 * a4 * a1 * lambda
    + (12409088231079936 : R) * h ^ 87 * a7 * a6 * a3 * a2 * lambda
    + (6204544115539968 : R) * h ^ 87 * a7 * a5 ^ 2 * a1 * lambda
    + (12409088231079936 : R) * h ^ 87 * a7 * a5 * a4 * a2 * lambda
    + (6204544115539968 : R) * h ^ 87 * a7 * a5 * a3 ^ 2 * lambda
    + (6204544115539968 : R) * h ^ 87 * a7 * a4 ^ 2 * a3 * lambda
    + (2068181371846656 : R) * h ^ 87 * a6 ^ 3 * a0 * lambda
    + (6204544115539968 : R) * h ^ 87 * a6 ^ 2 * a5 * a1 * lambda
    + (6204544115539968 : R) * h ^ 87 * a6 ^ 2 * a4 * a2 * lambda
    + (3102272057769984 : R) * h ^ 87 * a6 ^ 2 * a3 ^ 2 * lambda
    + (6204544115539968 : R) * h ^ 87 * a6 * a5 ^ 2 * a2 * lambda
    + (12409088231079936 : R) * h ^ 87 * a6 * a5 * a4 * a3 * lambda
    + (2068181371846656 : R) * h ^ 87 * a6 * a4 ^ 3 * lambda
    + (2068181371846656 : R) * h ^ 87 * a5 ^ 3 * a3 * lambda
    + (3102272057769984 : R) * h ^ 87 * a5 ^ 2 * a4 ^ 2 * lambda
    - (1451355348664320 : R) * h ^ 88 * a7 ^ 2 * a3 * a0
    - (1451355348664320 : R) * h ^ 88 * a7 ^ 2 * a2 * a1
    - (29027106973286400 : R) * h ^ 88 * a7 * a6 * a4 * a0
    - (29027106973286400 : R) * h ^ 88 * a7 * a6 * a3 * a1
    - (14513553486643200 : R) * h ^ 88 * a7 * a6 * a2 ^ 2


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
