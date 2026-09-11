import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 12 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock9_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (19303026137235456 : R) * h ^ 78 * a7 * a6 ^ 2 * a1 * b7
    - (22060601299697664 : R) * h ^ 78 * a7 * a6 ^ 2 * a0 * b8
    - (11030300649848832 : R) * h ^ 78 * a7 * a6 * a5 ^ 2 * b4
    - (27575751624622080 : R) * h ^ 78 * a7 * a6 * a5 * a4 * b5
    - (33090901949546496 : R) * h ^ 78 * a7 * a6 * a5 * a3 * b6
    - (38606052274470912 : R) * h ^ 78 * a7 * a6 * a5 * a2 * b7
    - (44121202599395328 : R) * h ^ 78 * a7 * a6 * a5 * a1 * b8
    - (16545450974773248 : R) * h ^ 78 * a7 * a6 * a4 ^ 2 * b6
    - (38606052274470912 : R) * h ^ 78 * a7 * a6 * a4 * a3 * b7
    - (44121202599395328 : R) * h ^ 78 * a7 * a6 * a4 * a2 * b8
    - (22060601299697664 : R) * h ^ 78 * a7 * a6 * a3 ^ 2 * b8
    - (4595958604103680 : R) * h ^ 78 * a7 * a5 ^ 3 * b5
    - (16545450974773248 : R) * h ^ 78 * a7 * a5 ^ 2 * a4 * b6
    - (19303026137235456 : R) * h ^ 78 * a7 * a5 ^ 2 * a3 * b7
    - (22060601299697664 : R) * h ^ 78 * a7 * a5 ^ 2 * a2 * b8
    - (19303026137235456 : R) * h ^ 78 * a7 * a5 * a4 ^ 2 * b7
    - (44121202599395328 : R) * h ^ 78 * a7 * a5 * a4 * a3 * b8
    - (7353533766565888 : R) * h ^ 78 * a7 * a4 ^ 3 * b8
    - (689393790615552 : R) * h ^ 78 * a6 ^ 4 * b3
    - (3676766883282944 : R) * h ^ 78 * a6 ^ 3 * a5 * b4
    - (4595958604103680 : R) * h ^ 78 * a6 ^ 3 * a4 * b5
    - (5515150324924416 : R) * h ^ 78 * a6 ^ 3 * a3 * b6
    - (6434342045745152 : R) * h ^ 78 * a6 ^ 3 * a2 * b7
    - (7353533766565888 : R) * h ^ 78 * a6 ^ 3 * a1 * b8
    - (6893937906155520 : R) * h ^ 78 * a6 ^ 2 * a5 ^ 2 * b5
    - (16545450974773248 : R) * h ^ 78 * a6 ^ 2 * a5 * a4 * b6
    - (19303026137235456 : R) * h ^ 78 * a6 ^ 2 * a5 * a3 * b7
    - (22060601299697664 : R) * h ^ 78 * a6 ^ 2 * a5 * a2 * b8
    - (9651513068617728 : R) * h ^ 78 * a6 ^ 2 * a4 ^ 2 * b7
    - (22060601299697664 : R) * h ^ 78 * a6 ^ 2 * a4 * a3 * b8
    - (5515150324924416 : R) * h ^ 78 * a6 * a5 ^ 3 * b6
    - (19303026137235456 : R) * h ^ 78 * a6 * a5 ^ 2 * a4 * b7
    - (22060601299697664 : R) * h ^ 78 * a6 * a5 ^ 2 * a3 * b8
    - (22060601299697664 : R) * h ^ 78 * a6 * a5 * a4 ^ 2 * b8
    - (1608585511436288 : R) * h ^ 78 * a5 ^ 4 * b7
    - (7353533766565888 : R) * h ^ 78 * a5 ^ 3 * a4 * b8
    - (6980112129982464 : R) * h ^ 79 * a7 ^ 3 * a5 * a0 * lambda
    - (6980112129982464 : R) * h ^ 79 * a7 ^ 3 * a4 * a1 * lambda
    - (6980112129982464 : R) * h ^ 79 * a7 ^ 3 * a3 * a2 * lambda
    - (10470168194973696 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a0 * lambda


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
