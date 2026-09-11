import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 11 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock8_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (98884921841418240 : R) * h ^ 72 * a7 ^ 2 * a6 * a5 * a4 ^ 2
    - (32961640613806080 : R) * h ^ 72 * a7 ^ 2 * a5 ^ 3 * a4
    - (25205960469381120 : R) * h ^ 72 * a7 * a6 ^ 4 * a2
    - (100823841877524480 : R) * h ^ 72 * a7 * a6 ^ 3 * a5 * a3
    - (50411920938762240 : R) * h ^ 72 * a7 * a6 ^ 3 * a4 ^ 2
    - (151235762816286720 : R) * h ^ 72 * a7 * a6 ^ 2 * a5 ^ 2 * a4
    - (25205960469381120 : R) * h ^ 72 * a7 * a6 * a5 ^ 4
    - (6786220126371840 : R) * h ^ 72 * a6 ^ 5 * a3
    - (33931100631859200 : R) * h ^ 72 * a6 ^ 4 * a5 * a4
    - (22620733754572800 : R) * h ^ 72 * a6 ^ 3 * a5 ^ 3
    - (919191720820736 : R) * h ^ 78 * a7 ^ 3 * a5 * b1
    - (1838383441641472 : R) * h ^ 78 * a7 ^ 3 * a4 * b2
    - (2757575162462208 : R) * h ^ 78 * a7 ^ 3 * a3 * b3
    - (3676766883282944 : R) * h ^ 78 * a7 ^ 3 * a2 * b4
    - (4595958604103680 : R) * h ^ 78 * a7 ^ 3 * a1 * b5
    - (5515150324924416 : R) * h ^ 78 * a7 ^ 3 * a0 * b6
    - (1378787581231104 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * b1
    - (5515150324924416 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * b2
    - (8272725487386624 : R) * h ^ 78 * a7 ^ 2 * a6 * a4 * b3
    - (11030300649848832 : R) * h ^ 78 * a7 ^ 2 * a6 * a3 * b4
    - (13787875812311040 : R) * h ^ 78 * a7 ^ 2 * a6 * a2 * b5
    - (16545450974773248 : R) * h ^ 78 * a7 ^ 2 * a6 * a1 * b6
    - (19303026137235456 : R) * h ^ 78 * a7 ^ 2 * a6 * a0 * b7
    - (4136362743693312 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 2 * b3
    - (11030300649848832 : R) * h ^ 78 * a7 ^ 2 * a5 * a4 * b4
    - (13787875812311040 : R) * h ^ 78 * a7 ^ 2 * a5 * a3 * b5
    - (16545450974773248 : R) * h ^ 78 * a7 ^ 2 * a5 * a2 * b6
    - (19303026137235456 : R) * h ^ 78 * a7 ^ 2 * a5 * a1 * b7
    - (22060601299697664 : R) * h ^ 78 * a7 ^ 2 * a5 * a0 * b8
    - (6893937906155520 : R) * h ^ 78 * a7 ^ 2 * a4 ^ 2 * b5
    - (16545450974773248 : R) * h ^ 78 * a7 ^ 2 * a4 * a3 * b6
    - (19303026137235456 : R) * h ^ 78 * a7 ^ 2 * a4 * a2 * b7
    - (22060601299697664 : R) * h ^ 78 * a7 ^ 2 * a4 * a1 * b8
    - (9651513068617728 : R) * h ^ 78 * a7 ^ 2 * a3 ^ 2 * b7
    - (22060601299697664 : R) * h ^ 78 * a7 ^ 2 * a3 * a2 * b8
    - (1838383441641472 : R) * h ^ 78 * a7 * a6 ^ 3 * b2
    - (8272725487386624 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 * b3
    - (11030300649848832 : R) * h ^ 78 * a7 * a6 ^ 2 * a4 * b4
    - (13787875812311040 : R) * h ^ 78 * a7 * a6 ^ 2 * a3 * b5
    - (16545450974773248 : R) * h ^ 78 * a7 * a6 ^ 2 * a2 * b6


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
