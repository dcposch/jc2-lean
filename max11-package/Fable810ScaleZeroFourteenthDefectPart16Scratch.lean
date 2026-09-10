import Fable810ScaleZeroFourteenthDefectPart15Scratch

/-! Part 16 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock13_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (14513553486643200 : R) * h ^ 88 * a7 * a5 ^ 2 * a0
    - (29027106973286400 : R) * h ^ 88 * a7 * a5 * a4 * a1
    - (29027106973286400 : R) * h ^ 88 * a7 * a5 * a3 * a2
    - (14513553486643200 : R) * h ^ 88 * a7 * a4 ^ 2 * a2
    - (14513553486643200 : R) * h ^ 88 * a7 * a4 * a3 ^ 2
    - (27575751624622080 : R) * h ^ 88 * a6 ^ 2 * a5 * a0
    - (27575751624622080 : R) * h ^ 88 * a6 ^ 2 * a4 * a1
    - (27575751624622080 : R) * h ^ 88 * a6 ^ 2 * a3 * a2
    - (27575751624622080 : R) * h ^ 88 * a6 * a5 ^ 2 * a1
    - (55151503249244160 : R) * h ^ 88 * a6 * a5 * a4 * a2
    - (27575751624622080 : R) * h ^ 88 * a6 * a5 * a3 ^ 2
    - (27575751624622080 : R) * h ^ 88 * a6 * a4 ^ 2 * a3
    - (9191917208207360 : R) * h ^ 88 * a5 ^ 3 * a2
    - (27575751624622080 : R) * h ^ 88 * a5 ^ 2 * a4 * a3
    - (9191917208207360 : R) * h ^ 88 * a5 * a4 ^ 3
    - (1688849860263936 : R) * h ^ 94 * a7 * a3 * b1
    - (3377699720527872 : R) * h ^ 94 * a7 * a2 * b2
    - (5066549580791808 : R) * h ^ 94 * a7 * a1 * b3
    - (6755399441055744 : R) * h ^ 94 * a7 * a0 * b4
    - (1688849860263936 : R) * h ^ 94 * a6 * a4 * b1
    - (3377699720527872 : R) * h ^ 94 * a6 * a3 * b2
    - (5066549580791808 : R) * h ^ 94 * a6 * a2 * b3
    - (6755399441055744 : R) * h ^ 94 * a6 * a1 * b4
    - (8444249301319680 : R) * h ^ 94 * a6 * a0 * b5
    - (844424930131968 : R) * h ^ 94 * a5 ^ 2 * b1
    - (3377699720527872 : R) * h ^ 94 * a5 * a4 * b2
    - (5066549580791808 : R) * h ^ 94 * a5 * a3 * b3
    - (6755399441055744 : R) * h ^ 94 * a5 * a2 * b4
    - (8444249301319680 : R) * h ^ 94 * a5 * a1 * b5
    - (10133099161583616 : R) * h ^ 94 * a5 * a0 * b6
    - (2533274790395904 : R) * h ^ 94 * a4 ^ 2 * b3
    - (6755399441055744 : R) * h ^ 94 * a4 * a3 * b4
    - (8444249301319680 : R) * h ^ 94 * a4 * a2 * b5
    - (10133099161583616 : R) * h ^ 94 * a4 * a1 * b6
    - (11821949021847552 : R) * h ^ 94 * a4 * a0 * b7
    - (4222124650659840 : R) * h ^ 94 * a3 ^ 2 * b5
    - (10133099161583616 : R) * h ^ 94 * a3 * a2 * b6
    - (11821949021847552 : R) * h ^ 94 * a3 * a1 * b7
    - (13510798882111488 : R) * h ^ 94 * a3 * a0 * b8
    - (5910974510923776 : R) * h ^ 94 * a2 ^ 2 * b7


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
