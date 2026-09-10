import Fable810ScaleZeroFourteenthDefectPart16Scratch

/-! Part 17 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock14_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (13510798882111488 : R) * h ^ 94 * a2 * a1 * b8
    - (5224879255191552 : R) * h ^ 95 * a7 * a3 * a0 * lambda
    - (5224879255191552 : R) * h ^ 95 * a7 * a2 * a1 * lambda
    - (5224879255191552 : R) * h ^ 95 * a6 * a4 * a0 * lambda
    - (5224879255191552 : R) * h ^ 95 * a6 * a3 * a1 * lambda
    - (2612439627595776 : R) * h ^ 95 * a6 * a2 ^ 2 * lambda
    - (2612439627595776 : R) * h ^ 95 * a5 ^ 2 * a0 * lambda
    - (5224879255191552 : R) * h ^ 95 * a5 * a4 * a1 * lambda
    - (5224879255191552 : R) * h ^ 95 * a5 * a3 * a2 * lambda
    - (2612439627595776 : R) * h ^ 95 * a4 ^ 2 * a2 * lambda
    - (2612439627595776 : R) * h ^ 95 * a4 * a3 ^ 2 * lambda
    + (4222124650659840 : R) * h ^ 96 * a7 * a2 * a0
    + (2111062325329920 : R) * h ^ 96 * a7 * a1 ^ 2
    + (23221685578629120 : R) * h ^ 96 * a6 * a3 * a0
    + (23221685578629120 : R) * h ^ 96 * a6 * a2 * a1
    + (23221685578629120 : R) * h ^ 96 * a5 * a4 * a0
    + (23221685578629120 : R) * h ^ 96 * a5 * a3 * a1
    + (11610842789314560 : R) * h ^ 96 * a5 * a2 ^ 2
    + (11610842789314560 : R) * h ^ 96 * a4 ^ 2 * a1
    + (23221685578629120 : R) * h ^ 96 * a4 * a3 * a2
    + (3870280929771520 : R) * h ^ 96 * a3 ^ 3
    + (4503599627370496 : R) * h ^ 102 * a2 * b1
    + (9007199254740992 : R) * h ^ 102 * a1 * b2
    + (13510798882111488 : R) * h ^ 102 * a0 * b3
    + (3799912185593856 : R) * h ^ 103 * a2 * a0 * lambda
    + (1899956092796928 : R) * h ^ 103 * a1 ^ 2 * lambda
    - (16888498602639360 : R) * h ^ 104 * a1 * a0


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
