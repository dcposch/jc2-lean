import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 14 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFifteenthDefectBlock11_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1161084278931456 : R) * h ^ 86 * a7 ^ 2 * a4 * b1
    + (2322168557862912 : R) * h ^ 86 * a7 ^ 2 * a3 * b2
    + (3483252836794368 : R) * h ^ 86 * a7 ^ 2 * a2 * b3
    + (4644337115725824 : R) * h ^ 86 * a7 ^ 2 * a1 * b4
    + (5805421394657280 : R) * h ^ 86 * a7 ^ 2 * a0 * b5
    + (2322168557862912 : R) * h ^ 86 * a7 * a6 * a5 * b1
    + (4644337115725824 : R) * h ^ 86 * a7 * a6 * a4 * b2
    + (6966505673588736 : R) * h ^ 86 * a7 * a6 * a3 * b3
    + (9288674231451648 : R) * h ^ 86 * a7 * a6 * a2 * b4
    + (11610842789314560 : R) * h ^ 86 * a7 * a6 * a1 * b5
    + (13933011347177472 : R) * h ^ 86 * a7 * a6 * a0 * b6
    + (2322168557862912 : R) * h ^ 86 * a7 * a5 ^ 2 * b2
    + (6966505673588736 : R) * h ^ 86 * a7 * a5 * a4 * b3
    + (9288674231451648 : R) * h ^ 86 * a7 * a5 * a3 * b4
    + (11610842789314560 : R) * h ^ 86 * a7 * a5 * a2 * b5
    + (13933011347177472 : R) * h ^ 86 * a7 * a5 * a1 * b6
    + (16255179905040384 : R) * h ^ 86 * a7 * a5 * a0 * b7
    + (4644337115725824 : R) * h ^ 86 * a7 * a4 ^ 2 * b4
    + (11610842789314560 : R) * h ^ 86 * a7 * a4 * a3 * b5
    + (13933011347177472 : R) * h ^ 86 * a7 * a4 * a2 * b6
    + (16255179905040384 : R) * h ^ 86 * a7 * a4 * a1 * b7
    + (18577348462903296 : R) * h ^ 86 * a7 * a4 * a0 * b8
    + (6966505673588736 : R) * h ^ 86 * a7 * a3 ^ 2 * b6
    + (16255179905040384 : R) * h ^ 86 * a7 * a3 * a2 * b7
    + (18577348462903296 : R) * h ^ 86 * a7 * a3 * a1 * b8
    + (9288674231451648 : R) * h ^ 86 * a7 * a2 ^ 2 * b8
    + (387028092977152 : R) * h ^ 86 * a6 ^ 3 * b1
    + (2322168557862912 : R) * h ^ 86 * a6 ^ 2 * a5 * b2
    + (3483252836794368 : R) * h ^ 86 * a6 ^ 2 * a4 * b3
    + (4644337115725824 : R) * h ^ 86 * a6 ^ 2 * a3 * b4
    + (5805421394657280 : R) * h ^ 86 * a6 ^ 2 * a2 * b5
    + (6966505673588736 : R) * h ^ 86 * a6 ^ 2 * a1 * b6
    + (8127589952520192 : R) * h ^ 86 * a6 ^ 2 * a0 * b7
    + (3483252836794368 : R) * h ^ 86 * a6 * a5 ^ 2 * b3
    + (9288674231451648 : R) * h ^ 86 * a6 * a5 * a4 * b4
    + (11610842789314560 : R) * h ^ 86 * a6 * a5 * a3 * b5
    + (13933011347177472 : R) * h ^ 86 * a6 * a5 * a2 * b6
    + (16255179905040384 : R) * h ^ 86 * a6 * a5 * a1 * b7
    + (18577348462903296 : R) * h ^ 86 * a6 * a5 * a0 * b8
    + (5805421394657280 : R) * h ^ 86 * a6 * a4 ^ 2 * b5


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
