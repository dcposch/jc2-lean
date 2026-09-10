import Fable810ScaleZeroThirteenthDefectPart11Scratch

/-! Part 12 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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

section Depression810FourteenthClearing

variable {F : Type*} [Field F] [CharZero F]


def localClearedFourteenthDefectBlock9_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2319282339840 : R) * h ^ 79 * a7 ^ 2 * a3 * a2 * lambda
    + (2319282339840 : R) * h ^ 79 * a7 * a6 ^ 2 * a0 * lambda
    + (4638564679680 : R) * h ^ 79 * a7 * a6 * a5 * a1 * lambda
    + (4638564679680 : R) * h ^ 79 * a7 * a6 * a4 * a2 * lambda
    + (2319282339840 : R) * h ^ 79 * a7 * a6 * a3 ^ 2 * lambda
    + (2319282339840 : R) * h ^ 79 * a7 * a5 ^ 2 * a2 * lambda
    + (4638564679680 : R) * h ^ 79 * a7 * a5 * a4 * a3 * lambda
    + (773094113280 : R) * h ^ 79 * a7 * a4 ^ 3 * lambda
    + (773094113280 : R) * h ^ 79 * a6 ^ 3 * a1 * lambda
    + (2319282339840 : R) * h ^ 79 * a6 ^ 2 * a5 * a2 * lambda
    + (2319282339840 : R) * h ^ 79 * a6 ^ 2 * a4 * a3 * lambda
    + (2319282339840 : R) * h ^ 79 * a6 * a5 ^ 2 * a3 * lambda
    + (2319282339840 : R) * h ^ 79 * a6 * a5 * a4 ^ 2 * lambda
    + (773094113280 : R) * h ^ 79 * a5 ^ 3 * a4 * lambda
    - (1030792151040 : R) * h ^ 80 * a7 ^ 2 * a4 * a0
    - (1030792151040 : R) * h ^ 80 * a7 ^ 2 * a3 * a1
    - (515396075520 : R) * h ^ 80 * a7 ^ 2 * a2 ^ 2
    - (11338713661440 : R) * h ^ 80 * a7 * a6 * a5 * a0
    - (11338713661440 : R) * h ^ 80 * a7 * a6 * a4 * a1
    - (11338713661440 : R) * h ^ 80 * a7 * a6 * a3 * a2
    - (5669356830720 : R) * h ^ 80 * a7 * a5 ^ 2 * a1
    - (11338713661440 : R) * h ^ 80 * a7 * a5 * a4 * a2
    - (5669356830720 : R) * h ^ 80 * a7 * a5 * a3 ^ 2
    - (5669356830720 : R) * h ^ 80 * a7 * a4 ^ 2 * a3
    - (3435973836800 : R) * h ^ 80 * a6 ^ 3 * a0
    - (10307921510400 : R) * h ^ 80 * a6 ^ 2 * a5 * a1
    - (10307921510400 : R) * h ^ 80 * a6 ^ 2 * a4 * a2
    - (5153960755200 : R) * h ^ 80 * a6 ^ 2 * a3 ^ 2
    - (10307921510400 : R) * h ^ 80 * a6 * a5 ^ 2 * a2
    - (20615843020800 : R) * h ^ 80 * a6 * a5 * a4 * a3
    - (3435973836800 : R) * h ^ 80 * a6 * a4 ^ 3
    - (3435973836800 : R) * h ^ 80 * a5 ^ 3 * a3
    - (5153960755200 : R) * h ^ 80 * a5 ^ 2 * a4 ^ 2
    - (549755813888 : R) * h ^ 86 * a7 * a4 * b1
    - (1099511627776 : R) * h ^ 86 * a7 * a3 * b2
    - (1649267441664 : R) * h ^ 86 * a7 * a2 * b3
    - (2199023255552 : R) * h ^ 86 * a7 * a1 * b4
    - (2748779069440 : R) * h ^ 86 * a7 * a0 * b5
    - (549755813888 : R) * h ^ 86 * a6 * a5 * b1
    - (1099511627776 : R) * h ^ 86 * a6 * a4 * b2


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
