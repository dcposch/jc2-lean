import Fable810ScaleZeroThirteenthDefectPart03Scratch

/-! Part 4 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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


def localClearedFourteenthDefectBlock1_810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (12897786789888 : R) * h ^ 38 * a7 ^ 6 * a6 * a4 * b8
    - (6448893394944 : R) * h ^ 38 * a7 ^ 6 * a5 ^ 2 * b8
    - (11285563441152 : R) * h ^ 38 * a7 ^ 5 * a6 ^ 3 * b7
    - (38693360369664 : R) * h ^ 38 * a7 ^ 5 * a6 ^ 2 * a5 * b8
    - (16122233487360 : R) * h ^ 38 * a7 ^ 4 * a6 ^ 4 * b8
    - (485826232320 : R) * h ^ 39 * a7 ^ 8 * a3 * lambda
    - (3886609858560 : R) * h ^ 39 * a7 ^ 7 * a6 * a4 * lambda
    - (1943304929280 : R) * h ^ 39 * a7 ^ 7 * a5 ^ 2 * lambda
    - (13603134504960 : R) * h ^ 39 * a7 ^ 6 * a6 ^ 2 * a5 * lambda
    - (6801567252480 : R) * h ^ 39 * a7 ^ 5 * a6 ^ 4 * lambda
    - (431845539840 : R) * h ^ 40 * a7 ^ 8 * a2
    - (863691079680 : R) * h ^ 40 * a7 ^ 7 * a6 * a3
    - (863691079680 : R) * h ^ 40 * a7 ^ 7 * a5 * a4
    + (6045837557760 : R) * h ^ 40 * a7 ^ 6 * a6 ^ 2 * a4
    + (6045837557760 : R) * h ^ 40 * a7 ^ 6 * a6 * a5 ^ 2
    + (30229187788800 : R) * h ^ 40 * a7 ^ 5 * a6 ^ 3 * a5
    + (12091675115520 : R) * h ^ 40 * a7 ^ 4 * a6 ^ 5
    + (106300440576 : R) * h ^ 46 * a7 ^ 7 * b3
    + (992137445376 : R) * h ^ 46 * a7 ^ 6 * a6 * b4
    + (1240171806720 : R) * h ^ 46 * a7 ^ 6 * a5 * b5
    + (1488206168064 : R) * h ^ 46 * a7 ^ 6 * a4 * b6
    + (1736240529408 : R) * h ^ 46 * a7 ^ 6 * a3 * b7
    + (1984274890752 : R) * h ^ 46 * a7 ^ 6 * a2 * b8
    + (3720515420160 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 2 * b5
    + (8929237008384 : R) * h ^ 46 * a7 ^ 5 * a6 * a5 * b6
    + (10417443176448 : R) * h ^ 46 * a7 ^ 5 * a6 * a4 * b7
    + (11905649344512 : R) * h ^ 46 * a7 ^ 5 * a6 * a3 * b8
    + (5208721588224 : R) * h ^ 46 * a7 ^ 5 * a5 ^ 2 * b7
    + (11905649344512 : R) * h ^ 46 * a7 ^ 5 * a5 * a4 * b8
    + (7441030840320 : R) * h ^ 46 * a7 ^ 4 * a6 ^ 3 * b6
    + (26043607941120 : R) * h ^ 46 * a7 ^ 4 * a6 ^ 2 * a5 * b7
    + (29764123361280 : R) * h ^ 46 * a7 ^ 4 * a6 ^ 2 * a4 * b8
    + (29764123361280 : R) * h ^ 46 * a7 ^ 4 * a6 * a5 ^ 2 * b8
    + (8681202647040 : R) * h ^ 46 * a7 ^ 3 * a6 ^ 4 * b7
    + (39685497815040 : R) * h ^ 46 * a7 ^ 3 * a6 ^ 3 * a5 * b8
    + (5952824672256 : R) * h ^ 46 * a7 ^ 2 * a6 ^ 5 * b8
    + (518214647808 : R) * h ^ 47 * a7 ^ 7 * a2 * lambda
    + (3627502534656 : R) * h ^ 47 * a7 ^ 6 * a6 * a3 * lambda
    + (3627502534656 : R) * h ^ 47 * a7 ^ 6 * a5 * a4 * lambda
    + (10882507603968 : R) * h ^ 47 * a7 ^ 5 * a6 ^ 2 * a4 * lambda


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
