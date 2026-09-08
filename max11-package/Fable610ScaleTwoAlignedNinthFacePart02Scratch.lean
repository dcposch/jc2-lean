import Fable610ScaleTwoAlignedEighthFaceScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Cleared ninth defect of the degree-`6` aligned `(6,10)` row, kept
in factored form through the third defect `D`, the fourth defect `E`,
the fifth defect `F`, the sixth defect `G`, the seventh defect `I`,
and the eighth defect `J`.  On the aligned face it is a polynomial
first integral of weight `45/2`. -/
def alignedNinthDefect610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (1813985280 : K[X]) * a0 * a3 * H ^ 21 + (1813985280 : K[X]) * a1 * a2 * H
    ^ 21 - (1632586752 : K[X]) * b1 * H ^ 22 - (604661760 : K[X]) * a0 * a4
    * a5 * H ^ 18 - (604661760 : K[X]) * a1 * a3 * a5 * H ^ 18 - (302330880
    : K[X]) * a1 * a4 ^ 2 * H ^ 18 - (302330880 : K[X]) * a2 ^ 2 * a5 * H ^
    18 - (604661760 : K[X]) * a2 * a3 * a4 * H ^ 18 - (100776960 : K[X]) *
    a3 ^ 3 * H ^ 18 + (134369280 : K[X]) * a0 * a5 ^ 3 * H ^ 15 + (403107840
    : K[X]) * a1 * a4 * a5 ^ 2 * H ^ 15 + (403107840 : K[X]) * a2 * a3 * a5
    ^ 2 * H ^ 15 + (403107840 : K[X]) * a2 * a4 ^ 2 * a5 * H ^ 15 +
    (403107840 : K[X]) * a3 ^ 2 * a4 * a5 * H ^ 15 + (134369280 : K[X]) * a3
    * a4 ^ 3 * H ^ 15 - (78382080 : K[X]) * a1 * a5 ^ 4 * H ^ 12 -
    (313528320 : K[X]) * a2 * a4 * a5 ^ 3 * H ^ 12 - (156764160 : K[X]) * a3
    ^ 2 * a5 ^ 3 * H ^ 12 - (470292480 : K[X]) * a3 * a4 ^ 2 * a5 ^ 2 * H ^
    12 - (78382080 : K[X]) * a4 ^ 4 * a5 * H ^ 12 + (52254720 : K[X]) * a2 *
    a5 ^ 5 * H ^ 9 + (261273600 : K[X]) * a3 * a4 * a5 ^ 4 * H ^ 9 +
    (174182400 : K[X]) * a4 ^ 3 * a5 ^ 3 * H ^ 9 - (37739520 : K[X]) * a3 *
    a5 ^ 6 * H ^ 6 - (113218560 : K[X]) * a4 ^ 2 * a5 ^ 5 * H ^ 6 +
    (28753920 : K[X]) * a4 * a5 ^ 7 * H ^ 3 - (2529280 : K[X]) * a5 ^ 9 +
    Polynomial.C κ * ((80621568 : K[X]) * a0 * a5 * H ^ 20 + (80621568 :
    K[X]) * a1 * a4 * H ^ 20 + (80621568 : K[X]) * a2 * a3 * H ^ 20 -
    (26873856 : K[X]) * a1 * a5 ^ 2 * H ^ 17 - (53747712 : K[X]) * a2 * a4 *
    a5 * H ^ 17 - (26873856 : K[X]) * a3 ^ 2 * a5 * H ^ 17 - (26873856 :
    K[X]) * a3 * a4 ^ 2 * H ^ 17 + (14929920 : K[X]) * a2 * a5 ^ 3 * H ^ 14
    + (44789760 : K[X]) * a3 * a4 * a5 ^ 2 * H ^ 14 + (14929920 : K[X]) * a4
    ^ 3 * a5 * H ^ 14 - (9953280 : K[X]) * a3 * a5 ^ 4 * H ^ 11 - (19906560
    : K[X]) * a4 ^ 2 * a5 ^ 3 * H ^ 11 + (7299072 : K[X]) * a4 * a5 ^ 5 * H
    ^ 8 - (811008 : K[X]) * a5 ^ 7 * H ^ 5) - ((23514624 : K[X]) * a0 * H ^
    15 + (3919104 : K[X]) * a1 * a5 * H ^ 12 + (3919104 : K[X]) * a2 * a4 *
    H ^ 12 + (1959552 : K[X]) * a3 ^ 2 * H ^ 12 - (1632960 : K[X]) * a2 * a5
    ^ 2 * H ^ 9 - (3265920 : K[X]) * a3 * a4 * a5 * H ^ 9 - (544320 : K[X])
    * a4 ^ 3 * H ^ 9 + (997920 : K[X]) * a3 * a5 ^ 3 * H ^ 6 + (1496880 :
    K[X]) * a4 ^ 2 * a5 ^ 2 * H ^ 6 - (706860 : K[X]) * a4 * a5 ^ 4 * H ^ 3
    + (90321 : K[X]) * a5 ^ 6) * alignedThirdDefect610 H a3 a4 a5 b7 κ -
    (3359232 : K[X]) * a1 * H ^ 12 * alignedFourthDefect610 H a2 a3 a4 a5 b6
    b7 κ - ((233280 : K[X]) * a2 * H ^ 9 - (38880 : K[X]) * a3 * a5 * H ^ 6
    - (19440 : K[X]) * a4 ^ 2 * H ^ 6 + (22680 : K[X]) * a4 * a5 ^ 2 * H ^ 3
    - (4095 : K[X]) * a5 ^ 4) * alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6
    b7 κ - ((10368 : K[X]) * a3 * H ^ 6 - (3456 : K[X]) * a4 * a5 * H ^ 3 +
    (768 : K[X]) * a5 ^ 3) * alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5
    b6 b7 κ - ((324 : K[X]) * a4 * H ^ 3 - (81 : K[X]) * a5 ^ 2) *
    alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ - (36 :
    K[X]) * a5 * alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6
    b7 κ

end Max11DegreeRoutes
