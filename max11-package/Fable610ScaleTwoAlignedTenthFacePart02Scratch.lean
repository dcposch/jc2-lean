import Fable610ScaleTwoAlignedNinthFacePart02Scratch
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 1600000000 in
/-- Cleared tenth defect of the degree-`5` aligned `(6,10)` row, kept
in factored form through the third defect `D`, the fourth defect `E`,
the fifth defect `F`, the sixth defect `G`, the seventh defect `I`,
the eighth defect `J`, and the ninth defect `L`.  On the aligned face
it is a polynomial first integral of weight `25`. -/
def alignedTenthDefect610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    K[X] :=
  (10883911680 : K[X]) * a0 * a2 * H ^ 24 - (3627970560 : K[X]) * a0 *
    a3 * a5 * H ^ 21 - (1813985280 : K[X]) * a0 * a4 ^ 2 * H ^ 21 +
    (2418647040 : K[X]) * a0 * a4 * a5 ^ 2 * H ^ 18 - (470292480 : K[X]) *
    a0 * a5 ^ 4 * H ^ 15 + (5441955840 : K[X]) * a1 ^ 2 * H ^ 24 -
    (3627970560 : K[X]) * a1 * a2 * a5 * H ^ 21 - (3627970560 : K[X]) * a1
    * a3 * a4 * H ^ 21 + (2418647040 : K[X]) * a1 * a3 * a5 ^ 2 * H ^ 18 +
    (2418647040 : K[X]) * a1 * a4 ^ 2 * a5 * H ^ 18 - (1881169920 : K[X])
    * a1 * a4 * a5 ^ 3 * H ^ 15 + (313528320 : K[X]) * a1 * a5 ^ 5 * H ^
    12 - (1813985280 : K[X]) * a2 ^ 2 * a4 * H ^ 21 + (1209323520 : K[X])
    * a2 ^ 2 * a5 ^ 2 * H ^ 18 - (1813985280 : K[X]) * a2 * a3 ^ 2 * H ^
    21 + (4837294080 : K[X]) * a2 * a3 * a4 * a5 * H ^ 18 - (1881169920 :
    K[X]) * a2 * a3 * a5 ^ 3 * H ^ 15 + (806215680 : K[X]) * a2 * a4 ^ 3 *
    H ^ 18 - (2821754880 : K[X]) * a2 * a4 ^ 2 * a5 ^ 2 * H ^ 15 +
    (1567641600 : K[X]) * a2 * a4 * a5 ^ 4 * H ^ 12 - (226437120 : K[X]) *
    a2 * a5 ^ 6 * H ^ 9 + (806215680 : K[X]) * a3 ^ 3 * a5 * H ^ 18 +
    (1209323520 : K[X]) * a3 ^ 2 * a4 ^ 2 * H ^ 18 - (2821754880 : K[X]) *
    a3 ^ 2 * a4 * a5 ^ 2 * H ^ 15 + (783820800 : K[X]) * a3 ^ 2 * a5 ^ 4 *
    H ^ 12 - (1881169920 : K[X]) * a3 * a4 ^ 3 * a5 * H ^ 15 + (3135283200
    : K[X]) * a3 * a4 ^ 2 * a5 ^ 3 * H ^ 12 - (1358622720 : K[X]) * a3 *
    a4 * a5 ^ 5 * H ^ 9 + (172523520 : K[X]) * a3 * a5 ^ 7 * H ^ 6 -
    (94058496 : K[X]) * a4 ^ 5 * H ^ 15 + (783820800 : K[X]) * a4 ^ 4 * a5
    ^ 2 * H ^ 12 - (1132185600 : K[X]) * a4 ^ 3 * a5 ^ 4 * H ^ 9 +
    (603832320 : K[X]) * a4 ^ 2 * a5 ^ 6 * H ^ 6 - (136581120 : K[X]) * a4
    * a5 ^ 8 * H ^ 3 + (11128832 : K[X]) * a5 ^ 10 - (9795520512 : K[X]) *
    b0 * H ^ 25 + Polynomial.C κ * ((483729408 : K[X]) * a0 * a4 * H ^ 23
    - (161243136 : K[X]) * a0 * a5 ^ 2 * H ^ 20 + (483729408 : K[X]) * a1
    * a3 * H ^ 23 - (322486272 : K[X]) * a1 * a4 * a5 * H ^ 20 + (89579520
    : K[X]) * a1 * a5 ^ 3 * H ^ 17 + (241864704 : K[X]) * a2 ^ 2 * H ^ 23
    - (322486272 : K[X]) * a2 * a3 * a5 * H ^ 20 - (161243136 : K[X]) * a2
    * a4 ^ 2 * H ^ 20 + (268738560 : K[X]) * a2 * a4 * a5 ^ 2 * H ^ 17 -
    (59719680 : K[X]) * a2 * a5 ^ 4 * H ^ 14 - (161243136 : K[X]) * a3 ^ 2
    * a4 * H ^ 20 + (134369280 : K[X]) * a3 ^ 2 * a5 ^ 2 * H ^ 17 +
    (268738560 : K[X]) * a3 * a4 ^ 2 * a5 * H ^ 17 - (238878720 : K[X]) *
    a3 * a4 * a5 ^ 3 * H ^ 14 + (43794432 : K[X]) * a3 * a5 ^ 5 * H ^ 11 +
    (22394880 : K[X]) * a4 ^ 4 * H ^ 17 - (119439360 : K[X]) * a4 ^ 3 * a5
    ^ 2 * H ^ 14 + (109486080 : K[X]) * a4 ^ 2 * a5 ^ 4 * H ^ 11 -
    (34062336 : K[X]) * a4 * a5 ^ 6 * H ^ 8 + (3446784 : K[X]) * a5 ^ 8 *
    H ^ 5) - ((23514624 : K[X]) * a0 * a5 * H ^ 15 + (23514624 : K[X]) *
    a1 * a4 * H ^ 15 - (9797760 : K[X]) * a1 * a5 ^ 2 * H ^ 12 + (23514624
    : K[X]) * a2 * a3 * H ^ 15 - (19595520 : K[X]) * a2 * a4 * a5 * H ^ 12
    + (5987520 : K[X]) * a2 * a5 ^ 3 * H ^ 9 - (9797760 : K[X]) * a3 ^ 2 *
    a5 * H ^ 12 - (9797760 : K[X]) * a3 * a4 ^ 2 * H ^ 12 + (17962560 :
    K[X]) * a3 * a4 * a5 ^ 2 * H ^ 9 - (4241160 : K[X]) * a3 * a5 ^ 4 * H
    ^ 6 + (5987520 : K[X]) * a4 ^ 3 * a5 * H ^ 9 - (8482320 : K[X]) * a4 ^
    2 * a5 ^ 3 * H ^ 6 + (3251556 : K[X]) * a4 * a5 ^ 5 * H ^ 3 - (374187
    : K[X]) * a5 ^ 7) * alignedThirdDefect610 H a3 a4 a5 b7 κ - ((20155392
    : K[X]) * a0 * H ^ 15) * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ
    - ((1399680 : K[X]) * a1 * H ^ 12 - (233280 : K[X]) * a2 * a5 * H ^ 9
    - (233280 : K[X]) * a3 * a4 * H ^ 9 + (136080 : K[X]) * a3 * a5 ^ 2 *
    H ^ 6 + (136080 : K[X]) * a4 ^ 2 * a5 * H ^ 6 - (98280 : K[X]) * a4 *
    a5 ^ 3 * H ^ 3 + (15561 : K[X]) * a5 ^ 5) * alignedFifthDefect610 H a1
    a2 a3 a4 a5 b5 b6 b7 κ - ((62208 : K[X]) * a2 * H ^ 9 - (20736 : K[X])
    * a3 * a5 * H ^ 6 - (10368 : K[X]) * a4 ^ 2 * H ^ 6 + (13824 : K[X]) *
    a4 * a5 ^ 2 * H ^ 3 - (2688 : K[X]) * a5 ^ 4) * alignedSixthDefect610
    H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ - ((1944 : K[X]) * a3 * H ^ 6 - (972
    : K[X]) * a4 * a5 * H ^ 3 + (243 : K[X]) * a5 ^ 3) *
    alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ - ((216 :
    K[X]) * a4 * H ^ 3 - (72 : K[X]) * a5 ^ 2) * alignedEighthDefect610 H
    a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 κ - a5 * alignedNinthDefect610 H
    a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ

end Max11DegreeRoutes
