import Fable610ScaleTwoAlignedTenthFaceScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 1600000000 in
/-- Cleared eleventh defect of the degree-`4` aligned `(6,10)` row,
kept in factored form through the third defect `D`, the fifth defect
`F`, the sixth defect `G`, the seventh defect `I`, the eighth defect
`J`, and the ninth defect `L` — in the minimal gauge the fourth defect
`E` and the tenth defect `Ω` do not enter, and the raw head carries no
`q`-coefficient at all.  On the aligned face it is a squared
polynomial first integral of weight `55/2`. -/
def alignedEleventhDefect610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    K[X] :=
  ((522427760640 : K[X]) * a0 * a1 * H ^ 27 - (174142586880 : K[X]) * a0
    * a2 * a5 * H ^ 24 - (174142586880 : K[X]) * a0 * a3 * a4 * H ^ 24 +
    (116095057920 : K[X]) * a0 * a3 * a5 ^ 2 * H ^ 21 + (116095057920 :
    K[X]) * a0 * a4 ^ 2 * a5 * H ^ 21 - (90296156160 : K[X]) * a0 * a4 *
    a5 ^ 3 * H ^ 18 + (15049359360 : K[X]) * a0 * a5 ^ 5 * H ^ 15 -
    (87071293440 : K[X]) * a1 ^ 2 * a5 * H ^ 24 - (174142586880 : K[X]) *
    a1 * a2 * a4 * H ^ 24 + (116095057920 : K[X]) * a1 * a2 * a5 ^ 2 * H ^
    21 - (87071293440 : K[X]) * a1 * a3 ^ 2 * H ^ 24 + (232190115840 :
    K[X]) * a1 * a3 * a4 * a5 * H ^ 21 - (90296156160 : K[X]) * a1 * a3 *
    a5 ^ 3 * H ^ 18 + (38698352640 : K[X]) * a1 * a4 ^ 3 * H ^ 21 -
    (135444234240 : K[X]) * a1 * a4 ^ 2 * a5 ^ 2 * H ^ 18 + (75246796800 :
    K[X]) * a1 * a4 * a5 ^ 4 * H ^ 15 - (10868981760 : K[X]) * a1 * a5 ^ 6
    * H ^ 12 - (87071293440 : K[X]) * a2 ^ 2 * a3 * H ^ 24 + (116095057920
    : K[X]) * a2 ^ 2 * a4 * a5 * H ^ 21 - (45148078080 : K[X]) * a2 ^ 2 *
    a5 ^ 3 * H ^ 18 + (116095057920 : K[X]) * a2 * a3 ^ 2 * a5 * H ^ 21 +
    (116095057920 : K[X]) * a2 * a3 * a4 ^ 2 * H ^ 21 - (270888468480 :
    K[X]) * a2 * a3 * a4 * a5 ^ 2 * H ^ 18 + (75246796800 : K[X]) * a2 *
    a3 * a5 ^ 4 * H ^ 15 - (90296156160 : K[X]) * a2 * a4 ^ 3 * a5 * H ^
    18 + (150493593600 : K[X]) * a2 * a4 ^ 2 * a5 ^ 3 * H ^ 15 -
    (65213890560 : K[X]) * a2 * a4 * a5 ^ 5 * H ^ 12 + (8281128960 : K[X])
    * a2 * a5 ^ 7 * H ^ 9 + (38698352640 : K[X]) * a3 ^ 3 * a4 * H ^ 21 -
    (45148078080 : K[X]) * a3 ^ 3 * a5 ^ 2 * H ^ 18 - (135444234240 :
    K[X]) * a3 ^ 2 * a4 ^ 2 * a5 * H ^ 18 + (150493593600 : K[X]) * a3 ^ 2
    * a4 * a5 ^ 3 * H ^ 15 - (32606945280 : K[X]) * a3 ^ 2 * a5 ^ 5 * H ^
    12 - (22574039040 : K[X]) * a3 * a4 ^ 4 * H ^ 18 + (150493593600 :
    K[X]) * a3 * a4 ^ 3 * a5 ^ 2 * H ^ 15 - (163034726400 : K[X]) * a3 *
    a4 ^ 2 * a5 ^ 4 * H ^ 12 + (57967902720 : K[X]) * a3 * a4 * a5 ^ 6 * H
    ^ 9 - (6555893760 : K[X]) * a3 * a5 ^ 8 * H ^ 6 + (15049359360 : K[X])
    * a4 ^ 5 * a5 * H ^ 15 - (54344908800 : K[X]) * a4 ^ 4 * a5 ^ 3 * H ^
    12 + (57967902720 : K[X]) * a4 ^ 3 * a5 ^ 5 * H ^ 9 - (26223575040 :
    K[X]) * a4 ^ 2 * a5 ^ 7 * H ^ 6 + (5341839360 : K[X]) * a4 * a5 ^ 9 *
    H ^ 3 - (404684800 : K[X]) * a5 ^ 11 + Polynomial.C κ * ((23219011584
    : K[X]) * a0 * a3 * H ^ 26 - (15479341056 : K[X]) * a0 * a4 * a5 * H ^
    23 + (4299816960 : K[X]) * a0 * a5 ^ 3 * H ^ 20 + (23219011584 : K[X])
    * a1 * a2 * H ^ 26 - (15479341056 : K[X]) * a1 * a3 * a5 * H ^ 23 -
    (7739670528 : K[X]) * a1 * a4 ^ 2 * H ^ 23 + (12899450880 : K[X]) * a1
    * a4 * a5 ^ 2 * H ^ 20 - (2866544640 : K[X]) * a1 * a5 ^ 4 * H ^ 17 -
    (7739670528 : K[X]) * a2 ^ 2 * a5 * H ^ 23 - (15479341056 : K[X]) * a2
    * a3 * a4 * H ^ 23 + (12899450880 : K[X]) * a2 * a3 * a5 ^ 2 * H ^ 20
    + (12899450880 : K[X]) * a2 * a4 ^ 2 * a5 * H ^ 20 - (11466178560 :
    K[X]) * a2 * a4 * a5 ^ 3 * H ^ 17 + (2102132736 : K[X]) * a2 * a5 ^ 5
    * H ^ 14 - (2579890176 : K[X]) * a3 ^ 3 * H ^ 23 + (12899450880 :
    K[X]) * a3 ^ 2 * a4 * a5 * H ^ 20 - (5733089280 : K[X]) * a3 ^ 2 * a5
    ^ 3 * H ^ 17 + (4299816960 : K[X]) * a3 * a4 ^ 3 * H ^ 20 -
    (17199267840 : K[X]) * a3 * a4 ^ 2 * a5 ^ 2 * H ^ 17 + (10510663680 :
    K[X]) * a3 * a4 * a5 ^ 4 * H ^ 14 - (1634992128 : K[X]) * a3 * a5 ^ 6
    * H ^ 11 - (2866544640 : K[X]) * a4 ^ 4 * a5 * H ^ 17 + (7007109120 :
    K[X]) * a4 ^ 3 * a5 ^ 3 * H ^ 14 - (4904976384 : K[X]) * a4 ^ 2 * a5 ^
    5 * H ^ 11 + (1323565056 : K[X]) * a4 * a5 ^ 7 * H ^ 8 - (122552320 :
    K[X]) * a5 ^ 9 * H ^ 5)) - ((1128701952 : K[X]) * a0 * a4 * H ^ 18 -
    (470292480 : K[X]) * a0 * a5 ^ 2 * H ^ 15 + (1128701952 : K[X]) * a1 *
    a3 * H ^ 18 - (940584960 : K[X]) * a1 * a4 * a5 * H ^ 15 + (287400960
    : K[X]) * a1 * a5 ^ 3 * H ^ 12 + (564350976 : K[X]) * a2 ^ 2 * H ^ 18
    - (940584960 : K[X]) * a2 * a3 * a5 * H ^ 15 - (470292480 : K[X]) * a2
    * a4 ^ 2 * H ^ 15 + (862202880 : K[X]) * a2 * a4 * a5 ^ 2 * H ^ 12 -
    (203575680 : K[X]) * a2 * a5 ^ 4 * H ^ 9 - (470292480 : K[X]) * a3 ^ 2
    * a4 * H ^ 15 + (431101440 : K[X]) * a3 ^ 2 * a5 ^ 2 * H ^ 12 +
    (862202880 : K[X]) * a3 * a4 ^ 2 * a5 * H ^ 12 - (814302720 : K[X]) *
    a3 * a4 * a5 ^ 3 * H ^ 9 + (156074688 : K[X]) * a3 * a5 ^ 5 * H ^ 6 +
    (71850240 : K[X]) * a4 ^ 4 * H ^ 12 - (407151360 : K[X]) * a4 ^ 3 * a5
    ^ 2 * H ^ 9 + (390186720 : K[X]) * a4 ^ 2 * a5 ^ 4 * H ^ 6 -
    (125726832 : K[X]) * a4 * a5 ^ 6 * H ^ 3 + (13096545 : K[X]) * a5 ^ 8)
    * alignedThirdDefect610 H a3 a4 a5 b7 κ - ((67184640 : K[X]) * a0 * H
    ^ 15 - (11197440 : K[X]) * a1 * a5 * H ^ 12 - (11197440 : K[X]) * a2 *
    a4 * H ^ 12 + (6531840 : K[X]) * a2 * a5 ^ 2 * H ^ 9 - (5598720 :
    K[X]) * a3 ^ 2 * H ^ 12 + (13063680 : K[X]) * a3 * a4 * a5 * H ^ 9 -
    (4717440 : K[X]) * a3 * a5 ^ 3 * H ^ 6 + (2177280 : K[X]) * a4 ^ 3 * H
    ^ 9 - (7076160 : K[X]) * a4 ^ 2 * a5 ^ 2 * H ^ 6 + (3734640 : K[X]) *
    a4 * a5 ^ 4 * H ^ 3 - (518700 : K[X]) * a5 ^ 6) *
    alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ - ((2985984 : K[X])
    * a1 * H ^ 12 - (995328 : K[X]) * a2 * a5 * H ^ 9 - (995328 : K[X]) *
    a3 * a4 * H ^ 9 + (663552 : K[X]) * a3 * a5 ^ 2 * H ^ 6 + (663552 :
    K[X]) * a4 ^ 2 * a5 * H ^ 6 - (516096 : K[X]) * a4 * a5 ^ 3 * H ^ 3 +
    (86016 : K[X]) * a5 ^ 5) * alignedSixthDefect610 H a0 a1 a2 a3 a4 a5
    b4 b5 b6 b7 κ - ((93312 : K[X]) * a2 * H ^ 9 - (46656 : K[X]) * a3 *
    a5 * H ^ 6 - (23328 : K[X]) * a4 ^ 2 * H ^ 6 + (34992 : K[X]) * a4 *
    a5 ^ 2 * H ^ 3 - (7290 : K[X]) * a5 ^ 4) * alignedSeventhDefect610 H
    a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ - ((10368 : K[X]) * a3 * H ^ 6 -
    (6912 : K[X]) * a4 * a5 * H ^ 3 + (1920 : K[X]) * a5 ^ 3) *
    alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 κ - ((48
    : K[X]) * a4 * H ^ 3 - (20 : K[X]) * a5 ^ 2) * alignedNinthDefect610 H
    a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ

end Max11DegreeRoutes
