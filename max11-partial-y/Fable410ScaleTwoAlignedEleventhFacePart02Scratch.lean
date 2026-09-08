import Fable410ScaleTwoAlignedEleventhFacePart01Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Cleared twelfth defect of the degree-`1` aligned `(4,10)` row,
kept in factored form through the third through ninth defects.  Every
monomial has exact `H`-weight `18`.  The head is the first weighted
`p₀`-CUBIC block, PURE in the `p`-letters: no `q`-letter and no
`κ`-module at all, and neither `M₈` nor `M₁₆` nor `M₁₈` appears among
the corrections — `q₀` and `q₄` drop out of the defect entirely. -/
def alignedTwelfthDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (838860800 : K[X]) * H ^ 18 * a0 ^ 3 -
    (104857600 : K[X]) * H ^ 16 * a1 ^ 4 -
    (1258291200 : K[X]) * H ^ 16 * a0 * a1 ^ 2 * a2 -
    (629145600 : K[X]) * H ^ 16 * a0 ^ 2 * a2 ^ 2 -
    (629145600 : K[X]) * H ^ 16 * a0 ^ 2 * a1 * a3 +
    (314572800 : K[X]) * H ^ 14 * a1 ^ 2 * a2 ^ 3 +
    (524288000 : K[X]) * H ^ 14 * a1 ^ 3 * a2 * a3 +
    (157286400 : K[X]) * H ^ 14 * a0 * a2 ^ 4 +
    (1572864000 : K[X]) * H ^ 14 * a0 * a1 * a2 ^ 2 * a3 +
    (629145600 : K[X]) * H ^ 14 * a0 * a1 ^ 2 * a3 ^ 2 +
    (629145600 : K[X]) * H ^ 14 * a0 ^ 2 * a2 * a3 ^ 2 -
    (13107200 : K[X]) * H ^ 12 * a2 ^ 6 -
    (353894400 : K[X]) * H ^ 12 * a1 * a2 ^ 4 * a3 -
    (943718400 : K[X]) * H ^ 12 * a1 ^ 2 * a2 ^ 2 * a3 ^ 2 -
    (183500800 : K[X]) * H ^ 12 * a1 ^ 3 * a3 ^ 3 -
    (629145600 : K[X]) * H ^ 12 * a0 * a2 ^ 3 * a3 ^ 2 -
    (1101004800 : K[X]) * H ^ 12 * a0 * a1 * a2 * a3 ^ 3 -
    (117964800 : K[X]) * H ^ 12 * a0 ^ 2 * a3 ^ 4 +
    (117964800 : K[X]) * H ^ 10 * a2 ^ 5 * a3 ^ 2 +
    (720896000 : K[X]) * H ^ 10 * a1 * a2 ^ 3 * a3 ^ 3 +
    (491520000 : K[X]) * H ^ 10 * a1 ^ 2 * a2 * a3 ^ 4 +
    (491520000 : K[X]) * H ^ 10 * a0 * a2 ^ 2 * a3 ^ 4 +
    (176947200 : K[X]) * H ^ 10 * a0 * a1 * a3 ^ 5 -
    (200704000 : K[X]) * H ^ 8 * a2 ^ 4 * a3 ^ 4 -
    (447283200 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 ^ 5 -
    (68812800 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 6 -
    (137625600 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 6 +
    (137625600 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 6 +
    (110592000 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 7 +
    (12902400 : K[X]) * H ^ 6 * a0 * a3 ^ 8 -
    (45619200 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 8 -
    (9574400 : K[X]) * H ^ 4 * a1 * a3 ^ 9 +
    (7321600 : K[X]) * H ^ 2 * a2 * a3 ^ 10 -
    (457600 : K[X]) * a3 ^ 12 -
    ((640 : K[X]) * H ^ 4 * a1 -
      (320 : K[X]) * H ^ 2 * a2 * a3 +
      (80 : K[X]) * a3 ^ 3) *
      alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ -
    ((10240 : K[X]) * H ^ 6 * a0 -
      (2560 : K[X]) * H ^ 4 * a2 ^ 2 -
      (2560 : K[X]) * H ^ 4 * a1 * a3 +
      (2560 : K[X]) * H ^ 2 * a2 * a3 ^ 2 -
      (480 : K[X]) * a3 ^ 4) *
      alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ -
    (-(15360 : K[X]) * H ^ 6 * a1 * a2 +
      (7680 : K[X]) * H ^ 4 * a2 ^ 2 * a3 +
      (5760 : K[X]) * H ^ 4 * a1 * a3 ^ 2 -
      (4800 : K[X]) * H ^ 2 * a2 * a3 ^ 3 +
      (720 : K[X]) * a3 ^ 5) *
      alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ -
    ((1638400 : K[X]) * H ^ 10 * a0 * a1 -
      (614400 : K[X]) * H ^ 8 * a1 * a2 ^ 2 -
      (409600 : K[X]) * H ^ 8 * a1 ^ 2 * a3 -
      (819200 : K[X]) * H ^ 8 * a0 * a2 * a3 +
      (307200 : K[X]) * H ^ 6 * a2 ^ 3 * a3 +
      (768000 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 2 +
      (204800 : K[X]) * H ^ 6 * a0 * a3 ^ 3 -
      (358400 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 3 -
      (156800 : K[X]) * H ^ 4 * a1 * a3 ^ 4 +
      (123200 : K[X]) * H ^ 2 * a2 * a3 ^ 5 -
      (13200 : K[X]) * a3 ^ 7) *
      alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ -
    ((7864320 : K[X]) * H ^ 12 * a0 ^ 2 -
      (3932160 : K[X]) * H ^ 10 * a1 ^ 2 * a2 -
      (3932160 : K[X]) * H ^ 10 * a0 * a2 ^ 2 -
      (3932160 : K[X]) * H ^ 10 * a0 * a1 * a3 +
      (491520 : K[X]) * H ^ 8 * a2 ^ 4 +
      (4915200 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 +
      (1966080 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 2 +
      (3932160 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 2 -
      (1966080 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 2 -
      (3440640 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 3 -
      (737280 : K[X]) * H ^ 6 * a0 * a3 ^ 4 +
      (1536000 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 4 +
      (552960 : K[X]) * H ^ 4 * a1 * a3 ^ 5 -
      (430080 : K[X]) * H ^ 2 * a2 * a3 ^ 6 +
      (40320 : K[X]) * a3 ^ 8) *
      alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ -
    (-(9175040 : K[X]) * H ^ 12 * a1 ^ 3 -
      (55050240 : K[X]) * H ^ 12 * a0 * a1 * a2 +
      (11468800 : K[X]) * H ^ 10 * a1 * a2 ^ 3 +
      (27525120 : K[X]) * H ^ 10 * a1 ^ 2 * a2 * a3 +
      (27525120 : K[X]) * H ^ 10 * a0 * a2 ^ 2 * a3 +
      (20643840 : K[X]) * H ^ 10 * a0 * a1 * a3 ^ 2 -
      (5734400 : K[X]) * H ^ 8 * a2 ^ 4 * a3 -
      (30105600 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 ^ 2 -
      (8601600 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 3 -
      (17203200 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 3 +
      (10752000 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 3 +
      (14515200 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 4 +
      (2580480 : K[X]) * H ^ 6 * a0 * a3 ^ 5 -
      (6289920 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 5 -
      (1921920 : K[X]) * H ^ 4 * a1 * a3 ^ 6 +
      (1485120 : K[X]) * H ^ 2 * a2 * a3 ^ 7 -
      (123760 : K[X]) * a3 ^ 9) *
      alignedThirdDefect410 H a1 a2 a3 b7 κ

end Max11DegreeRoutes
