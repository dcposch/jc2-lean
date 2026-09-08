import Fable410ScaleTwoAlignedNinthFacePart01Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Cleared tenth defect of the degree-`3` aligned `(4,10)` row, kept
in factored form through the third through ninth defects `M₂`, `M₄`,
`M₆`, `M₈`, `M₁₀`, `M₁₂`, and `M₁₄`.  Every monomial has exact
`H`-weight `15`; the head is `3932160 p₀ (p₁² + p₀ p₂) H¹⁴`, the
`κ`-module is the single pure-`p₀` term `524288 κ p₀² H¹⁵`, and the
new letter enters at full weight as `-4194304 q₀ H¹⁵`. -/
def alignedTenthDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (3932160 : K[X]) * a0 * a1 ^ 2 * H ^ 14 +
    (3932160 : K[X]) * a0 ^ 2 * a2 * H ^ 14 -
    (4194304 : K[X]) * b0 * H ^ 15 -
    (983040 : K[X]) * a0 ^ 2 * a3 ^ 2 * H ^ 12 -
    (3932160 : K[X]) * a0 * a1 * a2 * a3 * H ^ 12 -
    (983040 : K[X]) * a1 ^ 2 * a2 ^ 2 * H ^ 12 -
    (655360 : K[X]) * a0 * a2 ^ 3 * H ^ 12 -
    (655360 : K[X]) * a1 ^ 3 * a3 * H ^ 12 +
    (983040 : K[X]) * a0 * a1 * a3 ^ 3 * H ^ 10 +
    (1474560 : K[X]) * a0 * a2 ^ 2 * a3 ^ 2 * H ^ 10 +
    (1474560 : K[X]) * a1 ^ 2 * a2 * a3 ^ 2 * H ^ 10 +
    (983040 : K[X]) * a1 * a2 ^ 3 * a3 * H ^ 10 +
    (49152 : K[X]) * a2 ^ 5 * H ^ 10 -
    (614400 : K[X]) * a0 * a2 * a3 ^ 4 * H ^ 8 -
    (307200 : K[X]) * a1 ^ 2 * a3 ^ 4 * H ^ 8 -
    (1228800 : K[X]) * a1 * a2 ^ 2 * a3 ^ 3 * H ^ 8 -
    (307200 : K[X]) * a2 ^ 4 * a3 ^ 2 * H ^ 8 +
    (71680 : K[X]) * a0 * a3 ^ 6 * H ^ 6 +
    (430080 : K[X]) * a1 * a2 * a3 ^ 5 * H ^ 6 +
    (358400 : K[X]) * a2 ^ 3 * a3 ^ 4 * H ^ 6 -
    (46080 : K[X]) * a1 * a3 ^ 7 * H ^ 4 -
    (161280 : K[X]) * a2 ^ 2 * a3 ^ 6 * H ^ 4 +
    (31680 : K[X]) * a2 * a3 ^ 8 * H ^ 2 - (2288 : K[X]) * a3 ^ 10 +
    Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2 * H ^ 15) -
    a3 * alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ -
    ((16 : K[X]) * a2 * H ^ 2 - (4 : K[X]) * a3 ^ 2) *
      alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ -
    ((96 : K[X]) * a1 * H ^ 4 - (24 : K[X]) * a2 * a3 * H ^ 2 +
      (5 : K[X]) * a3 ^ 3) *
      alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ -
    (2048 : K[X]) * a0 * H ^ 6 *
      alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ -
    ((2560 : K[X]) * a0 * a3 * H ^ 6 + (2560 : K[X]) * a1 * a2 * H ^ 6 -
      (960 : K[X]) * a1 * a3 ^ 2 * H ^ 4 -
      (960 : K[X]) * a2 ^ 2 * a3 * H ^ 4 +
      (560 : K[X]) * a2 * a3 ^ 3 * H ^ 2 - (77 : K[X]) * a3 ^ 5) *
      alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ -
    ((24576 : K[X]) * a0 * a2 * H ^ 8 + (12288 : K[X]) * a1 ^ 2 * H ^ 8 -
      (6144 : K[X]) * a0 * a3 ^ 2 * H ^ 6 -
      (12288 : K[X]) * a1 * a2 * a3 * H ^ 6 -
      (2048 : K[X]) * a2 ^ 3 * H ^ 6 +
      (3072 : K[X]) * a1 * a3 ^ 3 * H ^ 4 +
      (4608 : K[X]) * a2 ^ 2 * a3 ^ 2 * H ^ 4 -
      (1920 : K[X]) * a2 * a3 ^ 4 * H ^ 2 + (224 : K[X]) * a3 ^ 6) *
      alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ -
    ((344064 : K[X]) * a0 * a1 * H ^ 10 -
      (86016 : K[X]) * a0 * a2 * a3 * H ^ 8 -
      (43008 : K[X]) * a1 ^ 2 * a3 * H ^ 8 -
      (43008 : K[X]) * a1 * a2 ^ 2 * H ^ 8 +
      (17920 : K[X]) * a0 * a3 ^ 3 * H ^ 6 +
      (53760 : K[X]) * a1 * a2 * a3 ^ 2 * H ^ 6 +
      (17920 : K[X]) * a2 ^ 3 * a3 * H ^ 6 -
      (10080 : K[X]) * a1 * a3 ^ 4 * H ^ 4 -
      (20160 : K[X]) * a2 ^ 2 * a3 ^ 3 * H ^ 4 +
      (6552 : K[X]) * a2 * a3 ^ 5 * H ^ 2 - (663 : K[X]) * a3 ^ 7) *
      alignedThirdDefect410 H a1 a2 a3 b7 κ

end Max11DegreeRoutes
