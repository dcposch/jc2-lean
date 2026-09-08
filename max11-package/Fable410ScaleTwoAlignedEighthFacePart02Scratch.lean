import Fable410ScaleTwoAlignedEighthFacePart01Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Cleared ninth defect of the degree-`4` aligned `(4,10)` row, kept
in factored form through the third through eighth defects `M₂`, `M₄`,
`M₆`, `M₈`, `M₁₀`, and `M₁₂`.  Every monomial has exact `H`-weight
`27/2`; the head is the weighted cubic
`327680 (3 p₀² p₃ + 6 p₀ p₁ p₂ + p₁³) H¹²`, and the `κ`-module is the
single term `262144 κ p₀ p₁ H¹³`. -/
def alignedNinthDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (983040 : K[X]) * a0 ^ 2 * a3 * H ^ 12 -
    (1048576 : K[X]) * b1 * H ^ 13 +
    (1966080 : K[X]) * a0 * a1 * a2 * H ^ 12 +
    (327680 : K[X]) * a1 ^ 3 * H ^ 12 -
    (491520 : K[X]) * a0 * a1 * a3 ^ 2 * H ^ 10 -
    (491520 : K[X]) * a0 * a2 ^ 2 * a3 * H ^ 10 -
    (491520 : K[X]) * a1 ^ 2 * a2 * a3 * H ^ 10 -
    (163840 : K[X]) * a1 * a2 ^ 3 * H ^ 10 +
    (245760 : K[X]) * a0 * a2 * a3 ^ 3 * H ^ 8 +
    (122880 : K[X]) * a1 ^ 2 * a3 ^ 3 * H ^ 8 +
    (368640 : K[X]) * a1 * a2 ^ 2 * a3 ^ 2 * H ^ 8 +
    (61440 : K[X]) * a2 ^ 4 * a3 * H ^ 8 -
    (30720 : K[X]) * a0 * a3 ^ 5 * H ^ 6 -
    (153600 : K[X]) * a1 * a2 * a3 ^ 4 * H ^ 6 -
    (102400 : K[X]) * a2 ^ 3 * a3 ^ 3 * H ^ 6 +
    (17920 : K[X]) * a1 * a3 ^ 6 * H ^ 4 +
    (53760 : K[X]) * a2 ^ 2 * a3 ^ 5 * H ^ 4 -
    (11520 : K[X]) * a2 * a3 ^ 7 * H ^ 2 + (880 : K[X]) * a3 ^ 9 +
    Polynomial.C κ * ((262144 : K[X]) * a0 * a1 * H ^ 13) -
    (4 : K[X]) * a3 *
      alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ -
    ((24 : K[X]) * a2 * H ^ 2 - (3 : K[X]) * a3 ^ 2) *
      alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ -
    (512 : K[X]) * a1 * H ^ 4 *
      alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ -
    ((2560 : K[X]) * a0 * H ^ 6 + (640 : K[X]) * a1 * a3 * H ^ 4 +
      (320 : K[X]) * a2 ^ 2 * H ^ 4 - (240 : K[X]) * a2 * a3 ^ 2 * H ^ 2 +
      (35 : K[X]) * a3 ^ 4) *
      alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ -
    ((6144 : K[X]) * a0 * a3 * H ^ 6 + (6144 : K[X]) * a1 * a2 * H ^ 6 -
      (1536 : K[X]) * a1 * a3 ^ 2 * H ^ 4 -
      (1536 : K[X]) * a2 ^ 2 * a3 * H ^ 4 +
      (768 : K[X]) * a2 * a3 ^ 3 * H ^ 2 - (96 : K[X]) * a3 ^ 5) *
      alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ -
    ((86016 : K[X]) * a0 * a2 * H ^ 8 + (43008 : K[X]) * a1 ^ 2 * H ^ 8 -
      (10752 : K[X]) * a0 * a3 ^ 2 * H ^ 6 -
      (21504 : K[X]) * a1 * a2 * a3 * H ^ 6 -
      (3584 : K[X]) * a2 ^ 3 * H ^ 6 +
      (4480 : K[X]) * a1 * a3 ^ 3 * H ^ 4 +
      (6720 : K[X]) * a2 ^ 2 * a3 ^ 2 * H ^ 4 -
      (2520 : K[X]) * a2 * a3 ^ 4 * H ^ 2 + (273 : K[X]) * a3 ^ 6) *
      alignedThirdDefect410 H a1 a2 a3 b7 κ

end Max11DegreeRoutes
