import Fable410ScaleTwoAlignedEighthFacePart10Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Cleared nonsquare-core form of the ninth defect relation:
cancelling `H⁹` from the parity kill `M₁₄ ≡ 0` on `p₃ = H g`,
`M₂ = 0`, `M₄ = κ₃ H⁶`, `M₆ = 0`, `M₈ = κ₅ H⁹`, `M₁₀ = 0`,
`M₁₂ = κ₇ H¹²` exposes the same core in `g` carried by `H²` against
the explicit quotient. -/
theorem alignedNonsquareNinth_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₅ κ₇ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM20 : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM60 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0)
    (hM8 : alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 9)
    (hM100 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ = 0)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM140 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      0) :
    (80 : K[X]) * g * ((11 : K[X]) * g ^ 2 - (12 : K[X]) * a2) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (2560 : K[X]) * H * a1 *
          ((7 : K[X]) * g ^ 2 - (4 : K[X]) * a2) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
      H ^ 2 *
        (((30720 : K[X]) * a0 - Polynomial.C κ₃ * (96 : K[X])) * g *
            (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
          (122880 : K[X]) * a1 ^ 2 * g * (g ^ 2 - (4 : K[X]) * a2) +
          H * (((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
              a1 * (g ^ 2 - (4 : K[X]) * a2) -
            (327680 : K[X]) * a1 ^ 3) +
          H ^ 2 *
            ((1048576 : K[X]) * b1 + Polynomial.C κ₇ * ((4 : K[X]) * g) +
              Polynomial.C κ₅ * ((512 : K[X]) * a1) +
              Polynomial.C κ₃ * ((6144 : K[X]) * a0 * g) -
              (983040 : K[X]) * a0 ^ 2 * g -
              Polynomial.C κ * ((262144 : K[X]) * a0 * a1))) := by
  have hM14' := hM140
  simp only [alignedNinthDefect410] at hM14'
  rw [hM12, hM100, hM8, hM60, hM4, hM20, hg] at hM14'
  apply mul_left_cancel₀ (pow_ne_zero 9 hH)
  linear_combination hM14'

end Max11DegreeRoutes
