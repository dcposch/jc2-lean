import Fable410ScaleTwoAlignedNinthFacePart08Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Cleared nonsquare-core form of the tenth defect relation:
cancelling `H¹⁰` from `M₁₆ = κ₉ H¹⁵` on `p₃ = H g`, `M₂ = 0`,
`M₄ = κ₃ H⁶`, `M₆ = 0`, `M₈ = κ₅ H⁹`, `M₁₀ = 0`, `M₁₂ = κ₇ H¹²`,
`M₁₄ = 0` exposes the same core in `g` carried by `H²` against the
explicit quotient — no parity kill: `κ₉` survives the nonsquare
chamber. -/
theorem alignedNonsquareTenth_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₅ κ₇ κ₉ : K}
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
      0)
    (hM16 : alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₉ * H ^ 15) :
    (16 : K[X]) * ((143 : K[X]) * g ^ 4 - (264 : K[X]) * a2 * g ^ 2 +
            (48 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (15360 : K[X]) * H * a1 * g *
          ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
      H ^ 2 *
        (((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
              g ^ 2 - (61440 : K[X]) * a1 ^ 2) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
          (245760 : K[X]) * a1 ^ 2 * g ^ 2 * (g ^ 2 - (4 : K[X]) * a2) +
          H * (((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
              g * a1 * (g ^ 2 - (4 : K[X]) * a2) -
            (655360 : K[X]) * a1 ^ 3 * g) +
          H ^ 2 *
            (((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
                a1 ^ 2 +
              (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
                Polynomial.C κ₇ * (4 : K[X]) -
                (983040 : K[X]) * a0 ^ 2) *
                (g ^ 2 - (4 : K[X]) * a2)) +
          H ^ 3 *
            (Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
              Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
              Polynomial.C κ₉ - (4194304 : K[X]) * b0)) := by
  have hM16' := hM16
  simp only [alignedTenthDefect410] at hM16'
  rw [hM140, hM12, hM100, hM8, hM60, hM4, hM20, hg] at hM16'
  apply mul_left_cancel₀ (pow_ne_zero 10 hH)
  linear_combination -hM16'

end Max11DegreeRoutes
