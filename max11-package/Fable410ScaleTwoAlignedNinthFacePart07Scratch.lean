import Fable410ScaleTwoAlignedNinthFacePart06Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Cleared square-core form of the tenth defect relation: cancelling
`h₀²⁰` from `M₁₆ = κ₉ H¹⁵` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
`M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`,
`M₁₄ = μ₄ h₀²⁷` exposes the `h₀`-free core
`16 (143 u⁴ - 264 p₂ u² + 48 p₂²) (u² - 4 p₂)³
+ 15360 h₀² p₁ u (3 u² - 4 p₂) (u² - 4 p₂)²` carried by `h₀³` against
the explicit quotient, whose leading block is the μ-loaded septic
`663 u⁷ - 6552 p₂ u⁵ + 20160 p₂² u³ - 17920 p₂³ u`. -/
theorem alignedSquareTenth_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ κ₉ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp3 : a3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H a1 a2 a3 b7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ =
      Polynomial.C μ₂ * h0 ^ 15)
    (hM8 : alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 9)
    (hM10 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₃ * h0 ^ 21)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM14 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₄ * h0 ^ 27)
    (hM16 : alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₉ * H ^ 15) :
    (16 : K[X]) * ((143 : K[X]) * u ^ 4 - (264 : K[X]) * a2 * u ^ 2 +
            (48 : K[X]) * a2 ^ 2) * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (15360 : K[X]) * h0 ^ 2 * a1 * u *
          ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
      h0 ^ 3 *
        (Polynomial.C μ *
            ((663 : K[X]) * u ^ 7 - (6552 : K[X]) * a2 * u ^ 5 +
              (20160 : K[X]) * a2 ^ 2 * u ^ 3 -
              (17920 : K[X]) * a2 ^ 3 * u) +
          h0 * (((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
              (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
            (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
                u ^ 2 - (61440 : K[X]) * a1 ^ 2) *
              (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
            (245760 : K[X]) * a1 ^ 2 * u ^ 2 *
              (u ^ 2 - (4 : K[X]) * a2)) +
          h0 ^ 2 *
            (Polynomial.C μ *
                (a1 * ((10080 : K[X]) * u ^ 4 -
                  (53760 : K[X]) * a2 * u ^ 2 +
                  (43008 : K[X]) * a2 ^ 2)) +
              Polynomial.C μ₂ *
                (u * ((77 : K[X]) * u ^ 4 - (560 : K[X]) * a2 * u ^ 2 +
                  (960 : K[X]) * a2 ^ 2))) +
          h0 ^ 3 *
            (((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
                a1 * u * (u ^ 2 - (4 : K[X]) * a2) -
              (655360 : K[X]) * a1 ^ 3 * u) +
          h0 ^ 4 *
            (Polynomial.C μ *
                ((86016 : K[X]) * a0 * a2 * u -
                  (17920 : K[X]) * a0 * u ^ 3 +
                  (43008 : K[X]) * a1 ^ 2 * u) +
              Polynomial.C μ₂ *
                ((960 : K[X]) * a1 * u ^ 2 - (2560 : K[X]) * a1 * a2) +
              Polynomial.C μ₃ *
                ((24 : K[X]) * a2 * u - (5 : K[X]) * u ^ 3)) +
          h0 ^ 5 *
            (((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
                a1 ^ 2 +
              (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
                Polynomial.C κ₇ * (4 : K[X]) -
                (983040 : K[X]) * a0 ^ 2) *
                (u ^ 2 - (4 : K[X]) * a2)) -
          h0 ^ 6 *
            (Polynomial.C μ * ((344064 : K[X]) * a0 * a1) +
              Polynomial.C μ₂ * ((2560 : K[X]) * a0 * u) +
              Polynomial.C μ₃ * ((96 : K[X]) * a1) +
              Polynomial.C μ₄ * u) +
          h0 ^ 7 *
            (Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
              Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
              Polynomial.C κ₉ - (4194304 : K[X]) * b0)) := by
  have hM16' := hM16
  simp only [alignedTenthDefect410] at hM16'
  rw [hM14, hM12, hM10, hM8, hM6, hM4, hM2, hHsq, hp3] at hM16'
  apply mul_left_cancel₀ (pow_ne_zero 20 hh0)
  linear_combination -hM16'

end Max11DegreeRoutes
