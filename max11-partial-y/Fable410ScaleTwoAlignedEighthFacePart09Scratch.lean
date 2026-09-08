import Fable410ScaleTwoAlignedEighthFacePart08Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Cleared square-core form of the ninth defect relation: cancelling
`h₀¹⁸` from `M₁₄ = μ₄ h₀²⁷` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`,
`M₄ = κ₃ H⁶`, `M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹`, `M₁₀ = μ₃ h₀²¹`,
`M₁₂ = κ₇ H¹²` exposes the `h₀`-free core
`80 u (11 u² - 12 p₂) (u² - 4 p₂)³
+ 2560 h₀² p₁ (7 u² - 4 p₂) (u² - 4 p₂)²` — the fifth face's perfect
cube times a NEW odd cofactor plus a `p₁`-loaded square — carried by
`h₀³` against the explicit quotient, whose leading block is the
μ-loaded sextic `273 u⁶ - 2520 p₂ u⁴ + 6720 p₂² u² - 3584 p₂³`. -/
theorem alignedSquareNinth_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ : K}
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
      Polynomial.C μ₄ * h0 ^ 27) :
    (80 : K[X]) * u * ((11 : K[X]) * u ^ 2 - (12 : K[X]) * a2) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (2560 : K[X]) * h0 ^ 2 * a1 *
          ((7 : K[X]) * u ^ 2 - (4 : K[X]) * a2) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
      h0 ^ 3 *
        (Polynomial.C μ *
            ((273 : K[X]) * u ^ 6 - (2520 : K[X]) * a2 * u ^ 4 +
              (6720 : K[X]) * a2 ^ 2 * u ^ 2 - (3584 : K[X]) * a2 ^ 3) +
          h0 * (((30720 : K[X]) * a0 - Polynomial.C κ₃ * (96 : K[X])) *
              u * (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
            (122880 : K[X]) * a1 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
          h0 ^ 2 *
            (Polynomial.C μ₂ *
                ((35 : K[X]) * u ^ 4 - (240 : K[X]) * a2 * u ^ 2 +
                  (320 : K[X]) * a2 ^ 2) +
              Polynomial.C μ *
                (a1 * ((4480 : K[X]) * u ^ 3 - (21504 : K[X]) * a2 * u))) +
          h0 ^ 3 *
            (((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
                a1 * (u ^ 2 - (4 : K[X]) * a2) -
              (327680 : K[X]) * a1 ^ 3) +
          h0 ^ 4 *
            (Polynomial.C μ₂ * ((640 : K[X]) * a1 * u) +
              Polynomial.C μ *
                ((86016 : K[X]) * a0 * a2 + (43008 : K[X]) * a1 ^ 2 -
                  (10752 : K[X]) * a0 * u ^ 2) -
              Polynomial.C μ₃ *
                ((3 : K[X]) * (u ^ 2 - (8 : K[X]) * a2))) +
          h0 ^ 5 *
            ((1048576 : K[X]) * b1 + Polynomial.C κ₇ * ((4 : K[X]) * u) +
              Polynomial.C κ₅ * ((512 : K[X]) * a1) +
              Polynomial.C κ₃ * ((6144 : K[X]) * a0 * u) -
              (983040 : K[X]) * a0 ^ 2 * u -
              Polynomial.C κ * ((262144 : K[X]) * a0 * a1)) +
          h0 ^ 6 *
            (Polynomial.C μ₄ + Polynomial.C μ₂ * ((2560 : K[X]) * a0))) := by
  have hM14' := hM14
  simp only [alignedNinthDefect410] at hM14'
  rw [hM12, hM10, hM8, hM6, hM4, hM2, hHsq, hp3] at hM14'
  apply mul_left_cancel₀ (pow_ne_zero 18 hh0)
  linear_combination hM14'

end Max11DegreeRoutes
