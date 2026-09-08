import Fable410ScaleTwoAlignedTenthFacePart08Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Square chamber -/

set_option maxHeartbeats 64000000 in
/-- Cleared square-core form of the eleventh defect relation:
cancelling `h₀²²` from `M₁₈ = μ₅ h₀³³` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`,
`M₄ = κ₃ H⁶`, `M₆ = μ₂ h₀¹⁵`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`,
`M₁₄ = μ₄ h₀²⁷` exposes the `h₀`-free core
`1280 u (39 u⁴ - 104 p₂ u² + 48 p₂²) (u² - 4 p₂)³
+ 30720 h₀² p₁ (33 u⁴ - 72 p₂ u² + 16 p₂²) (u² - 4 p₂)²` carried by
`h₀³` against the explicit quotient, whose leading block is the
μ-loaded octic `13923 u⁸ - 148512 p₂ u⁶ + 524160 p₂² u⁴
- 645120 p₂³ u² + 143360 p₂⁴`.  Neither `M₈` nor `M₁₆` enters, and
the whole relation is `q`-free and `κ`/`κ₅`/`κ₉`-free. -/
theorem alignedSquareEleventh_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ μ₂ μ₃ κ₇ μ₄ μ₅ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp3 : a3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H a1 a2 a3 b7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ =
      Polynomial.C μ₂ * h0 ^ 15)
    (hM10 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₃ * h0 ^ 21)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM14 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₄ * h0 ^ 27)
    (hM18 : alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C μ₅ * h0 ^ 33) :
    (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 - (104 : K[X]) * a2 * u ^ 2 +
            (48 : K[X]) * a2 ^ 2) * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (30720 : K[X]) * h0 ^ 2 * a1 *
          ((33 : K[X]) * u ^ 4 - (72 : K[X]) * a2 * u ^ 2 +
            (16 : K[X]) * a2 ^ 2) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
      h0 ^ 3 *
        (Polynomial.C μ *
            ((13923 : K[X]) * u ^ 8 - (148512 : K[X]) * a2 * u ^ 6 +
              (524160 : K[X]) * a2 ^ 2 * u ^ 4 -
              (645120 : K[X]) * a2 ^ 3 * u ^ 2 +
              (143360 : K[X]) * a2 ^ 4) +
          h0 * ((1536 : K[X]) * u *
            (((320 : K[X]) * a0 - Polynomial.C κ₃) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
              (((640 : K[X]) * a0 - Polynomial.C κ₃ * (2 : K[X])) *
                  u ^ 2 - (1920 : K[X]) * a1 ^ 2) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
              (2560 : K[X]) * a1 ^ 2 * u ^ 2 *
                (u ^ 2 - (4 : K[X]) * a2))) +
          h0 ^ 2 *
            (Polynomial.C μ *
                ((209664 : K[X]) * a1 * u ^ 5 -
                  (1290240 : K[X]) * a1 * a2 * u ^ 3 +
                  (1720320 : K[X]) * a1 * a2 ^ 2 * u) +
              Polynomial.C μ₂ *
                ((1540 : K[X]) * u ^ 6 - (12320 : K[X]) * a2 * u ^ 4 +
                  (26880 : K[X]) * a2 ^ 2 * u ^ 2 -
                  (10240 : K[X]) * a2 ^ 3)) +
          h0 ^ 3 * ((4096 : K[X]) * a1 *
            (((960 : K[X]) * a0 - Polynomial.C κ₃ * (3 : K[X])) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
              ((3840 : K[X]) * a0 - Polynomial.C κ₃ * (12 : K[X])) *
                u ^ 2 * (u ^ 2 - (4 : K[X]) * a2) -
              (1280 : K[X]) * a1 ^ 2 *
                ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2))) +
          h0 ^ 4 *
            (Polynomial.C μ *
                ((1720320 : K[X]) * a0 * a2 * u ^ 2 -
                  (322560 : K[X]) * a0 * u ^ 4 -
                  (1376256 : K[X]) * a0 * a2 ^ 2 +
                  (860160 : K[X]) * a1 ^ 2 * u ^ 2 -
                  (1376256 : K[X]) * a1 ^ 2 * a2) +
              Polynomial.C μ₂ *
                ((17920 : K[X]) * a1 * u ^ 3 -
                  (61440 : K[X]) * a1 * a2 * u) +
              Polynomial.C μ₃ *
                ((480 : K[X]) * a2 * u ^ 2 - (90 : K[X]) * u ^ 4 -
                  (384 : K[X]) * a2 ^ 2)) +
          h0 ^ 5 * ((64 : K[X]) * u *
            ((Polynomial.C κ₃ * ((1536 : K[X]) * a0) + Polynomial.C κ₇ -
                (245760 : K[X]) * a0 ^ 2) *
                (u ^ 2 - (4 : K[X]) * a2) +
              ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
                a1 ^ 2)) +
          h0 ^ 6 *
            (Polynomial.C μ₂ *
                ((81920 : K[X]) * a0 * a2 - (30720 : K[X]) * a0 * u ^ 2 +
                  (40960 : K[X]) * a1 ^ 2) -
              Polynomial.C μ * ((2752512 : K[X]) * a0 * a1 * u) -
              Polynomial.C μ₃ * ((768 : K[X]) * a1 * u) +
              Polynomial.C μ₄ *
                ((32 : K[X]) * a2 - (12 : K[X]) * u ^ 2)) +
          h0 ^ 7 *
            (Polynomial.C κ₃ * ((786432 : K[X]) * a0 * a1) +
              Polynomial.C κ₇ * ((512 : K[X]) * a1) -
              (125829120 : K[X]) * a0 ^ 2 * a1) +
          h0 ^ 8 *
            (Polynomial.C μ * ((5505024 : K[X]) * a0 ^ 2) +
              Polynomial.C μ₃ * ((3072 : K[X]) * a0) +
              Polynomial.C μ₅)) := by
  have hM18' := hM18
  simp only [alignedEleventhDefect410] at hM18'
  rw [hM14, hM12, hM10, hM6, hM4, hM2, hHsq, hp3] at hM18'
  apply mul_left_cancel₀ (pow_ne_zero 22 hh0)
  linear_combination hM18'

#print axioms alignedSquareEleventh_core_410

end Max11DegreeRoutes
