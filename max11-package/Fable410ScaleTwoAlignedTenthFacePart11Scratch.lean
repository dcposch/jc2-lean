import Fable410ScaleTwoAlignedTenthFacePart10Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Nonsquare chamber -/

set_option maxHeartbeats 64000000 in
/-- Cleared nonsquare-core form of the eleventh defect relation:
cancelling `H¹¹` from `M₁₈ = 0` (parity kill) on `p₃ = H g`,
`M₂ = M₆ = M₁₀ = M₁₄ = 0`, `M₄ = κ₃ H⁶`, `M₁₂ = κ₇ H¹²` exposes the
same core in `g` carried by `H²` against the explicit quotient — a
`q`-free constraint. -/
theorem alignedNonsquareEleventh_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₇ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM20 : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM60 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0)
    (hM100 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ = 0)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM140 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      0)
    (hM180 : alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
      κ = 0) :
    (1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 - (104 : K[X]) * a2 * g ^ 2 +
            (48 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (30720 : K[X]) * H * a1 *
          ((33 : K[X]) * g ^ 4 - (72 : K[X]) * a2 * g ^ 2 +
            (16 : K[X]) * a2 ^ 2) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
      H ^ 2 *
        ((1536 : K[X]) * g * (g ^ 2 - (4 : K[X]) * a2) *
            (((320 : K[X]) * a0 - Polynomial.C κ₃) *
                (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              (((640 : K[X]) * a0 - Polynomial.C κ₃ * (2 : K[X])) *
                  g ^ 2 - (1920 : K[X]) * a1 ^ 2) *
                (g ^ 2 - (4 : K[X]) * a2) -
              (2560 : K[X]) * a1 ^ 2 * g ^ 2) +
          (4096 : K[X]) * H * a1 *
            (((960 : K[X]) * a0 - Polynomial.C κ₃ * (3 : K[X])) *
                (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              ((3840 : K[X]) * a0 - Polynomial.C κ₃ * (12 : K[X])) *
                g ^ 2 * (g ^ 2 - (4 : K[X]) * a2) -
              (1280 : K[X]) * a1 ^ 2 *
                ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2)) +
          (64 : K[X]) * H ^ 2 * g *
            ((Polynomial.C κ₃ * ((1536 : K[X]) * a0) + Polynomial.C κ₇ -
                (245760 : K[X]) * a0 ^ 2) *
                (g ^ 2 - (4 : K[X]) * a2) +
              ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
                a1 ^ 2) +
          (512 : K[X]) * H ^ 3 * a1 *
            (Polynomial.C κ₃ * ((1536 : K[X]) * a0) + Polynomial.C κ₇ -
              (245760 : K[X]) * a0 ^ 2)) := by
  have hM18' := hM180
  simp only [alignedEleventhDefect410] at hM18'
  rw [hM140, hM12, hM100, hM60, hM4, hM20, hg] at hM18'
  apply mul_left_cancel₀ (pow_ne_zero 11 hH)
  linear_combination hM18'

#print axioms alignedNonsquareEleventh_core_410

end Max11DegreeRoutes
