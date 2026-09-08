import Fable410ScaleTwoAlignedEleventhFacePart08Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Cleared nonsquare-core form of the twelfth defect relation:
cancelling `H¹²` from `M₂₀ = κ₁₁ H¹⁸` on `p₃ = H g`,
`M₂ = M₆ = M₁₀ = M₁₄ = 0`, `M₄ = κ₃ H⁶`, `M₁₂ = κ₇ H¹²` exposes the
same core in `g` carried by `H²` against the explicit quotient — no
parity kill: `κ₁₁` survives the nonsquare chamber, tied in the
`H²`-part of the quotient. -/
theorem alignedNonsquareTwelfth_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₇ κ₁₁ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM2z : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6z : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0)
    (hM10z : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ = 0)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM14z : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      0)
    (hM20 : alignedTwelfthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₁₁ * H ^ 18) :
    (3200 : K[X]) * ((143 : K[X]) * g ^ 6 - (572 : K[X]) * a2 * g ^ 4 +
          (528 : K[X]) * a2 ^ 2 * g ^ 2 - (64 : K[X]) * a2 ^ 3) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
      (51200 : K[X]) * H * a1 * g *
          ((187 : K[X]) * g ^ 4 - (664 : K[X]) * a2 * g ^ 2 +
            (432 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
      H ^ 2 *
      (((12902400 : K[X]) * a0 * (g ^ 2 - (4 : K[X]) * a2) ^ 4 -
            Polynomial.C κ₃ * ((40320 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 4) -
            (68812800 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
            (68812800 : K[X]) * a0 * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3 -
            Polynomial.C κ₃ * ((215040 : K[X]) * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3) -
            (334233600 : K[X]) * a1 ^ 2 * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
            (78643200 : K[X]) * a0 * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
            Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2) -
            (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2)) +
        H * ((176947200 : K[X]) * a0 * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
            Polynomial.C κ₃ * ((552960 : K[X]) * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2) -
            (183500800 : K[X]) * a1 ^ 3 * g * (g ^ 2 - (4 : K[X]) * a2) +
            (314572800 : K[X]) * a0 * a1 * a2 * g * (g ^ 2 - (4 : K[X]) * a2) -
            Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * g * (g ^ 2 - (4 : K[X]) * a2)) -
            (209715200 : K[X]) * a1 ^ 3 * a2 * g) +
        H ^ 2 * (-(117964800 : K[X]) * a0 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
            Polynomial.C κ₇ * ((480 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 2) +
            Polynomial.C κ₃ * ((737280 : K[X]) * a0 * (g ^ 2 - (4 : K[X]) * a2) ^ 2) +
            (629145600 : K[X]) * a0 * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) -
            (314572800 : K[X]) * a0 ^ 2 * a2 * (g ^ 2 - (4 : K[X]) * a2) +
            Polynomial.C κ₇ * ((1280 : K[X]) * a2 * (g ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * (g ^ 2 - (4 : K[X]) * a2)) -
            (104857600 : K[X]) * a1 ^ 4 +
            (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
            Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2)) +
        H ^ 3 * (-(629145600 : K[X]) * a0 ^ 2 * a1 * g +
            Polynomial.C κ₇ * ((2560 : K[X]) * a1 * g) +
            Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * g)) +
        H ^ 4 * ((838860800 : K[X]) * a0 ^ 3 -
            Polynomial.C κ₁₁ * ((1 : K[X])) -
            Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
            Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2))) := by
  have hM20' := hM20
  simp only [alignedTwelfthDefect410] at hM20'
  rw [hM14z, hM12, hM10z, hM6z, hM4, hM2z, hg] at hM20'
  apply mul_left_cancel₀ (pow_ne_zero 12 hH)
  linear_combination -hM20'

end Max11DegreeRoutes
