import Fable410ScaleTwoAlignedEleventhFacePart06Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Cleared square-core form of the twelfth defect relation:
cancelling `h₀²⁴` from `M₂₀ = κ₁₁ H¹⁸` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`,
`M₄ = κ₃ H⁶`, `M₆ = μ₂ h₀¹⁵`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`,
`M₁₄ = μ₄ h₀²⁷` exposes the `h₀`-free core carried by `h₀³` against
the explicit quotient; the μ-block factors through `(u² - 4 p₂)`, so
the level-zero quotient block is μ-loaded with no constant term.
Neither `M₈` nor `M₁₆` nor `M₁₈` enters, and the whole relation is
`q`-free and `κ`/`κ₅`/`κ₉`-free. -/
theorem alignedSquareTwelfth_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ μ₂ μ₃ κ₇ μ₄ κ₁₁ : K}
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
    (hM20 : alignedTwelfthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₁₁ * H ^ 18) :
    (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * a2 * u ^ 4 +
          (528 : K[X]) * a2 ^ 2 * u ^ 2 - (64 : K[X]) * a2 ^ 3) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
      (51200 : K[X]) * h0 ^ 2 * a1 * u *
          ((187 : K[X]) * u ^ 4 - (664 : K[X]) * a2 * u ^ 2 +
            (432 : K[X]) * a2 ^ 2) * (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
      h0 ^ 3 *
      ((Polynomial.C μ * ((123760 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 4) +
            Polynomial.C μ * ((495040 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
            Polynomial.C μ * ((349440 : K[X]) * a2 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
            Polynomial.C μ * ((35840 : K[X]) * a2 ^ 3 * u * (u ^ 2 - (4 : K[X]) * a2))) +
        h0 * ((12902400 : K[X]) * a0 * (u ^ 2 - (4 : K[X]) * a2) ^ 4 -
            Polynomial.C κ₃ * ((40320 : K[X]) * (u ^ 2 - (4 : K[X]) * a2) ^ 4) -
            (68812800 : K[X]) * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
            (68812800 : K[X]) * a0 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3 -
            Polynomial.C κ₃ * ((215040 : K[X]) * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3) -
            (334233600 : K[X]) * a1 ^ 2 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
            (78643200 : K[X]) * a0 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
            Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
            (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) +
        h0 ^ 2 * (Polynomial.C μ₂ * ((13200 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
            Polynomial.C μ * ((1921920 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
            Polynomial.C μ₂ * ((35200 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
            Polynomial.C μ * ((8547840 : K[X]) * a1 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
            Polynomial.C μ₂ * ((6400 : K[X]) * a2 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C μ * ((6236160 : K[X]) * a1 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ * ((286720 : K[X]) * a1 * a2 ^ 3)) +
        h0 ^ 3 * ((176947200 : K[X]) * a0 * a1 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
            Polynomial.C κ₃ * ((552960 : K[X]) * a1 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
            (183500800 : K[X]) * a1 ^ 3 * u * (u ^ 2 - (4 : K[X]) * a2) +
            (314572800 : K[X]) * a0 * a1 * a2 * u * (u ^ 2 - (4 : K[X]) * a2) -
            Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) -
            (209715200 : K[X]) * a1 ^ 3 * a2 * u) +
        h0 ^ 4 * (-Polynomial.C μ₃ * ((720 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
            Polynomial.C μ₂ * ((156800 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
            Polynomial.C μ * ((2580480 : K[X]) * a0 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
            Polynomial.C μ₃ * ((960 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C μ₂ * ((486400 : K[X]) * a1 * a2 * (u ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C μ * ((8601600 : K[X]) * a1 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ * ((3440640 : K[X]) * a0 * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C μ₂ * ((51200 : K[X]) * a1 * a2 ^ 2) +
            Polynomial.C μ * ((6881280 : K[X]) * a1 ^ 2 * a2 * u)) +
        h0 ^ 5 * (-(117964800 : K[X]) * a0 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
            Polynomial.C κ₇ * ((480 : K[X]) * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
            Polynomial.C κ₃ * ((737280 : K[X]) * a0 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
            (629145600 : K[X]) * a0 * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) -
            (314572800 : K[X]) * a0 ^ 2 * a2 * (u ^ 2 - (4 : K[X]) * a2) +
            Polynomial.C κ₇ * ((1280 : K[X]) * a2 * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * (u ^ 2 - (4 : K[X]) * a2)) -
            (104857600 : K[X]) * a1 ^ 4 +
            (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
            Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2)) +
        h0 ^ 6 * (-Polynomial.C μ₄ * ((80 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ₃ * ((5760 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ₂ * ((204800 : K[X]) * a0 * u * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ * ((20643840 : K[X]) * a0 * a1 * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ₃ * ((7680 : K[X]) * a1 * a2) +
            Polynomial.C μ₂ * ((409600 : K[X]) * a1 ^ 2 * u) +
            Polynomial.C μ * ((9175040 : K[X]) * a1 ^ 3) -
            Polynomial.C μ * ((27525120 : K[X]) * a0 * a1 * a2)) +
        h0 ^ 7 * (-(629145600 : K[X]) * a0 ^ 2 * a1 * u +
            Polynomial.C κ₇ * ((2560 : K[X]) * a1 * u) +
            Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * u)) +
        h0 ^ 8 * (-Polynomial.C μ₄ * ((640 : K[X]) * a1) -
            Polynomial.C μ₂ * ((1638400 : K[X]) * a0 * a1)) +
        h0 ^ 9 * ((838860800 : K[X]) * a0 ^ 3 -
            Polynomial.C κ₁₁ * ((1 : K[X])) -
            Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
            Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2))) := by
  have hM20' := hM20
  simp only [alignedTwelfthDefect410] at hM20'
  rw [hM14, hM12, hM10, hM6, hM4, hM2, hHsq, hp3] at hM20'
  apply mul_left_cancel₀ (pow_ne_zero 24 hh0)
  linear_combination -hM20'

end Max11DegreeRoutes
