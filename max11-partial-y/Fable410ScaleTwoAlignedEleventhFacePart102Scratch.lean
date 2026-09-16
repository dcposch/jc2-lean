import Fable410ScaleTwoAlignedEleventhFacePart03Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- On the aligned face, with the consumed degree-`11` through
degree-`2` rows, the degree-`1` row is the weighted derivative
`H M₂₀' - 18 M₂₀ H' = 0`. -/
theorem alignedTwelfthDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    H * (alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (18 : K[X]) *
        alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedTwelfthCoefficientJacobianRow_410 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC2] at hrow
  have hB2 :=
    alignedThirdDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB4 :=
    alignedFourthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB6 :=
    alignedFifthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB8 :=
    alignedSixthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB10 :=
    alignedSeventhDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB12 :=
    alignedEighthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB14 :=
    alignedNinthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB16 :=
    alignedTenthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB18 :=
    alignedEleventhDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hid := alignedTwelfthDefect_weightedDerivative_identity_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 0)
    (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
    (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hB2, hB4, hB6, hB8, hB10, hB12, hB14, hB16, hB18] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-! ## Weight-`18` polynomial first integral -/

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Generic Wronskian quotient for the weight-`18` bracket: over a
characteristic-zero field, `H D' - 18 D H' = 0` forces
`D = C c * H¹⁸`.  Even-type: no squaring, no parity split. -/
theorem eighteenthPowerRelation_of_weightEighteenRow_410 {K : Type*}
    [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : H * D.derivative - (18 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D = Polynomial.C c * H ^ 18 := by
  have hC18 : Polynomial.C (18 : K) = (18 : K[X]) :=
    Polynomial.C_eq_natCast 18
  have hW : Polynomial.wronskian D (H ^ 18) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      D * (Polynomial.C (18 : K) * H ^ (18 - 1) * H.derivative) -
          D.derivative * H ^ 18 =
          H ^ 17 *
            (Polynomial.C (18 : K) * D * H.derivative -
              H * D.derivative) := by ring
      _ = 0 := by
        rw [hC18]
        have hfac :
            (18 : K[X]) * D * H.derivative - H * D.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 18 hH) hW

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Weight-eighteen polynomial first integral of the aligned `(4,10)`
twelfth defect: `M₂₀ = κ₁₁ H¹⁸` — even-type and chamber-free, the
sixth rung of the even ladder `H⁴, H⁶, H⁹, H¹², H¹⁵, H¹⁸`. -/
theorem alignedTwelfthDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₁₁ : K,
      alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₁₁ * H ^ 18 :=
  eighteenthPowerRelation_of_weightEighteenRow_410 hH
    (alignedTwelfthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Square chamber -/

end Max11DegreeRoutes
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
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- The consumed degree-`1` row in the square chamber: on the
divisibility `u² - 4 p₂ = h₀ v` of the fifth face the core gains
`h₀³`, and the peel is NINE deep: the NEW μ-FREE leading divisibility
`3200 (143 u⁶ - 572 p₂ u⁴ + 528 p₂² u² - 64 p₂³) v³ = h₀ s₂₅`, the
explicit peels producing `s₂₆` through `s₃₃` (`s₃₁` is loaded with
`μ₄`), and — with no letter left to solve — the SECOND aligned
CONSTANT PIN, now a `p₀`-cubic:
`C κ₁₁ = 838860800 p₀³ - 7864320 κ₃ p₀² - 10240 κ₇ p₀ - s₃₃`. -/
theorem alignedSquareTwelfth_solved_410 {K : Type*} [Field K]
    [CharZero K] {h0 u v a0 a1 a2 : K[X]} {μ κ₃ μ₂ μ₃ κ₇ μ₄ κ₁₁ : K}
    (hh0 : h0 ≠ 0)
    (hcore :
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
              Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2))))
    (hv : u ^ 2 - (4 : K[X]) * a2 = h0 * v) :
    ∃ s₂₅ s₂₆ s₂₇ s₂₈ s₂₉ s₃₀ s₃₁ s₃₂ s₃₃ : K[X],
      (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * a2 * u ^ 4 +
          (528 : K[X]) * a2 ^ 2 * u ^ 2 - (64 : K[X]) * a2 ^ 3) * v ^ 3 =
      h0 * s₂₅ ∧
      s₂₅ + (51200 : K[X]) * a1 * u *
        ((187 : K[X]) * u ^ 4 - (664 : K[X]) * a2 * u ^ 2 +
          (432 : K[X]) * a2 ^ 2) * v ^ 2 +
        Polynomial.C μ * ((35840 : K[X]) * a2 ^ 3 * u * v) = h0 * s₂₆ ∧
      s₂₆ +
        (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * v -
        Polynomial.C μ * ((349440 : K[X]) * a2 ^ 2 * u * v ^ 2) +
        Polynomial.C μ * ((286720 : K[X]) * a1 * a2 ^ 3) = h0 * s₂₇ ∧
      s₂₇ +
        (334233600 : K[X]) * a1 ^ 2 * a2 * v ^ 2 +
        (209715200 : K[X]) * a1 ^ 3 * a2 * u -
        (78643200 : K[X]) * a0 * a2 ^ 2 * v ^ 2 -
        Polynomial.C μ₂ * ((6400 : K[X]) * a2 ^ 2 * u * v) -
        Polynomial.C μ * ((495040 : K[X]) * a2 * u * v ^ 3) -
        Polynomial.C μ * ((6236160 : K[X]) * a1 * a2 ^ 2 * v) +
        Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * v ^ 2) = h0 * s₂₈ ∧
      s₂₈ +
        (68812800 : K[X]) * a1 ^ 2 * v ^ 3 +
        (183500800 : K[X]) * a1 ^ 3 * u * v -
        (68812800 : K[X]) * a0 * a2 * v ^ 3 -
        (314572800 : K[X]) * a0 * a1 * a2 * u * v -
        Polynomial.C μ₂ * ((35200 : K[X]) * a2 * u * v ^ 2) -
        Polynomial.C μ₂ * ((51200 : K[X]) * a1 * a2 ^ 2) -
        Polynomial.C μ * ((123760 : K[X]) * u * v ^ 4) -
        Polynomial.C μ * ((8547840 : K[X]) * a1 * a2 * v ^ 2) -
        Polynomial.C μ * ((6881280 : K[X]) * a1 ^ 2 * a2 * u) +
        Polynomial.C κ₃ * ((215040 : K[X]) * a2 * v ^ 3) +
        Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * u * v) = h0 * s₂₉ ∧
      s₂₉ -
        (12902400 : K[X]) * a0 * v ^ 4 -
        (176947200 : K[X]) * a0 * a1 * u * v ^ 2 +
        (104857600 : K[X]) * a1 ^ 4 -
        (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 +
        Polynomial.C μ₃ * ((960 : K[X]) * a2 * u * v) -
        Polynomial.C μ₂ * ((13200 : K[X]) * u * v ^ 3) -
        Polynomial.C μ₂ * ((486400 : K[X]) * a1 * a2 * v) -
        Polynomial.C μ * ((1921920 : K[X]) * a1 * v ^ 3) -
        Polynomial.C μ * ((8601600 : K[X]) * a1 ^ 2 * u * v) +
        Polynomial.C μ * ((3440640 : K[X]) * a0 * a2 * u * v) +
        Polynomial.C κ₃ * ((40320 : K[X]) * v ^ 4) +
        Polynomial.C κ₃ * ((552960 : K[X]) * a1 * u * v ^ 2) +
        Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2) = h0 * s₃₀ ∧
      s₃₀ -
        (629145600 : K[X]) * a0 * a1 ^ 2 * v +
        (314572800 : K[X]) * a0 ^ 2 * a2 * v +
        Polynomial.C μ₃ * ((720 : K[X]) * u * v ^ 2) +
        Polynomial.C μ₃ * ((7680 : K[X]) * a1 * a2) -
        Polynomial.C μ₂ * ((156800 : K[X]) * a1 * v ^ 2) -
        Polynomial.C μ₂ * ((409600 : K[X]) * a1 ^ 2 * u) +
        Polynomial.C μ * ((2580480 : K[X]) * a0 * u * v ^ 2) -
        Polynomial.C μ * ((9175040 : K[X]) * a1 ^ 3) +
        Polynomial.C μ * ((27525120 : K[X]) * a0 * a1 * a2) -
        Polynomial.C κ₇ * ((1280 : K[X]) * a2 * v) +
        Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * v) -
        Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * v) = h0 * s₃₁ ∧
      s₃₁ +
        (117964800 : K[X]) * a0 ^ 2 * v ^ 2 +
        (629145600 : K[X]) * a0 ^ 2 * a1 * u +
        Polynomial.C μ₄ * ((80 : K[X]) * u * v) +
        Polynomial.C μ₃ * ((5760 : K[X]) * a1 * v) +
        Polynomial.C μ₂ * ((204800 : K[X]) * a0 * u * v) +
        Polynomial.C μ * ((20643840 : K[X]) * a0 * a1 * v) -
        Polynomial.C κ₇ * ((480 : K[X]) * v ^ 2) -
        Polynomial.C κ₇ * ((2560 : K[X]) * a1 * u) -
        Polynomial.C κ₃ * ((737280 : K[X]) * a0 * v ^ 2) -
        Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * u) = h0 * s₃₂ ∧
      s₃₂ +
        Polynomial.C μ₄ * ((640 : K[X]) * a1) +
        Polynomial.C μ₂ * ((1638400 : K[X]) * a0 * a1) = h0 * s₃₃ ∧
      Polynomial.C κ₁₁ =
        (838860800 : K[X]) * a0 ^ 3 -
          Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
          Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2) - s₃₃ := by
  obtain ⟨s₃₃, hs9⟩ : ∃ w : K[X],
      w = (838860800 : K[X]) * a0 ^ 3 -
        Polynomial.C κ₁₁ * ((1 : K[X])) -
        Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
        Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2) := ⟨_, rfl⟩
  obtain ⟨s₃₂, hs8⟩ : ∃ w : K[X],
      w = -Polynomial.C μ₄ * ((640 : K[X]) * a1) -
        Polynomial.C μ₂ * ((1638400 : K[X]) * a0 * a1) + h0 * s₃₃ := ⟨_, rfl⟩
  obtain ⟨s₃₁, hs7⟩ : ∃ w : K[X],
      w = -(117964800 : K[X]) * a0 ^ 2 * v ^ 2 -
        (629145600 : K[X]) * a0 ^ 2 * a1 * u -
        Polynomial.C μ₄ * ((80 : K[X]) * u * v) -
        Polynomial.C μ₃ * ((5760 : K[X]) * a1 * v) -
        Polynomial.C μ₂ * ((204800 : K[X]) * a0 * u * v) -
        Polynomial.C μ * ((20643840 : K[X]) * a0 * a1 * v) +
        Polynomial.C κ₇ * ((480 : K[X]) * v ^ 2) +
        Polynomial.C κ₇ * ((2560 : K[X]) * a1 * u) +
        Polynomial.C κ₃ * ((737280 : K[X]) * a0 * v ^ 2) +
        Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * u) + h0 * s₃₂ := ⟨_, rfl⟩
  obtain ⟨s₃₀, hs6⟩ : ∃ w : K[X],
      w = (629145600 : K[X]) * a0 * a1 ^ 2 * v -
        (314572800 : K[X]) * a0 ^ 2 * a2 * v -
        Polynomial.C μ₃ * ((720 : K[X]) * u * v ^ 2) -
        Polynomial.C μ₃ * ((7680 : K[X]) * a1 * a2) +
        Polynomial.C μ₂ * ((156800 : K[X]) * a1 * v ^ 2) +
        Polynomial.C μ₂ * ((409600 : K[X]) * a1 ^ 2 * u) -
        Polynomial.C μ * ((2580480 : K[X]) * a0 * u * v ^ 2) +
        Polynomial.C μ * ((9175040 : K[X]) * a1 ^ 3) -
        Polynomial.C μ * ((27525120 : K[X]) * a0 * a1 * a2) +
        Polynomial.C κ₇ * ((1280 : K[X]) * a2 * v) -
        Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * v) +
        Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * v) + h0 * s₃₁ := ⟨_, rfl⟩
  obtain ⟨s₂₉, hs5⟩ : ∃ w : K[X],
      w = (12902400 : K[X]) * a0 * v ^ 4 +
        (176947200 : K[X]) * a0 * a1 * u * v ^ 2 -
        (104857600 : K[X]) * a1 ^ 4 +
        (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
        Polynomial.C μ₃ * ((960 : K[X]) * a2 * u * v) +
        Polynomial.C μ₂ * ((13200 : K[X]) * u * v ^ 3) +
        Polynomial.C μ₂ * ((486400 : K[X]) * a1 * a2 * v) +
        Polynomial.C μ * ((1921920 : K[X]) * a1 * v ^ 3) +
        Polynomial.C μ * ((8601600 : K[X]) * a1 ^ 2 * u * v) -
        Polynomial.C μ * ((3440640 : K[X]) * a0 * a2 * u * v) -
        Polynomial.C κ₃ * ((40320 : K[X]) * v ^ 4) -
        Polynomial.C κ₃ * ((552960 : K[X]) * a1 * u * v ^ 2) -
        Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2) + h0 * s₃₀ := ⟨_, rfl⟩
  obtain ⟨s₂₈, hs4⟩ : ∃ w : K[X],
      w = -(68812800 : K[X]) * a1 ^ 2 * v ^ 3 -
        (183500800 : K[X]) * a1 ^ 3 * u * v +
        (68812800 : K[X]) * a0 * a2 * v ^ 3 +
        (314572800 : K[X]) * a0 * a1 * a2 * u * v +
        Polynomial.C μ₂ * ((35200 : K[X]) * a2 * u * v ^ 2) +
        Polynomial.C μ₂ * ((51200 : K[X]) * a1 * a2 ^ 2) +
        Polynomial.C μ * ((123760 : K[X]) * u * v ^ 4) +
        Polynomial.C μ * ((8547840 : K[X]) * a1 * a2 * v ^ 2) +
        Polynomial.C μ * ((6881280 : K[X]) * a1 ^ 2 * a2 * u) -
        Polynomial.C κ₃ * ((215040 : K[X]) * a2 * v ^ 3) -
        Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * u * v) + h0 * s₂₉ := ⟨_, rfl⟩
  obtain ⟨s₂₇, hs3⟩ : ∃ w : K[X],
      w = -(334233600 : K[X]) * a1 ^ 2 * a2 * v ^ 2 -
        (209715200 : K[X]) * a1 ^ 3 * a2 * u +
        (78643200 : K[X]) * a0 * a2 ^ 2 * v ^ 2 +
        Polynomial.C μ₂ * ((6400 : K[X]) * a2 ^ 2 * u * v) +
        Polynomial.C μ * ((495040 : K[X]) * a2 * u * v ^ 3) +
        Polynomial.C μ * ((6236160 : K[X]) * a1 * a2 ^ 2 * v) -
        Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * v ^ 2) + h0 * s₂₈ := ⟨_, rfl⟩
  obtain ⟨s₂₆, hs2⟩ : ∃ w : K[X],
      w = -(314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * v +
        Polynomial.C μ * ((349440 : K[X]) * a2 ^ 2 * u * v ^ 2) -
        Polynomial.C μ * ((286720 : K[X]) * a1 * a2 ^ 3) + h0 * s₂₇ := ⟨_, rfl⟩
  obtain ⟨s₂₅, hs1⟩ : ∃ w : K[X],
      w = -(9574400 : K[X]) * a1 * u ^ 5 * v ^ 2 +
        (33996800 : K[X]) * a1 * a2 * u ^ 3 * v ^ 2 -
        (22118400 : K[X]) * a1 * a2 ^ 2 * u * v ^ 2 -
        Polynomial.C μ * ((35840 : K[X]) * a2 ^ 3 * u * v) + h0 * s₂₆ := ⟨_, rfl⟩
  refine ⟨s₂₅, s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv] at hcore
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9]
    linear_combination hcore
  · rw [hs1]
    ring
  · rw [hs2]
    ring
  · rw [hs3]
    ring
  · rw [hs4]
    ring
  · rw [hs5]
    ring
  · rw [hs6]
    ring
  · rw [hs7]
    ring
  · rw [hs8]
    ring
  · rw [hs9]
    ring

/-! ## Nonsquare chamber -/

end Max11DegreeRoutes
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
