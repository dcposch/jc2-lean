import LowScale46AlignedPolynomialEndgame

/-! # Finite poles in the final aligned `(4,6)` stratum

This module treats `beta=delta=0` after the aligned Newton strata.  It
introduces the local numerator of `V=U-8gamma/3`, verifies its exact two
curve equations after boundary elimination, and derives the forced orders
`v(Y)=v(W)=7/2` when `k2 != 0`.
-/

noncomputable section

namespace Max11DegreeRoutes

section ExactLocalRows

variable {F : Type*} [Field F] [CharZero F]

/-- In the weighted local chart, `W=s^4 V` after eliminating `Z` by the
first boundary equation. -/
def alignedZeroLocalVNumerator46
    (s Q Y gamma d0 : F) : F :=
  alignedLocalZ46 s Q Y d0 - (8 / 3 : F) * gamma * s ^ 4

/-- Exact first-boundary expression for the shifted numerator `W`. -/
theorem alignedZeroLocalVNumerator46_eq
    (s Q Y gamma d0 : F) :
    alignedZeroLocalVNumerator46 s Q Y gamma d0 =
      4 * Y + 4 * Q ^ 2 - (4 * d0 + (8 / 3 : F) * gamma) * s ^ 4 := by
  simp only [alignedZeroLocalVNumerator46, alignedLocalZ46]
  ring

/-- The first local coefficient-curve row is exactly the cleared equation
`Y*W=(-4/3)k2*s^7`. -/
theorem alignedZeroLocal_curveTwo_identity46
    (s Q Y gamma d0 k2 : F) :
    Y * alignedZeroLocalVNumerator46 s Q Y gamma d0 -
        ((-4 / 3 : F) * k2) * s ^ 7 =
      (-2 / 3 : F) * alignedLocalJTwo46 s Q Y 0 gamma 0 d0 k2 := by
  simp only [alignedZeroLocalVNumerator46, alignedLocalZ46,
    alignedLocalJTwo46]
  ring

/-- The second local coefficient-curve row is exactly the cleared equation
`W^2=16(Q-1)Y^2+(32/3)(k1+2gamma^2/3)s^8`. -/
theorem alignedZeroLocal_curveOne_identity46
    (s Q Y gamma d0 k1 : F) :
    alignedZeroLocalVNumerator46 s Q Y gamma d0 ^ 2 -
        16 * (Q - 1) * Y ^ 2 -
        (32 / 3 : F) * (k1 + (2 / 3 : F) * gamma ^ 2) * s ^ 8 =
      (16 / 3 : F) * alignedLocalJOne46 s Q Y 0 gamma 0 d0 k1 := by
  simp only [alignedZeroLocalVNumerator46, alignedLocalZ46,
    alignedLocalJOne46]
  ring

/-- Vanishing of the literal first curve row gives the exact local product
equation. -/
theorem alignedZeroLocal_curveTwo_eq46
    (s Q Y gamma d0 k2 : F)
    (hJ2 : alignedLocalJTwo46 s Q Y 0 gamma 0 d0 k2 = 0) :
    Y * alignedZeroLocalVNumerator46 s Q Y gamma d0 =
      ((-4 / 3 : F) * k2) * s ^ 7 := by
  have h := alignedZeroLocal_curveTwo_identity46 s Q Y gamma d0 k2
  rw [hJ2, mul_zero] at h
  exact sub_eq_zero.mp h

/-- Vanishing of the literal second curve row gives the exact local square
equation. -/
theorem alignedZeroLocal_curveOne_eq46
    (s Q Y gamma d0 k1 : F)
    (hJ1 : alignedLocalJOne46 s Q Y 0 gamma 0 d0 k1 = 0) :
    alignedZeroLocalVNumerator46 s Q Y gamma d0 ^ 2 =
      16 * (Q - 1) * Y ^ 2 +
        (32 / 3 : F) * (k1 + (2 / 3 : F) * gamma ^ 2) * s ^ 8 := by
  have h := alignedZeroLocal_curveOne_identity46 s Q Y gamma d0 k1
  rw [hJ1, mul_zero] at h
  linear_combination h

end ExactLocalRows

section FinalAlignedOrderCone

variable {k : Type*} [Field k] [CharZero k]

omit [CharZero k] in
/-- Two exact finite-order Hahn terms cannot cancel modulo a remainder whose
order is strictly above both candidates unless their orders agree. -/
theorem hahnOrders_eq_of_two_terms_add_higher_eq_zero46
    (p q r : HahnSeries ℚ k) (a b : ℚ)
    (hp : p.orderTop = (↑a : WithTop ℚ))
    (hq : q.orderTop = (↑b : WithTop ℚ))
    (hr : (↑(min a b) : WithTop ℚ) < r.orderTop)
    (hsum : p + q + r = 0) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hq0 : q.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hq]
      exact WithTop.coe_lt_coe.mpr hab)
    have hr0 : r.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [min_eq_left (le_of_lt hab)] at hr
      exact hr)
    have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff a) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hq0, hr0,
      add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hp hcoeff
  · have hp0 : p.coeff b = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hp]
      exact WithTop.coe_lt_coe.mpr hba)
    have hr0 : r.coeff b = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [min_eq_right (le_of_lt hba)] at hr
      exact hr)
    have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff b) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hp0, hr0,
      zero_add, add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hq hcoeff

/-- A strictly positive-order Hahn series differs from `1` by a series of
exact order zero. -/
theorem hahnOrderTop_sub_one_eq_zero_of_pos46
    (Q : HahnSeries ℚ k)
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop) :
    (Q - 1).orderTop = (↑(0 : ℚ) : WithTop ℚ) := by
  have hnegOne : (-1 : HahnSeries ℚ k).orderTop =
      (↑(0 : ℚ) : WithTop ℚ) := by simp
  have hlt : (-1 : HahnSeries ℚ k).orderTop < Q.orderTop := by
    rwa [hnegOne]
  have h := HahnSeries.orderTop_add_eq_left hlt
  simpa [sub_eq_add_neg, add_comm] using h

/-- The two exact curve equations in the final aligned stratum force the
unique positive local order pair `(v(Y),v(W))=(7/2,7/2)` when `k2 != 0`. -/
theorem alignedZeroCurveOrders46
    (gamma k2 k1 : k) (s Q Y W : HahnSeries ℚ k) (y w : ℚ)
    (hk2 : k2 ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop)
    (_hy : 0 < y) (hY : Y.orderTop = (↑y : WithTop ℚ))
    (_hw : 0 < w) (hW : W.orderTop = (↑w : WithTop ℚ))
    (hcurve2 : Y * W = HahnSeries.C ((-4 / 3 : k) * k2) * s ^ 7)
    (hcurve1 : W ^ 2 =
      HahnSeries.C (16 : k) * ((Q - 1) * Y ^ 2) +
        HahnSeries.C ((32 / 3 : k) *
          (k1 + (2 / 3 : k) * gamma ^ 2)) * s ^ 8) :
    y = 7 / 2 ∧ w = 7 / 2 := by
  have hs7 := hahnOrderTop_pow_eq46 s 1 7 hs
  have hleft2 := hahnOrderTop_mul_eq46 Y W y w hY hW
  have hright2 :
      (HahnSeries.C ((-4 / 3 : k) * k2) * s ^ 7).orderTop =
        (↑(7 : ℚ) : WithTop ℚ) := by
    exact hahnOrderTop_C_mul_eq46 _ _ 7 (mul_ne_zero (by norm_num) hk2)
      (by simpa using hs7)
  have hyw : y + w = 7 := by
    have horders := congrArg HahnSeries.orderTop hcurve2
    rw [hleft2, hright2] at horders
    exact WithTop.coe_eq_coe.mp horders
  have hQm1 := hahnOrderTop_sub_one_eq_zero_of_pos46 Q hQ
  have hY2 := hahnOrderTop_pow_eq46 Y y 2 hY
  have hW2 := hahnOrderTop_pow_eq46 W w 2 hW
  let p : HahnSeries ℚ k := W ^ 2
  let q : HahnSeries ℚ k :=
    -(HahnSeries.C (16 : k) * ((Q - 1) * Y ^ 2))
  let r : HahnSeries ℚ k :=
    -(HahnSeries.C ((32 / 3 : k) *
      (k1 + (2 / 3 : k) * gamma ^ 2)) * s ^ 8)
  have hp : p.orderTop = (↑(2 * w) : WithTop ℚ) := by
    dsimp [p]
    simpa using hW2
  have hQm1Y2 : ((Q - 1) * Y ^ 2).orderTop =
      (↑(2 * y) : WithTop ℚ) := by
    have h := hahnOrderTop_mul_eq46 (Q - 1) (Y ^ 2) 0 (2 * y)
      hQm1 (by simpa using hY2)
    simpa using h
  have hq : q.orderTop = (↑(2 * y) : WithTop ℚ) := by
    dsimp [q]
    rw [HahnSeries.orderTop_neg]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * y) (by norm_num) hQm1Y2
  have hminlt : min (2 * w) (2 * y) < 8 := by
    by_cases hwy : w ≤ y
    · rw [min_eq_left (by linarith)]
      linarith
    · rw [min_eq_right (by linarith)]
      linarith
  have hs8 := hahnOrderTop_pow_eq46 s 1 8 hs
  have hr : (↑(min (2 * w) (2 * y)) : WithTop ℚ) < r.orderTop := by
    dsimp [r]
    rw [HahnSeries.orderTop_neg]
    exact hahnOrderTop_C_mul_gt46 _ _ _ 8 (by simpa using hs8) hminlt
  have hsum : p + q + r = 0 := by
    dsimp [p, q, r]
    rw [hcurve1]
    ring
  have htwice := hahnOrders_eq_of_two_terms_add_higher_eq_zero46
    p q r (2 * w) (2 * y) hp hq hr hsum
  constructor <;> linarith

/-- Literal local-row instantiation of the final aligned order cone. -/
theorem alignedZeroLocalCurveOrders46
    (gamma d0 k2 k1 : k) (s Q Y : HahnSeries ℚ k) (y w : ℚ)
    (hk2 : k2 ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop)
    (hy : 0 < y) (hY : Y.orderTop = (↑y : WithTop ℚ))
    (hw : 0 < w)
    (hW : (alignedZeroLocalVNumerator46 s Q Y (HahnSeries.C gamma)
      (HahnSeries.C d0)).orderTop = (↑w : WithTop ℚ))
    (hJ2 : alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma) 0
      (HahnSeries.C d0) (HahnSeries.C k2) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y 0 (HahnSeries.C gamma) 0
      (HahnSeries.C d0) (HahnSeries.C k1) = 0) :
    y = 7 / 2 ∧ w = 7 / 2 := by
  let _ : CharZero (HahnSeries ℚ k) := by
    constructor
    intro m n h
    apply Nat.cast_injective (R := k)
    apply HahnSeries.C_injective (Γ := ℚ)
    simpa using h
  let W := alignedZeroLocalVNumerator46 s Q Y (HahnSeries.C gamma)
    (HahnSeries.C d0)
  have hcurve2 : Y * W =
      HahnSeries.C ((-4 / 3 : k) * k2) * s ^ 7 := by
    dsimp [W]
    have h := alignedZeroLocal_curveTwo_eq46 s Q Y (HahnSeries.C gamma)
      (HahnSeries.C d0) (HahnSeries.C k2) hJ2
    simpa only [map_mul, map_neg, map_div₀, map_ofNat] using h
  have hcurve1 : W ^ 2 =
      HahnSeries.C (16 : k) * ((Q - 1) * Y ^ 2) +
        HahnSeries.C ((32 / 3 : k) *
          (k1 + (2 / 3 : k) * gamma ^ 2)) * s ^ 8 := by
    dsimp [W]
    have h := alignedZeroLocal_curveOne_eq46 s Q Y (HahnSeries.C gamma)
      (HahnSeries.C d0) (HahnSeries.C k1) hJ1
    simpa only [map_add, map_mul, map_pow, map_div₀, map_ofNat, mul_assoc] using h
  exact alignedZeroCurveOrders46 gamma k2 k1 s Q Y W y w hk2 hs hQ hy hY
    hw hW hcurve2 hcurve1

end FinalAlignedOrderCone

end Max11DegreeRoutes
