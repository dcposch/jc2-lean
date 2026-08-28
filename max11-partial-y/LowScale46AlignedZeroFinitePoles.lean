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

omit [CharZero k] in
/-- Exact finite order implies nonvanishing. -/
theorem hahn_ne_zero_of_orderTop_eq_coe46
    (x : HahnSeries ℚ k) (a : ℚ)
    (hx : x.orderTop = (↑a : WithTop ℚ)) : x ≠ 0 := by
  intro h
  rw [h, HahnSeries.orderTop_zero] at hx
  exact WithTop.coe_ne_top hx.symm

omit [CharZero k] in
/-- The leading coefficient of a nonzero Hahn constant is that constant. -/
theorem hahnLeadingCoeff_C46 (c : k) (hc : c ≠ 0) :
    (HahnSeries.C c : HahnSeries ℚ k).leadingCoeff = c := by
  have hne : (HahnSeries.C c : HahnSeries ℚ k) ≠ 0 := by
    intro h
    apply hc
    apply HahnSeries.C_injective (Γ := ℚ)
    simpa using h
  have hordtop : (HahnSeries.C c : HahnSeries ℚ k).orderTop =
      (↑(0 : ℚ) : WithTop ℚ) := by
    rw [HahnSeries.C_apply, HahnSeries.orderTop_single hc]
  have hord : (HahnSeries.C c : HahnSeries ℚ k).order = 0 := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hne, hordtop]
  rw [HahnSeries.leadingCoeff_eq, hord, HahnSeries.C_apply,
    HahnSeries.coeff_single]
  simp

omit [CharZero k] in
/-- If two exact same-order terms sum with a strictly higher remainder to
zero, their leading coefficients cancel. -/
theorem hahnLeadingCoeffs_cancel_of_add_higher_eq_zero46
    (p q r : HahnSeries ℚ k) (a : ℚ)
    (hp : p.orderTop = (↑a : WithTop ℚ))
    (hq : q.orderTop = (↑a : WithTop ℚ))
    (hr : (↑a : WithTop ℚ) < r.orderTop)
    (hsum : p + q + r = 0) :
    p.leadingCoeff + q.leadingCoeff = 0 := by
  have hr0 : r.coeff a = 0 := HahnSeries.coeff_eq_zero_of_lt_orderTop hr
  have hpcoeff := hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 p a hp
  have hqcoeff := hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 q a hq
  have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff a) hsum
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hr0, add_zero]
    at hcoeff
  rwa [hpcoeff, hqcoeff] at hcoeff

/-- The first boundary numerator cannot have `Q²` strictly below the forced
`Y,W` order `7/2`. -/
theorem alignedZeroBoundary_Qsq_lower_impossible46
    (gamma d0 : k) (s Q Y W : HahnSeries ℚ k) (q : ℚ)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑q : WithTop ℚ))
    (hlt : 2 * q < 7 / 2)
    (hY : Y.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ))
    (hW : W.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ))
    (hboundary : W = HahnSeries.C (4 : k) * Y +
        HahnSeries.C (4 : k) * Q ^ 2 -
        HahnSeries.C (4 * d0 + (8 / 3 : k) * gamma) * s ^ 4) : False := by
  let p : HahnSeries ℚ k := HahnSeries.C (-4 : k) * Q ^ 2
  let r : HahnSeries ℚ k := W - HahnSeries.C (4 : k) * Y +
    HahnSeries.C (4 * d0 + (8 / 3 : k) * gamma) * s ^ 4
  have hQ2 := hahnOrderTop_pow_eq46 Q q 2 hQ
  have hp : p.orderTop = (↑(2 * q) : WithTop ℚ) := by
    dsimp [p]
    exact hahnOrderTop_C_mul_eq46 _ _ (2 * q) (by norm_num)
      (by simpa using hQ2)
  have hWgt : (↑(2 * q) : WithTop ℚ) < W.orderTop := by
    rw [hW, WithTop.coe_lt_coe]
    exact hlt
  have hYgt : (↑(2 * q) : WithTop ℚ) <
      (HahnSeries.C (4 : k) * Y).orderTop := by
    have h := hahnOrderTop_C_mul_eq46 (4 : k) Y (7 / 2) (by norm_num) hY
    rw [h, WithTop.coe_lt_coe]
    exact hlt
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs4gt : (↑(2 * q) : WithTop ℚ) <
      (HahnSeries.C (4 * d0 + (8 / 3 : k) * gamma) * s ^ 4).orderTop := by
    exact hahnOrderTop_C_mul_gt46 _ _ (2 * q) 4 (by simpa using hs4)
      (by linarith)
  have hsubgt : (↑(2 * q) : WithTop ℚ) <
      (W - HahnSeries.C (4 : k) * Y).orderTop := by
    rw [sub_eq_add_neg]
    exact hahnOrderTop_add_gt46 _ _ _ hWgt (by simpa using hYgt)
  have hr : (↑(2 * q) : WithTop ℚ) < r.orderTop := by
    dsimp [r]
    exact hahnOrderTop_add_gt46 _ _ _ hsubgt hs4gt
  have hsum : p + r = 0 := by
    dsimp [p, r]
    rw [hboundary]
    simp only [map_neg, map_ofNat]
    ring
  exact hahnExactAddHigher_impossible46 p r (2 * q) hp hr hsum

/-- If `Q²` is strictly above `7/2`, the first boundary gives `W₀=4Y₀`,
whereas the second curve row gives `W₀²=-16Y₀²`; these are incompatible. -/
theorem alignedZeroBoundary_Qsq_higher_impossible46
    (gamma d0 k1 : k) (s Q Y W : HahnSeries ℚ k)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop)
    (hQ2 : (↑(7 / 2 : ℚ) : WithTop ℚ) < (Q ^ 2).orderTop)
    (hY : Y.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ))
    (hW : W.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ))
    (hboundary : W = HahnSeries.C (4 : k) * Y +
        HahnSeries.C (4 : k) * Q ^ 2 -
        HahnSeries.C (4 * d0 + (8 / 3 : k) * gamma) * s ^ 4)
    (hcurve1 : W ^ 2 =
      HahnSeries.C (16 : k) * ((Q - 1) * Y ^ 2) +
        HahnSeries.C ((32 / 3 : k) *
          (k1 + (2 / 3 : k) * gamma ^ 2)) * s ^ 8) : False := by
  let p : HahnSeries ℚ k := W
  let qterm : HahnSeries ℚ k := HahnSeries.C (-4 : k) * Y
  let r : HahnSeries ℚ k := HahnSeries.C (-4 : k) * Q ^ 2 +
    HahnSeries.C (4 * d0 + (8 / 3 : k) * gamma) * s ^ 4
  have hp : p.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ) := by exact hW
  have hqterm : qterm.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ) := by
    dsimp [qterm]
    exact hahnOrderTop_C_mul_eq46 _ _ (7 / 2) (by norm_num) hY
  have hQ2gt : (↑(7 / 2 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (-4 : k) * Q ^ 2).orderTop :=
    hahnOrderTop_C_mul_gt_of_gt46 _ _ _ hQ2
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs4gt : (↑(7 / 2 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (4 * d0 + (8 / 3 : k) * gamma) * s ^ 4).orderTop := by
    exact hahnOrderTop_C_mul_gt46 _ _ (7 / 2) 4 (by simpa using hs4) (by norm_num)
  have hr : (↑(7 / 2 : ℚ) : WithTop ℚ) < r.orderTop := by
    dsimp [r]
    exact hahnOrderTop_add_gt46 _ _ _ hQ2gt hs4gt
  have hsum : p + qterm + r = 0 := by
    dsimp [p, qterm, r]
    rw [hboundary]
    simp only [map_neg, map_ofNat]
    ring
  have hleadBoundary := hahnLeadingCoeffs_cancel_of_add_higher_eq_zero46
    p qterm r (7 / 2) hp hqterm hr hsum
  have hqlead : qterm.leadingCoeff = -4 * Y.leadingCoeff := by
    dsimp [qterm]
    rw [HahnSeries.leadingCoeff_mul, hahnLeadingCoeff_C46 (-4 : k) (by norm_num)]
  have hWY : W.leadingCoeff = 4 * Y.leadingCoeff := by
    dsimp [p] at hleadBoundary
    rw [hqlead] at hleadBoundary
    linear_combination hleadBoundary
  let p1 : HahnSeries ℚ k := W ^ 2
  let q1 : HahnSeries ℚ k := HahnSeries.C (16 : k) * Y ^ 2
  let r1 : HahnSeries ℚ k :=
    -(HahnSeries.C (16 : k) * (Q * Y ^ 2)) -
      HahnSeries.C ((32 / 3 : k) *
        (k1 + (2 / 3 : k) * gamma ^ 2)) * s ^ 8
  have hW2 := hahnOrderTop_pow_eq46 W (7 / 2) 2 hW
  have hY2 := hahnOrderTop_pow_eq46 Y (7 / 2) 2 hY
  have hp1 : p1.orderTop = (↑(7 : ℚ) : WithTop ℚ) := by
    dsimp [p1]
    norm_num at hW2 ⊢
    exact hW2
  have hq1 : q1.orderTop = (↑(7 : ℚ) : WithTop ℚ) := by
    dsimp [q1]
    have hY2' : (Y ^ 2).orderTop = (↑(7 : ℚ) : WithTop ℚ) := by
      norm_num at hY2 ⊢
      exact hY2
    exact hahnOrderTop_C_mul_eq46 _ _ 7 (by norm_num) hY2'
  have hQY2gt : (↑(7 : ℚ) : WithTop ℚ) < (Q * Y ^ 2).orderTop :=
    hahnOrderTop_pos_mul_exact_gt46 Q (Y ^ 2) 7 hQ (by
      norm_num at hY2 ⊢
      exact hY2)
  have hfirstgt : (↑(7 : ℚ) : WithTop ℚ) <
      (-(HahnSeries.C (16 : k) * (Q * Y ^ 2))).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact hahnOrderTop_C_mul_gt_of_gt46 _ _ _ hQY2gt
  have hs8 := hahnOrderTop_pow_eq46 s 1 8 hs
  have hsecondgt : (↑(7 : ℚ) : WithTop ℚ) <
      (-(HahnSeries.C ((32 / 3 : k) *
        (k1 + (2 / 3 : k) * gamma ^ 2)) * s ^ 8)).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact hahnOrderTop_C_mul_gt46 _ _ 7 8 (by simpa using hs8) (by norm_num)
  have hr1 : (↑(7 : ℚ) : WithTop ℚ) < r1.orderTop := by
    dsimp [r1]
    rw [sub_eq_add_neg]
    exact hahnOrderTop_add_gt46 _ _ _ hfirstgt hsecondgt
  have hsum1 : p1 + q1 + r1 = 0 := by
    dsimp [p1, q1, r1]
    rw [hcurve1]
    ring
  have hleadCurve := hahnLeadingCoeffs_cancel_of_add_higher_eq_zero46
    p1 q1 r1 7 hp1 hq1 hr1 hsum1
  have hp1lead : p1.leadingCoeff = W.leadingCoeff ^ 2 := by
    dsimp [p1]
    simp [pow_two, HahnSeries.leadingCoeff_mul]
  have hq1lead : q1.leadingCoeff = 16 * Y.leadingCoeff ^ 2 := by
    dsimp [q1]
    rw [HahnSeries.leadingCoeff_mul, hahnLeadingCoeff_C46 (16 : k) (by norm_num),
      pow_two, HahnSeries.leadingCoeff_mul]
    ring
  rw [hp1lead, hq1lead, hWY] at hleadCurve
  have hYne := hahn_ne_zero_of_orderTop_eq_coe46 Y (7 / 2) hY
  have hYlead : Y.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hYne
  have hYsq : Y.leadingCoeff ^ 2 = 0 := by
    linear_combination (1 / 32 : k) * hleadCurve
  exact pow_ne_zero 2 hYlead hYsq

/-- At the boundary value `v(Q)=7/4`, the `4Q³` term is uniquely lowest in
the exact second boundary row. -/
theorem alignedZeroBoundary_Q_tie_impossible46
    (gamma d0 e0 : k) (s Q Y : HahnSeries ℚ k)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑(7 / 4 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ))
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma) 0
      (HahnSeries.C d0) (HahnSeries.C e0) = 0) : False := by
  let p : HahnSeries ℚ k := HahnSeries.C (4 : k) * Q ^ 3
  let r : HahnSeries ℚ k := HahnSeries.C (-3 : k) * Y ^ 2 -
      HahnSeries.C (8 * gamma + 12 * d0) * (Q * s ^ 4) +
      HahnSeries.C (8 * e0) * s ^ 6
  have hQ3 := hahnOrderTop_pow_eq46 Q (7 / 4) 3 hQ
  have hp : p.orderTop = (↑(21 / 4 : ℚ) : WithTop ℚ) := by
    dsimp [p]
    have hQ3' : (Q ^ 3).orderTop = (↑(21 / 4 : ℚ) : WithTop ℚ) := by
      norm_num at hQ3 ⊢
      exact hQ3
    exact hahnOrderTop_C_mul_eq46 _ _ (21 / 4) (by norm_num) hQ3'
  have hY2 := hahnOrderTop_pow_eq46 Y (7 / 2) 2 hY
  have hYgt : (↑(21 / 4 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (-3 : k) * Y ^ 2).orderTop := by
    have hY2' : (Y ^ 2).orderTop = (↑(7 : ℚ) : WithTop ℚ) := by
      norm_num at hY2 ⊢
      exact hY2
    exact hahnOrderTop_C_mul_gt46 _ _ (21 / 4) 7 hY2' (by norm_num)
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hQs4 := hahnOrderTop_mul_eq46 Q (s ^ 4) (7 / 4) 4 hQ
    (by simpa using hs4)
  have hQsgt : (↑(21 / 4 : ℚ) : WithTop ℚ) <
      (-(HahnSeries.C (8 * gamma + 12 * d0) * (Q * s ^ 4))).orderTop := by
    rw [HahnSeries.orderTop_neg]
    have hQs4' : (Q * s ^ 4).orderTop =
        (↑(23 / 4 : ℚ) : WithTop ℚ) := by
      norm_num at hQs4 ⊢
      exact hQs4
    exact hahnOrderTop_C_mul_gt46 _ _ (21 / 4) (23 / 4)
      hQs4' (by norm_num)
  have hs6 := hahnOrderTop_pow_eq46 s 1 6 hs
  have hs6gt : (↑(21 / 4 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (8 * e0) * s ^ 6).orderTop := by
    exact hahnOrderTop_C_mul_gt46 _ _ (21 / 4) 6 (by simpa using hs6) (by norm_num)
  have hrest1 := hahnOrderTop_add_gt46 (21 / 4)
    (HahnSeries.C (-3 : k) * Y ^ 2)
    (-(HahnSeries.C (8 * gamma + 12 * d0) * (Q * s ^ 4))) hYgt hQsgt
  have hr : (↑(21 / 4 : ℚ) : WithTop ℚ) < r.orderTop := by
    dsimp [r]
    rw [sub_eq_add_neg]
    exact hahnOrderTop_add_gt46 _ _ _ hrest1 hs6gt
  have hsum : p + r = 0 := by
    dsimp [p, r]
    simp only [alignedLocalG46, mul_zero, zero_mul, add_zero,
      sub_zero] at hG
    simp only [map_add, map_mul, map_neg, map_ofNat]
    rw [← hG]
    ring
  exact hahnExactAddHigher_impossible46 p r (21 / 4) hp hr hsum

/-- Complete `k2 != 0` finite-pole exclusion in the final aligned stratum.
The literal local curve rows first force `v(Y)=v(W)=7/2`; the first boundary
then forces `2v(Q) >= 7/2`.  Strict inequality gives the incompatible
`W₀=4Y₀`, `W₀²=-16Y₀²` system, while equality is killed by the exact second
boundary row. -/
theorem alignedZeroFinitePole46_exhaustive
    (gamma d0 e0 k2 k1 : k) (s Q Y : HahnSeries ℚ k)
    (hk2 : k2 ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQcases : PositiveFiniteOrZero46 Q)
    (hYcases : PositiveFiniteOrZero46 Y)
    (hG : alignedLocalG46 s Q Y 0 (HahnSeries.C gamma) 0
      (HahnSeries.C d0) (HahnSeries.C e0) = 0)
    (hJ2 : alignedLocalJTwo46 s Q Y 0 (HahnSeries.C gamma) 0
      (HahnSeries.C d0) (HahnSeries.C k2) = 0)
    (hJ1 : alignedLocalJOne46 s Q Y 0 (HahnSeries.C gamma) 0
      (HahnSeries.C d0) (HahnSeries.C k1) = 0) : False := by
  let _ : CharZero (HahnSeries ℚ k) := by
    constructor
    intro m n h
    apply Nat.cast_injective (R := k)
    apply HahnSeries.C_injective (Γ := ℚ)
    simpa using h
  let W : HahnSeries ℚ k :=
    alignedZeroLocalVNumerator46 s Q Y (HahnSeries.C gamma)
      (HahnSeries.C d0)
  have hQpos := orderTop_pos_of_positiveFiniteOrZero46 Q hQcases
  have hYpos := orderTop_pos_of_positiveFiniteOrZero46 Y hYcases
  have hboundary : W = HahnSeries.C (4 : k) * Y +
      HahnSeries.C (4 : k) * Q ^ 2 -
      HahnSeries.C (4 * d0 + (8 / 3 : k) * gamma) * s ^ 4 := by
    dsimp [W]
    have h := alignedZeroLocalVNumerator46_eq s Q Y
      (HahnSeries.C gamma) (HahnSeries.C d0)
    simpa only [map_add, map_mul, map_div₀, map_ofNat, mul_assoc] using h
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
  have hsne := hahn_ne_zero_of_orderTop_eq_coe46 s 1 hs
  have hc : (-4 / 3 : k) * k2 ≠ 0 := mul_ne_zero (by norm_num) hk2
  have hCne : (HahnSeries.C ((-4 / 3 : k) * k2) : HahnSeries ℚ k) ≠ 0 := by
    intro h
    apply hc
    apply HahnSeries.C_injective (Γ := ℚ)
    simpa using h
  have hproduct : Y * W ≠ 0 := by
    rw [hcurve2]
    exact mul_ne_zero hCne (pow_ne_zero 7 hsne)
  have hYne : Y ≠ 0 := by
    intro h
    rw [h, zero_mul] at hproduct
    exact hproduct rfl
  have hWne : W ≠ 0 := by
    intro h
    rw [h, mul_zero] at hproduct
    exact hproduct rfl
  obtain ⟨y, hy, hYord⟩ : ∃ y : ℚ, 0 < y ∧
      Y.orderTop = (↑y : WithTop ℚ) := by
    rcases hYcases with hYzero | hYfinite
    · exact (hYne hYzero).elim
    · exact hYfinite
  have hQ2pos : (↑(0 : ℚ) : WithTop ℚ) < (Q ^ 2).orderTop := by
    rw [pow_two]
    exact hahnOrderTop_mul_pos46 Q Q hQpos hQpos
  have hYtermPos : (↑(0 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (4 : k) * Y).orderTop :=
    hahnOrderTop_C_mul_gt_of_gt46 _ _ _ hYpos
  have hQtermPos : (↑(0 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (4 : k) * Q ^ 2).orderTop :=
    hahnOrderTop_C_mul_gt_of_gt46 _ _ _ hQ2pos
  have hs4 := hahnOrderTop_pow_eq46 s 1 4 hs
  have hs4pos : (↑(0 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (4 * d0 + (8 / 3 : k) * gamma) * s ^ 4).orderTop := by
    exact hahnOrderTop_C_mul_gt46 _ _ 0 4 (by simpa using hs4) (by norm_num)
  have haddPos : (↑(0 : ℚ) : WithTop ℚ) <
      (HahnSeries.C (4 : k) * Y + HahnSeries.C (4 : k) * Q ^ 2).orderTop :=
    hahnOrderTop_add_gt46 _ _ _ hYtermPos hQtermPos
  have hWpos : (↑(0 : ℚ) : WithTop ℚ) < W.orderTop := by
    rw [hboundary, sub_eq_add_neg]
    exact hahnOrderTop_add_gt46 _ _ _ haddPos (by simpa using hs4pos)
  let w : ℚ := W.order
  have hWord : W.orderTop = (↑w : WithTop ℚ) := by
    exact (HahnSeries.order_eq_orderTop_of_ne_zero hWne).symm
  have hw : 0 < w := by
    rw [hWord, WithTop.coe_lt_coe] at hWpos
    exact hWpos
  have horders := alignedZeroCurveOrders46 gamma k2 k1 s Q Y W y w hk2 hs
    hQpos hy hYord hw hWord hcurve2 hcurve1
  have hYhalf : Y.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ) := by
    rw [← horders.1]
    exact hYord
  have hWhalf : W.orderTop = (↑(7 / 2 : ℚ) : WithTop ℚ) := by
    rw [← horders.2]
    exact hWord
  rcases hQcases with hQzero | ⟨q, hq, hQord⟩
  · have hQ2gt : (↑(7 / 2 : ℚ) : WithTop ℚ) < (Q ^ 2).orderTop := by
      simp [hQzero]
    exact alignedZeroBoundary_Qsq_higher_impossible46 gamma d0 k1 s Q Y W
      hs hQpos hQ2gt hYhalf hWhalf hboundary hcurve1
  · rcases lt_trichotomy (2 * q) (7 / 2) with hlt | heq | hgt
    · exact alignedZeroBoundary_Qsq_lower_impossible46 gamma d0 s Q Y W q
        hs hQord hlt hYhalf hWhalf hboundary
    · have hqeq : q = 7 / 4 := by linarith
      subst q
      exact alignedZeroBoundary_Q_tie_impossible46 gamma d0 e0 s Q Y
        hs hQord hYhalf hG
    · have hQ2ord := hahnOrderTop_pow_eq46 Q q 2 hQord
      have hQ2gt : (↑(7 / 2 : ℚ) : WithTop ℚ) < (Q ^ 2).orderTop := by
        rw [hQ2ord, WithTop.coe_lt_coe]
        simpa using hgt
      exact alignedZeroBoundary_Qsq_higher_impossible46 gamma d0 k1 s Q Y W
        hs hQpos hQ2gt hYhalf hWhalf hboundary hcurve1

end FinalAlignedOrderCone

end Max11DegreeRoutes
