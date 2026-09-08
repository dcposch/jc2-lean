import LowScale46RegularLoads

/-! # Weighted-infinity specialization for the `(4,6)` coefficient curve

This module supplies the Hahn-series initial-form calculus needed to pass
from a genuine finite pole of the coefficient curve to its unique weighted
point at infinity.
-/

noncomputable section

namespace Max11DegreeRoutes

open Polynomial

section InitialCoefficientCalculus

variable {k : Type*} [Field k]

/-- At the sum of two lower order bounds, a Hahn product has only the
product of the two boundary coefficients. -/
theorem hahnCoeff_mul_at_lower46
    (x y : HahnSeries ℚ k) (a b : ℚ)
    (hx : (↑a : WithTop ℚ) ≤ x.orderTop)
    (hy : (↑b : WithTop ℚ) ≤ y.orderTop) :
    (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hxord : x.orderTop = (↑x.order : WithTop ℚ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hx0).symm
  have hyord : y.orderTop = (↑y.order : WithTop ℚ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hy0).symm
  have hax : a ≤ x.order := by
    rw [hxord, WithTop.coe_le_coe] at hx
    exact hx
  have hby : b ≤ y.order := by
    rw [hyord, WithTop.coe_le_coe] at hy
    exact hy
  by_cases haxe : a = x.order
  · by_cases hbye : b = y.order
    · subst a
      subst b
      rw [HahnSeries.coeff_mul_order_add_order,
        HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq]
    · have hblt : b < y.order := lt_of_le_of_ne hby hbye
      have hycoeff : y.coeff b = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop (by
          rw [hyord]
          exact WithTop.coe_lt_coe.mpr hblt)
      have hprod : (x * y).coeff (a + b) = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop (by
          rw [HahnSeries.orderTop_mul, hxord, hyord, ← WithTop.coe_add]
          exact WithTop.coe_lt_coe.mpr (by
            rw [haxe]
            simpa [add_comm] using add_lt_add_left hblt x.order))
      rw [hprod, hycoeff, mul_zero]
  · have halt : a < x.order := lt_of_le_of_ne hax haxe
    have hxcoeff : x.coeff a = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hxord]
        exact WithTop.coe_lt_coe.mpr halt)
    have hprod : (x * y).coeff (a + b) = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [HahnSeries.orderTop_mul, hxord, hyord, ← WithTop.coe_add]
        exact WithTop.coe_lt_coe.mpr (add_lt_add_of_lt_of_le halt hby))
    rw [hprod, hxcoeff, zero_mul]

/-- Natural powers respect a lower Hahn-order bound. -/
theorem hahnOrderTop_pow_lower46
    (x : HahnSeries ℚ k) (a : ℚ) (n : ℕ)
    (hx : (↑a : WithTop ℚ) ≤ x.orderTop) :
    (↑((n : ℚ) * a) : WithTop ℚ) ≤ (x ^ n).orderTop := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, HahnSeries.orderTop_mul, Nat.cast_succ, add_mul,
        one_mul, WithTop.coe_add]
      exact add_le_add ih hx

/-- At the scaled lower boundary, the coefficient of a power is the power
of the boundary coefficient. -/
theorem hahnCoeff_pow_at_lower46
    (x : HahnSeries ℚ k) (a : ℚ) (n : ℕ)
    (hx : (↑a : WithTop ℚ) ≤ x.orderTop) :
    (x ^ n).coeff ((n : ℚ) * a) = (x.coeff a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Nat.cast_succ, add_mul, one_mul,
        hahnCoeff_mul_at_lower46 (x ^ n) x ((n : ℚ) * a) a
          (hahnOrderTop_pow_lower46 x a n hx) hx,
        ih, pow_succ]

end InitialCoefficientCalculus

section WeightedPoleRadius

variable {k : Type*} [Field k]

/-- The ordinary Hahn order, coerced to `WithTop`, is always a lower
bound for `orderTop`; for the zero series this just says `0 ≤ ⊤`. -/
theorem hahnOrder_coe_le_orderTop46 (x : HahnSeries ℚ k) :
    (↑x.order : WithTop ℚ) ≤ x.orderTop := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [HahnSeries.order_eq_orderTop_of_ne_zero hx]

/-- A lower bound on the ordinary Hahn order is also a lower bound on
`orderTop`, including for the identically-zero series. -/
theorem hahnOrderTop_lower_of_order46 (x : HahnSeries ℚ k) (a : ℚ)
    (h : a ≤ x.order) :
    (↑a : WithTop ℚ) ≤ x.orderTop := by
  exact (WithTop.coe_le_coe.mpr h).trans (hahnOrder_coe_le_orderTop46 x)

/-- The largest weighted pole radius among coordinates of weights
`1,2,3,4`.  The convention `order 0 = 0` makes zero coordinates harmless. -/
def weightedPoleRadius46
    (r q B U : HahnSeries ℚ k) : ℚ :=
  max (-r.order)
    (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)))

theorem weightedPoleRadius46_r_lower
    (r q B U : HahnSeries ℚ k) :
    (↑(-weightedPoleRadius46 r q B U) : WithTop ℚ) ≤ r.orderTop := by
  apply hahnOrderTop_lower_of_order46
  have h := le_max_left (-r.order)
    (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)))
  dsimp only [weightedPoleRadius46]
  linarith

theorem weightedPoleRadius46_q_lower
    (r q B U : HahnSeries ℚ k) :
    (↑(-2 * weightedPoleRadius46 r q B U) : WithTop ℚ) ≤ q.orderTop := by
  apply hahnOrderTop_lower_of_order46
  have hinner := le_max_left (-q.order / 2)
    (max (-B.order / 3) (-U.order / 4))
  have houter := le_max_right (-r.order)
    (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)))
  dsimp only [weightedPoleRadius46]
  linarith

theorem weightedPoleRadius46_B_lower
    (r q B U : HahnSeries ℚ k) :
    (↑(-3 * weightedPoleRadius46 r q B U) : WithTop ℚ) ≤ B.orderTop := by
  apply hahnOrderTop_lower_of_order46
  have hB := le_max_left (-B.order / 3) (-U.order / 4)
  have hmiddle := le_max_right (-q.order / 2)
    (max (-B.order / 3) (-U.order / 4))
  have houter := le_max_right (-r.order)
    (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)))
  dsimp only [weightedPoleRadius46]
  linarith

theorem weightedPoleRadius46_U_lower
    (r q B U : HahnSeries ℚ k) :
    (↑(-4 * weightedPoleRadius46 r q B U) : WithTop ℚ) ≤ U.orderTop := by
  apply hahnOrderTop_lower_of_order46
  have hU := le_max_right (-B.order / 3) (-U.order / 4)
  have hmiddle := le_max_right (-q.order / 2)
    (max (-B.order / 3) (-U.order / 4))
  have houter := le_max_right (-r.order)
    (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)))
  dsimp only [weightedPoleRadius46]
  linarith

/-- If at least one weighted coordinate has negative ordinary order, the
weighted pole radius is positive. -/
theorem weightedPoleRadius46_pos
    (r q B U : HahnSeries ℚ k)
    (hpole : r.order < 0 ∨ q.order < 0 ∨ B.order < 0 ∨ U.order < 0) :
    0 < weightedPoleRadius46 r q B U := by
  rcases hpole with hr | hq | hB | hU
  · have h := le_max_left (-r.order)
      (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)))
    dsimp only [weightedPoleRadius46]
    linarith
  · have hinner := le_max_left (-q.order / 2)
      (max (-B.order / 3) (-U.order / 4))
    have houter := le_max_right (-r.order)
      (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)))
    dsimp only [weightedPoleRadius46]
    linarith
  · have hB' := le_max_left (-B.order / 3) (-U.order / 4)
    have hmiddle := le_max_right (-q.order / 2)
      (max (-B.order / 3) (-U.order / 4))
    have houter := le_max_right (-r.order)
      (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)))
    dsimp only [weightedPoleRadius46]
    linarith
  · have hU' := le_max_right (-B.order / 3) (-U.order / 4)
    have hmiddle := le_max_right (-q.order / 2)
      (max (-B.order / 3) (-U.order / 4))
    have houter := le_max_right (-r.order)
      (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)))
    dsimp only [weightedPoleRadius46]
    linarith

/-- One of the four coordinates attains the weighted pole radius. -/
theorem weightedPoleRadius46_attained
    (r q B U : HahnSeries ℚ k) :
    weightedPoleRadius46 r q B U = -r.order ∨
      weightedPoleRadius46 r q B U = -q.order / 2 ∨
      weightedPoleRadius46 r q B U = -B.order / 3 ∨
      weightedPoleRadius46 r q B U = -U.order / 4 := by
  rcases max_choice (-B.order / 3) (-U.order / 4) with hB | hU
  · rcases max_choice (-q.order / 2)
        (max (-B.order / 3) (-U.order / 4)) with hq | hrest
    · rcases max_choice (-r.order)
          (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4))) with hr | htail
      · exact Or.inl (by simpa only [weightedPoleRadius46] using hr)
      · exact Or.inr (Or.inl (calc
          weightedPoleRadius46 r q B U =
              max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)) := htail
          _ = -q.order / 2 := hq))
    · rcases max_choice (-r.order)
          (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4))) with hr | htail
      · exact Or.inl (by simpa only [weightedPoleRadius46] using hr)
      · exact Or.inr (Or.inr (Or.inl (by
          calc
            weightedPoleRadius46 r q B U =
                max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)) := htail
            _ = max (-B.order / 3) (-U.order / 4) := hrest
            _ = -B.order / 3 := hB)))
  · rcases max_choice (-q.order / 2)
        (max (-B.order / 3) (-U.order / 4)) with hq | hrest
    · rcases max_choice (-r.order)
          (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4))) with hr | htail
      · exact Or.inl (by simpa only [weightedPoleRadius46] using hr)
      · exact Or.inr (Or.inl (calc
          weightedPoleRadius46 r q B U =
              max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)) := htail
          _ = -q.order / 2 := hq))
    · rcases max_choice (-r.order)
          (max (-q.order / 2) (max (-B.order / 3) (-U.order / 4))) with hr | htail
      · exact Or.inl (by simpa only [weightedPoleRadius46] using hr)
      · exact Or.inr (Or.inr (Or.inr (by
          calc
            weightedPoleRadius46 r q B U =
                max (-q.order / 2) (max (-B.order / 3) (-U.order / 4)) := htail
            _ = max (-B.order / 3) (-U.order / 4) := hrest
            _ = -U.order / 4 := hU)))

/-- A coordinate whose (nonzero) boundary order is attained has a nonzero
boundary coefficient. -/
theorem hahnCoeff_ne_zero_of_order_eq_neg_weight46
    (x : HahnSeries ℚ k) (rho w : ℚ) (hrho : 0 < rho) (hw : 0 < w)
    (hx : x.order = -w * rho) :
    x.coeff (-w * rho) ≠ 0 := by
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, HahnSeries.order_zero] at hx
    nlinarith
  apply HahnSeries.coeff_orderTop_ne
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hx0, hx]

end WeightedPoleRadius

section WeightedInitialForms

variable {k : Type*} [Field k] [CharZero k]

local instance hahnCharZero46 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- A standardized monomial in coordinates of weights `1,2,3,4`. -/
def weightedMonomial46 (c : k) (r q B U : HahnSeries ℚ k)
    (ar aq aB aU : ℕ) : HahnSeries ℚ k :=
  HahnSeries.C c * r ^ ar * q ^ aq * B ^ aB * U ^ aU

theorem hahnNatCast_ne_zero46 (n : ℕ) (hn : n ≠ 0) :
    (n : HahnSeries ℚ k) ≠ 0 := by
  rw [← map_natCast (HahnSeries.C : k →+* HahnSeries ℚ k)]
  simpa only [map_zero] using
    (HahnSeries.C_injective (R := k) (Γ := ℚ)).ne
      (Nat.cast_ne_zero.mpr hn)

/-- Lower Hahn-order bounds add under multiplication. -/
theorem hahnOrderTop_mul_lower46
    (x y : HahnSeries ℚ k) (a b : ℚ)
    (hx : (↑a : WithTop ℚ) ≤ x.orderTop)
    (hy : (↑b : WithTop ℚ) ≤ y.orderTop) :
    (↑(a + b) : WithTop ℚ) ≤ (x * y).orderTop := by
  rw [HahnSeries.orderTop_mul]
  simpa only [WithTop.coe_add] using add_le_add hx hy

/-- Every monomial of weighted degree below `target` lies strictly above
order `-target * rho` when `rho > 0`. -/
theorem weightedMonomial46_orderTop_gt
    (c : k) (r q B U : HahnSeries ℚ k)
    (ar aq aB aU : ℕ) (rho target : ℚ)
    (hrho : 0 < rho)
    (hr : (↑(-rho) : WithTop ℚ) ≤ r.orderTop)
    (hq : (↑(-2 * rho) : WithTop ℚ) ≤ q.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hU : (↑(-4 * rho) : WithTop ℚ) ≤ U.orderTop)
    (hweight : (ar : ℚ) + 2 * aq + 3 * aB + 4 * aU < target) :
    (↑(-target * rho) : WithTop ℚ) <
      (weightedMonomial46 c r q B U ar aq aB aU).orderTop := by
  have hC : (0 : WithTop ℚ) ≤
      (HahnSeries.C c : HahnSeries ℚ k).orderTop :=
    hahnOrderTop_C_nonneg46 c
  have hrp := hahnOrderTop_pow_lower46 r (-rho) ar hr
  have hqp := hahnOrderTop_pow_lower46 q (-2 * rho) aq hq
  have hBp := hahnOrderTop_pow_lower46 B (-3 * rho) aB hB
  have hUp := hahnOrderTop_pow_lower46 U (-4 * rho) aU hU
  have hCr := hahnOrderTop_mul_lower46
    (HahnSeries.C c) (r ^ ar) 0 ((ar : ℚ) * (-rho)) hC hrp
  have hCrq := hahnOrderTop_mul_lower46
    (HahnSeries.C c * r ^ ar) (q ^ aq)
      (0 + (ar : ℚ) * (-rho)) ((aq : ℚ) * (-2 * rho)) hCr hqp
  have hCrqB := hahnOrderTop_mul_lower46
    (HahnSeries.C c * r ^ ar * q ^ aq) (B ^ aB)
      ((0 + (ar : ℚ) * (-rho)) + (aq : ℚ) * (-2 * rho))
      ((aB : ℚ) * (-3 * rho)) hCrq hBp
  have hfull := hahnOrderTop_mul_lower46
    (HahnSeries.C c * r ^ ar * q ^ aq * B ^ aB) (U ^ aU)
      (((0 + (ar : ℚ) * (-rho)) + (aq : ℚ) * (-2 * rho)) +
        (aB : ℚ) * (-3 * rho))
      ((aU : ℚ) * (-4 * rho)) hCrqB hUp
  have hstrict : -target * rho <
      (((0 + (ar : ℚ) * (-rho)) + (aq : ℚ) * (-2 * rho)) +
        (aB : ℚ) * (-3 * rho)) + (aU : ℚ) * (-4 * rho) := by
    nlinarith
  exact (WithTop.coe_lt_coe.mpr hstrict).trans_le (by
    simpa only [weightedMonomial46] using hfull)

/-- The boundary coefficient of a weighted monomial is the corresponding
monomial in the four boundary coefficients. -/
theorem weightedMonomial46_coeff_at_weight
    (c : k) (r q B U : HahnSeries ℚ k)
    (ar aq aB aU : ℕ) (rho : ℚ)
    (hr : (↑(-rho) : WithTop ℚ) ≤ r.orderTop)
    (hq : (↑(-2 * rho) : WithTop ℚ) ≤ q.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hU : (↑(-4 * rho) : WithTop ℚ) ≤ U.orderTop) :
    (weightedMonomial46 c r q B U ar aq aB aU).coeff
        (-((ar : ℚ) + 2 * aq + 3 * aB + 4 * aU) * rho) =
      c * (r.coeff (-rho)) ^ ar * (q.coeff (-2 * rho)) ^ aq *
        (B.coeff (-3 * rho)) ^ aB * (U.coeff (-4 * rho)) ^ aU := by
  have hC : (0 : WithTop ℚ) ≤
      (HahnSeries.C c : HahnSeries ℚ k).orderTop :=
    hahnOrderTop_C_nonneg46 c
  have hrp := hahnOrderTop_pow_lower46 r (-rho) ar hr
  have hqp := hahnOrderTop_pow_lower46 q (-2 * rho) aq hq
  have hBp := hahnOrderTop_pow_lower46 B (-3 * rho) aB hB
  have hUp := hahnOrderTop_pow_lower46 U (-4 * rho) aU hU
  have hCr := hahnOrderTop_mul_lower46
    (HahnSeries.C c) (r ^ ar) 0 ((ar : ℚ) * (-rho)) hC hrp
  have hCrq := hahnOrderTop_mul_lower46
    (HahnSeries.C c * r ^ ar) (q ^ aq)
      (0 + (ar : ℚ) * (-rho)) ((aq : ℚ) * (-2 * rho)) hCr hqp
  have hCrqB := hahnOrderTop_mul_lower46
    (HahnSeries.C c * r ^ ar * q ^ aq) (B ^ aB)
      ((0 + (ar : ℚ) * (-rho)) + (aq : ℚ) * (-2 * rho))
      ((aB : ℚ) * (-3 * rho)) hCrq hBp
  rw [weightedMonomial46]
  rw [show -((ar : ℚ) + 2 * aq + 3 * aB + 4 * aU) * rho =
      (((0 + (ar : ℚ) * (-rho)) + (aq : ℚ) * (-2 * rho)) +
        (aB : ℚ) * (-3 * rho)) + (aU : ℚ) * (-4 * rho) by ring]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c * r ^ ar * q ^ aq * B ^ aB) (U ^ aU)
      (((0 + (ar : ℚ) * (-rho)) + (aq : ℚ) * (-2 * rho)) +
        (aB : ℚ) * (-3 * rho)) ((aU : ℚ) * (-4 * rho)) hCrqB hUp]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c * r ^ ar * q ^ aq) (B ^ aB)
      ((0 + (ar : ℚ) * (-rho)) + (aq : ℚ) * (-2 * rho))
      ((aB : ℚ) * (-3 * rho)) hCrq hBp]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c * r ^ ar) (q ^ aq)
      (0 + (ar : ℚ) * (-rho)) ((aq : ℚ) * (-2 * rho)) hCr hqp]
  rw [hahnCoeff_mul_at_lower46
    (HahnSeries.C c) (r ^ ar) 0 ((ar : ℚ) * (-rho)) hC hrp]
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same,
    hahnCoeff_pow_at_lower46 r (-rho) ar hr,
    hahnCoeff_pow_at_lower46 q (-2 * rho) aq hq,
    hahnCoeff_pow_at_lower46 B (-3 * rho) aB hB,
    hahnCoeff_pow_at_lower46 U (-4 * rho) aU hU]

/-- The terms of the second boundary equation below weighted degree six. -/
def weightedInfinityGHigher46
    (L beta gamma delta : k) (r q B U : HahnSeries ℚ k) :
    HahnSeries ℚ k :=
  weightedMonomial46 ((3 / 8 : k) * L) r q B U 5 0 0 0 +
  (weightedMonomial46 ((-5 / 4 : k) * L) r q B U 3 1 0 0 +
  (weightedMonomial46 ((-1 / 2 : k) * beta) r q B U 3 0 0 0 +
  (weightedMonomial46 ((5 / 8 : k) * L) r q B U 2 0 1 0 +
  (weightedMonomial46 ((15 / 8 : k) * L) r q B U 1 2 0 0 +
  (weightedMonomial46 ((3 / 2 : k) * beta) r q B U 1 1 0 0 +
  (weightedMonomial46 ((-5 / 16 : k) * L) r q B U 1 0 0 1 +
  (weightedMonomial46 delta r q B U 1 0 0 0 +
  (weightedMonomial46 ((5 / 8 : k) * L) r q B U 0 1 1 0 +
  (weightedMonomial46 gamma r q B U 0 1 0 0 +
  weightedMonomial46 ((3 / 4 : k) * beta) r q B U 0 0 1 0)))))))))

/-- The terms of the first coefficient-curve row below weighted degree
seven, after substituting `A = 2q - 2r²`. -/
def weightedInfinityJTwoHigher46
    (L beta gamma delta k2 : k) (r q B U : HahnSeries ℚ k) :
    HahnSeries ℚ k :=
  weightedMonomial46 ((-5 / 4 : k) * L) r q B U 6 0 0 0 +
  (weightedMonomial46 ((15 / 4 : k) * L) r q B U 4 1 0 0 +
  (weightedMonomial46 ((3 / 2 : k) * beta) r q B U 4 0 0 0 +
  (weightedMonomial46 ((-15 / 4 : k) * L) r q B U 2 2 0 0 +
  (weightedMonomial46 (-3 * beta) r q B U 2 1 0 0 +
  (weightedMonomial46 ((5 / 8 : k) * L) r q B U 2 0 0 1 +
  (weightedMonomial46 (-2 * delta) r q B U 2 0 0 0 +
  (weightedMonomial46 ((5 / 4 : k) * L) r q B U 0 3 0 0 +
  (weightedMonomial46 ((3 / 2 : k) * beta) r q B U 0 2 0 0 +
  (weightedMonomial46 ((-5 / 8 : k) * L) r q B U 0 1 0 1 +
  (weightedMonomial46 (2 * delta) r q B U 0 1 0 0 +
  (weightedMonomial46 ((5 / 8 : k) * L) r q B U 0 0 2 0 +
  (weightedMonomial46 (2 * gamma) r q B U 0 0 1 0 +
  (weightedMonomial46 ((-3 / 4 : k) * beta) r q B U 0 0 0 1 +
  weightedMonomial46 (-k2) r q B U 0 0 0 0)))))))))))))

/-- The terms of the second coefficient-curve row below weighted degree
eight, after substituting `A = 2q - 2r²`. -/
def weightedInfinityJOneHigher46
    (L beta gamma delta k1 : k) (r q B U : HahnSeries ℚ k) :
    HahnSeries ℚ k :=
  weightedMonomial46 ((-5 / 8 : k) * L) r q B U 4 0 1 0 +
  (weightedMonomial46 ((5 / 4 : k) * L) r q B U 2 1 1 0 +
  (weightedMonomial46 ((3 / 2 : k) * beta) r q B U 2 0 1 0 +
  (weightedMonomial46 ((-5 / 8 : k) * L) r q B U 0 2 1 0 +
  (weightedMonomial46 ((-3 / 2 : k) * beta) r q B U 0 1 1 0 +
  (weightedMonomial46 ((-5 / 16 : k) * L) r q B U 0 0 1 1 +
  (weightedMonomial46 delta r q B U 0 0 1 0 +
  (weightedMonomial46 ((-1 / 2 : k) * gamma) r q B U 0 0 0 1 +
  weightedMonomial46 (-k1) r q B U 0 0 0 0)))))))

theorem boundaryE46_eq_weightedInfinity_faces
    (L beta gamma delta : k) (r q B U : HahnSeries ℚ k) :
    boundaryE46 (HahnSeries.C L) r q B U (HahnSeries.C beta)
        (HahnSeries.C gamma) (HahnSeries.C delta) =
      weightedInfinityG46 r q B U +
        weightedInfinityGHigher46 L beta gamma delta r q B U := by
  simp only [boundaryE46, weightedInfinityG46, weightedInfinityGHigher46,
    weightedMonomial46]
  simp only [map_mul, map_div₀, map_neg, map_ofNat, map_one]
  ring_nf

theorem coefficientCurveTwo46_eq_weightedInfinity_faces
    (L beta gamma delta k2 : k) (r q B U : HahnSeries ℚ k) :
    coefficientCurveTwo46 (HahnSeries.C L) (2 * q - 2 * r ^ 2) B U
        (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta) -
        HahnSeries.C k2 =
      weightedInfinityJTwo46 B U +
        weightedInfinityJTwoHigher46 L beta gamma delta k2 r q B U := by
  simp only [coefficientCurveTwo46, weightedInfinityJTwo46,
    weightedInfinityJTwoHigher46, weightedMonomial46]
  simp only [map_mul, map_div₀, map_neg, map_ofNat, map_one]
  field_simp [hahnNatCast_ne_zero46 (k := k) 2 (by norm_num),
    hahnNatCast_ne_zero46 (k := k) 4 (by norm_num),
    hahnNatCast_ne_zero46 (k := k) 8 (by norm_num),
    hahnNatCast_ne_zero46 (k := k) 16 (by norm_num),
    hahnNatCast_ne_zero46 (k := k) 32 (by norm_num)]
  ring

theorem coefficientCurveOne46_eq_weightedInfinity_faces
    (L beta gamma delta k1 : k) (r q B U : HahnSeries ℚ k) :
    coefficientCurveOne46 (HahnSeries.C L) (2 * q - 2 * r ^ 2) B U
        (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta) -
        HahnSeries.C k1 =
      weightedInfinityJOne46 r q B U +
        weightedInfinityJOneHigher46 L beta gamma delta k1 r q B U := by
  simp only [coefficientCurveOne46, weightedInfinityJOne46,
    weightedInfinityJOneHigher46, weightedMonomial46]
  simp only [map_mul, map_div₀, map_neg, map_ofNat, map_one]
  field_simp [hahnNatCast_ne_zero46 (k := k) 2 (by norm_num),
    hahnNatCast_ne_zero46 (k := k) 4 (by norm_num),
    hahnNatCast_ne_zero46 (k := k) 8 (by norm_num),
    hahnNatCast_ne_zero46 (k := k) 16 (by norm_num),
    hahnNatCast_ne_zero46 (k := k) 32 (by norm_num)]
  ring

/-- All non-leading terms of the second boundary row lie strictly above
weighted order `-6*rho`. -/
theorem weightedInfinityGHigher46_orderTop_gt
    (L beta gamma delta : k) (r q B U : HahnSeries ℚ k) (rho : ℚ)
    (hrho : 0 < rho)
    (hr : (↑(-rho) : WithTop ℚ) ≤ r.orderTop)
    (hq : (↑(-2 * rho) : WithTop ℚ) ≤ q.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hU : (↑(-4 * rho) : WithTop ℚ) ≤ U.orderTop) :
    (↑(-6 * rho) : WithTop ℚ) <
      (weightedInfinityGHigher46 L beta gamma delta r q B U).orderTop := by
  simp only [weightedInfinityGHigher46]
  repeat' apply hahnOrderTop_add_gt46
  all_goals
    apply weightedMonomial46_orderTop_gt <;> try assumption
  all_goals norm_num

/-- All non-leading terms of the first coefficient-curve row lie strictly
above weighted order `-7*rho`. -/
theorem weightedInfinityJTwoHigher46_orderTop_gt
    (L beta gamma delta k2 : k) (r q B U : HahnSeries ℚ k) (rho : ℚ)
    (hrho : 0 < rho)
    (hr : (↑(-rho) : WithTop ℚ) ≤ r.orderTop)
    (hq : (↑(-2 * rho) : WithTop ℚ) ≤ q.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hU : (↑(-4 * rho) : WithTop ℚ) ≤ U.orderTop) :
    (↑(-7 * rho) : WithTop ℚ) <
      (weightedInfinityJTwoHigher46 L beta gamma delta k2 r q B U).orderTop := by
  simp only [weightedInfinityJTwoHigher46]
  repeat' apply hahnOrderTop_add_gt46
  all_goals
    apply weightedMonomial46_orderTop_gt <;> try assumption
  all_goals norm_num

/-- All non-leading terms of the second coefficient-curve row lie strictly
above weighted order `-8*rho`. -/
theorem weightedInfinityJOneHigher46_orderTop_gt
    (L beta gamma delta k1 : k) (r q B U : HahnSeries ℚ k) (rho : ℚ)
    (hrho : 0 < rho)
    (hr : (↑(-rho) : WithTop ℚ) ≤ r.orderTop)
    (hq : (↑(-2 * rho) : WithTop ℚ) ≤ q.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hU : (↑(-4 * rho) : WithTop ℚ) ≤ U.orderTop) :
    (↑(-8 * rho) : WithTop ℚ) <
      (weightedInfinityJOneHigher46 L beta gamma delta k1 r q B U).orderTop := by
  simp only [weightedInfinityJOneHigher46]
  repeat' apply hahnOrderTop_add_gt46
  all_goals
    apply weightedMonomial46_orderTop_gt <;> try assumption
  all_goals norm_num

theorem weightedInfinityF46_eq_weightedMonomials
    (r q B U : HahnSeries ℚ k) :
    weightedInfinityF46 r q B U =
      weightedMonomial46 1 r q B U 1 0 1 0 +
      weightedMonomial46 1 r q B U 0 2 0 0 +
      weightedMonomial46 (-1 / 4 : k) r q B U 0 0 0 1 := by
  simp only [weightedInfinityF46, weightedMonomial46]
  simp only [map_div₀, map_neg, map_ofNat, map_one]
  ring

theorem weightedInfinityG46_eq_weightedMonomials
    (r q B U : HahnSeries ℚ k) :
    weightedInfinityG46 r q B U =
      weightedMonomial46 1 r q B U 0 3 0 0 +
      weightedMonomial46 (3 / 2 : k) r q B U 1 1 1 0 +
      weightedMonomial46 (-3 / 8 : k) r q B U 0 1 0 1 +
      weightedMonomial46 (3 / 8 : k) r q B U 0 0 2 0 := by
  simp only [weightedInfinityG46, weightedMonomial46]
  simp only [map_div₀, map_neg, map_ofNat, map_one]
  ring

theorem weightedInfinityJTwo46_eq_weightedMonomial
    (r q B U : HahnSeries ℚ k) :
    weightedInfinityJTwo46 B U =
      weightedMonomial46 (-3 / 4 : k) r q B U 0 0 1 1 := by
  simp only [weightedInfinityJTwo46, weightedMonomial46]
  simp only [map_div₀, map_neg, map_ofNat, map_one]
  ring

theorem weightedInfinityJOne46_eq_weightedMonomials
    (r q B U : HahnSeries ℚ k) :
    weightedInfinityJOne46 r q B U =
      weightedMonomial46 (3 / 2 : k) r q B U 2 0 2 0 +
      weightedMonomial46 (-3 / 2 : k) r q B U 0 1 2 0 +
      weightedMonomial46 (3 / 32 : k) r q B U 0 0 0 2 := by
  simp only [weightedInfinityJOne46, weightedMonomial46]
  simp only [map_div₀, map_neg, map_ofNat, map_one]
  ring

/-- The coefficient of the weight-four form is its evaluation on the four
weighted boundary coefficients. -/
theorem weightedInfinityF46_coeff_at_weight
    (r q B U : HahnSeries ℚ k) (rho : ℚ)
    (hr : (↑(-rho) : WithTop ℚ) ≤ r.orderTop)
    (hq : (↑(-2 * rho) : WithTop ℚ) ≤ q.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hU : (↑(-4 * rho) : WithTop ℚ) ≤ U.orderTop) :
    (weightedInfinityF46 r q B U).coeff (-4 * rho) =
      weightedInfinityF46 (r.coeff (-rho)) (q.coeff (-2 * rho))
        (B.coeff (-3 * rho)) (U.coeff (-4 * rho)) := by
  have h1 := weightedMonomial46_coeff_at_weight
    (1 : k) r q B U 1 0 1 0 rho hr hq hB hU
  have h2 := weightedMonomial46_coeff_at_weight
    (1 : k) r q B U 0 2 0 0 rho hr hq hB hU
  have h3 := weightedMonomial46_coeff_at_weight
    (-1 / 4 : k) r q B U 0 0 0 1 rho hr hq hB hU
  norm_num at h1 h2 h3
  ring_nf at h1 h2 h3
  rw [weightedInfinityF46_eq_weightedMonomials,
    HahnSeries.coeff_add, HahnSeries.coeff_add]
  ring_nf
  rw [h1, h2, h3]
  simp only [weightedInfinityF46]
  ring

/-- The coefficient of the weight-six form is its evaluation on the four
weighted boundary coefficients. -/
theorem weightedInfinityG46_coeff_at_weight
    (r q B U : HahnSeries ℚ k) (rho : ℚ)
    (hr : (↑(-rho) : WithTop ℚ) ≤ r.orderTop)
    (hq : (↑(-2 * rho) : WithTop ℚ) ≤ q.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hU : (↑(-4 * rho) : WithTop ℚ) ≤ U.orderTop) :
    (weightedInfinityG46 r q B U).coeff (-6 * rho) =
      weightedInfinityG46 (r.coeff (-rho)) (q.coeff (-2 * rho))
        (B.coeff (-3 * rho)) (U.coeff (-4 * rho)) := by
  have h1 := weightedMonomial46_coeff_at_weight
    (1 : k) r q B U 0 3 0 0 rho hr hq hB hU
  have h2 := weightedMonomial46_coeff_at_weight
    (3 / 2 : k) r q B U 1 1 1 0 rho hr hq hB hU
  have h3 := weightedMonomial46_coeff_at_weight
    (-3 / 8 : k) r q B U 0 1 0 1 rho hr hq hB hU
  have h4 := weightedMonomial46_coeff_at_weight
    (3 / 8 : k) r q B U 0 0 2 0 rho hr hq hB hU
  norm_num at h1 h2 h3 h4
  ring_nf at h1 h2 h3 h4
  rw [weightedInfinityG46_eq_weightedMonomials,
    HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add]
  ring_nf
  rw [h1, h2, h3, h4]
  simp only [weightedInfinityG46]
  ring

/-- The coefficient of the weight-seven form is its evaluation on the
weighted boundary coefficients. -/
theorem weightedInfinityJTwo46_coeff_at_weight
    (r q B U : HahnSeries ℚ k) (rho : ℚ)
    (hr : (↑(-rho) : WithTop ℚ) ≤ r.orderTop)
    (hq : (↑(-2 * rho) : WithTop ℚ) ≤ q.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hU : (↑(-4 * rho) : WithTop ℚ) ≤ U.orderTop) :
    (weightedInfinityJTwo46 B U).coeff (-7 * rho) =
      weightedInfinityJTwo46 (B.coeff (-3 * rho))
        (U.coeff (-4 * rho)) := by
  have h := weightedMonomial46_coeff_at_weight
    (-3 / 4 : k) r q B U 0 0 1 1 rho hr hq hB hU
  norm_num at h
  ring_nf at h
  rw [weightedInfinityJTwo46_eq_weightedMonomial r q B U]
  ring_nf
  rw [h]
  simp only [weightedInfinityJTwo46]
  ring

/-- The coefficient of the weight-eight form is its evaluation on the
four weighted boundary coefficients. -/
theorem weightedInfinityJOne46_coeff_at_weight
    (r q B U : HahnSeries ℚ k) (rho : ℚ)
    (hr : (↑(-rho) : WithTop ℚ) ≤ r.orderTop)
    (hq : (↑(-2 * rho) : WithTop ℚ) ≤ q.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hU : (↑(-4 * rho) : WithTop ℚ) ≤ U.orderTop) :
    (weightedInfinityJOne46 r q B U).coeff (-8 * rho) =
      weightedInfinityJOne46 (r.coeff (-rho)) (q.coeff (-2 * rho))
        (B.coeff (-3 * rho)) (U.coeff (-4 * rho)) := by
  have h1 := weightedMonomial46_coeff_at_weight
    (3 / 2 : k) r q B U 2 0 2 0 rho hr hq hB hU
  have h2 := weightedMonomial46_coeff_at_weight
    (-3 / 2 : k) r q B U 0 1 2 0 rho hr hq hB hU
  have h3 := weightedMonomial46_coeff_at_weight
    (3 / 32 : k) r q B U 0 0 0 2 rho hr hq hB hU
  norm_num at h1 h2 h3
  ring_nf at h1 h2 h3
  rw [weightedInfinityJOne46_eq_weightedMonomials,
    HahnSeries.coeff_add, HahnSeries.coeff_add]
  ring_nf
  rw [h1, h2, h3]
  simp only [weightedInfinityJOne46]
  ring

/-- The four exact coefficient-curve equations force the four weighted
initial forms to vanish at every positive common pole radius. -/
theorem weightedInfinity_initialForms_zero46
    (L beta gamma delta k2 k1 : k)
    (r q B U D E : HahnSeries ℚ k) (rho : ℚ)
    (hrho : 0 < rho)
    (hr : (↑(-rho) : WithTop ℚ) ≤ r.orderTop)
    (hq : (↑(-2 * rho) : WithTop ℚ) ≤ q.orderTop)
    (hB : (↑(-3 * rho) : WithTop ℚ) ≤ B.orderTop)
    (hU : (↑(-4 * rho) : WithTop ℚ) ≤ U.orderTop)
    (hDreg : (0 : WithTop ℚ) ≤ D.orderTop)
    (hEreg : (0 : WithTop ℚ) ≤ E.orderTop)
    (hD : boundaryD46 r q B U = D)
    (hE : boundaryE46 (HahnSeries.C L) r q B U
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta) = E)
    (hJ2 : coefficientCurveTwo46 (HahnSeries.C L) (2 * q - 2 * r ^ 2)
      B U (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) = HahnSeries.C k2)
    (hJ1 : coefficientCurveOne46 (HahnSeries.C L) (2 * q - 2 * r ^ 2)
      B U (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) = HahnSeries.C k1) :
    weightedInfinityF46 (r.coeff (-rho)) (q.coeff (-2 * rho))
        (B.coeff (-3 * rho)) (U.coeff (-4 * rho)) = 0 ∧
      weightedInfinityG46 (r.coeff (-rho)) (q.coeff (-2 * rho))
        (B.coeff (-3 * rho)) (U.coeff (-4 * rho)) = 0 ∧
      weightedInfinityJTwo46 (B.coeff (-3 * rho))
        (U.coeff (-4 * rho)) = 0 ∧
      weightedInfinityJOne46 (r.coeff (-rho)) (q.coeff (-2 * rho))
        (B.coeff (-3 * rho)) (U.coeff (-4 * rho)) = 0 := by
  have hneg4 : (↑(-4 * rho) : WithTop ℚ) < 0 :=
    WithTop.coe_lt_coe.mpr (by linarith)
  have hneg6 : (↑(-6 * rho) : WithTop ℚ) < 0 :=
    WithTop.coe_lt_coe.mpr (by linarith)
  have hD0 : D.coeff (-4 * rho) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (hneg4.trans_le hDreg)
  have hE0 : E.coeff (-6 * rho) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (hneg6.trans_le hEreg)
  have hGhigh0 :
      (weightedInfinityGHigher46 L beta gamma delta r q B U).coeff
        (-6 * rho) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (weightedInfinityGHigher46_orderTop_gt L beta gamma delta
        r q B U rho hrho hr hq hB hU)
  have hJ2high0 :
      (weightedInfinityJTwoHigher46 L beta gamma delta k2 r q B U).coeff
        (-7 * rho) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (weightedInfinityJTwoHigher46_orderTop_gt L beta gamma delta k2
        r q B U rho hrho hr hq hB hU)
  have hJ1high0 :
      (weightedInfinityJOneHigher46 L beta gamma delta k1 r q B U).coeff
        (-8 * rho) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (weightedInfinityJOneHigher46_orderTop_gt L beta gamma delta k1
        r q B U rho hrho hr hq hB hU)
  have hFzero : weightedInfinityF46 (r.coeff (-rho)) (q.coeff (-2 * rho))
      (B.coeff (-3 * rho)) (U.coeff (-4 * rho)) = 0 := by
    have hcoeff := congrArg (fun x : HahnSeries ℚ k => x.coeff (-4 * rho)) hD
    rw [show boundaryD46 r q B U = weightedInfinityF46 r q B U by rfl,
      weightedInfinityF46_coeff_at_weight r q B U rho hr hq hB hU,
      hD0] at hcoeff
    exact hcoeff
  have hGzero : weightedInfinityG46 (r.coeff (-rho)) (q.coeff (-2 * rho))
      (B.coeff (-3 * rho)) (U.coeff (-4 * rho)) = 0 := by
    have hface : weightedInfinityG46 r q B U +
        weightedInfinityGHigher46 L beta gamma delta r q B U = E := by
      rw [← boundaryE46_eq_weightedInfinity_faces]
      exact hE
    have hcoeff := congrArg (fun x : HahnSeries ℚ k => x.coeff (-6 * rho)) hface
    rw [HahnSeries.coeff_add,
      weightedInfinityG46_coeff_at_weight r q B U rho hr hq hB hU,
      hGhigh0, hE0, add_zero] at hcoeff
    exact hcoeff
  have hJ2zero : weightedInfinityJTwo46 (B.coeff (-3 * rho))
      (U.coeff (-4 * rho)) = 0 := by
    have hrow : coefficientCurveTwo46 (HahnSeries.C L) (2 * q - 2 * r ^ 2)
        B U (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) - HahnSeries.C k2 = 0 := sub_eq_zero.mpr hJ2
    rw [coefficientCurveTwo46_eq_weightedInfinity_faces] at hrow
    have hcoeff := congrArg (fun x : HahnSeries ℚ k => x.coeff (-7 * rho)) hrow
    rw [HahnSeries.coeff_add,
      weightedInfinityJTwo46_coeff_at_weight r q B U rho hr hq hB hU,
      hJ2high0, HahnSeries.coeff_zero, add_zero] at hcoeff
    exact hcoeff
  have hJ1zero : weightedInfinityJOne46 (r.coeff (-rho)) (q.coeff (-2 * rho))
      (B.coeff (-3 * rho)) (U.coeff (-4 * rho)) = 0 := by
    have hrow : coefficientCurveOne46 (HahnSeries.C L) (2 * q - 2 * r ^ 2)
        B U (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) - HahnSeries.C k1 = 0 := sub_eq_zero.mpr hJ1
    rw [coefficientCurveOne46_eq_weightedInfinity_faces] at hrow
    have hcoeff := congrArg (fun x : HahnSeries ℚ k => x.coeff (-8 * rho)) hrow
    rw [HahnSeries.coeff_add,
      weightedInfinityJOne46_coeff_at_weight r q B U rho hr hq hB hU,
      hJ1high0, HahnSeries.coeff_zero, add_zero] at hcoeff
    exact hcoeff
  exact ⟨hFzero, hGzero, hJ2zero, hJ1zero⟩

/-- A genuine pole on the exact coefficient curve can only approach the
unique weighted point `[1:0:0:0]`: `r` has the dominant pole and the other
three coordinates lie strictly above their weighted bounds. -/
theorem weightedInfinity_dominant_r46
    (L beta gamma delta k2 k1 : k)
    (r q B U D E : HahnSeries ℚ k)
    (hpole : ¬ ((0 : WithTop ℚ) ≤ r.orderTop ∧
      (0 : WithTop ℚ) ≤ q.orderTop ∧
      (0 : WithTop ℚ) ≤ B.orderTop ∧
      (0 : WithTop ℚ) ≤ U.orderTop))
    (hDreg : (0 : WithTop ℚ) ≤ D.orderTop)
    (hEreg : (0 : WithTop ℚ) ≤ E.orderTop)
    (hD : boundaryD46 r q B U = D)
    (hE : boundaryE46 (HahnSeries.C L) r q B U
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta) = E)
    (hJ2 : coefficientCurveTwo46 (HahnSeries.C L) (2 * q - 2 * r ^ 2)
      B U (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) = HahnSeries.C k2)
    (hJ1 : coefficientCurveOne46 (HahnSeries.C L) (2 * q - 2 * r ^ 2)
      B U (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) = HahnSeries.C k1) :
    ∃ rho : ℚ, 0 < rho ∧
      r.orderTop = (↑(-rho) : WithTop ℚ) ∧
      (↑(-2 * rho) : WithTop ℚ) < q.orderTop ∧
      (↑(-3 * rho) : WithTop ℚ) < B.orderTop ∧
      (↑(-4 * rho) : WithTop ℚ) < U.orderTop := by
  have hpoleOrder : r.order < 0 ∨ q.order < 0 ∨
      B.order < 0 ∨ U.order < 0 := by
    rw [HahnSeries.zero_le_orderTop_iff, HahnSeries.zero_le_orderTop_iff,
      HahnSeries.zero_le_orderTop_iff, HahnSeries.zero_le_orderTop_iff] at hpole
    by_cases hr0 : 0 ≤ r.order
    · by_cases hq0 : 0 ≤ q.order
      · by_cases hB0 : 0 ≤ B.order
        · exact Or.inr (Or.inr (Or.inr (lt_of_not_ge (fun hU0 =>
            hpole ⟨hr0, hq0, hB0, hU0⟩))))
        · exact Or.inr (Or.inr (Or.inl (lt_of_not_ge hB0)))
      · exact Or.inr (Or.inl (lt_of_not_ge hq0))
    · exact Or.inl (lt_of_not_ge hr0)
  let rho := weightedPoleRadius46 r q B U
  have hrho : 0 < rho := weightedPoleRadius46_pos r q B U hpoleOrder
  have hr := weightedPoleRadius46_r_lower r q B U
  have hq := weightedPoleRadius46_q_lower r q B U
  have hB := weightedPoleRadius46_B_lower r q B U
  have hU := weightedPoleRadius46_U_lower r q B U
  have hinitial := weightedInfinity_initialForms_zero46
    L beta gamma delta k2 k1 r q B U D E rho hrho hr hq hB hU
      hDreg hEreg hD hE hJ2 hJ1
  rcases hinitial with ⟨hF0, hG0, hJ20, hJ10⟩
  rcases weightedInfinity_commonZeros46
      (r.coeff (-rho)) (q.coeff (-2 * rho))
      (B.coeff (-3 * rho)) (U.coeff (-4 * rho))
      hF0 hG0 hJ20 hJ10 with ⟨hB0, hU0, hq0⟩
  have hattain := weightedPoleRadius46_attained r q B U
  have hrOrder : r.order = -rho := by
    rcases hattain with hratt | hqatt | hBatt | hUatt
    · linarith
    · have hqOrder : q.order = -2 * rho := by
        linarith
      exact (hahnCoeff_ne_zero_of_order_eq_neg_weight46
        q rho 2 hrho (by norm_num) hqOrder hq0).elim
    · have hBOrder : B.order = -3 * rho := by
        linarith
      exact (hahnCoeff_ne_zero_of_order_eq_neg_weight46
        B rho 3 hrho (by norm_num) hBOrder hB0).elim
    · have hUOrder : U.order = -4 * rho := by
        linarith
      exact (hahnCoeff_ne_zero_of_order_eq_neg_weight46
        U rho 4 hrho (by norm_num) hUOrder hU0).elim
  have hrCoeff : r.coeff (-rho) ≠ 0 :=
    by simpa only [neg_mul, one_mul] using
      (hahnCoeff_ne_zero_of_order_eq_neg_weight46
        r rho 1 hrho (by norm_num) (by simpa only [neg_mul, one_mul] using hrOrder))
  have hrne : r ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hrCoeff
  have hrExact : r.orderTop = (↑(-rho) : WithTop ℚ) := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hrne, hrOrder]
  have hqStrict : (↑(-2 * rho) : WithTop ℚ) < q.orderTop :=
    lt_of_le_of_ne hq (Ne.symm (HahnSeries.orderTop_ne_of_coeff_eq_zero hq0))
  have hBStrict : (↑(-3 * rho) : WithTop ℚ) < B.orderTop :=
    lt_of_le_of_ne hB (Ne.symm (HahnSeries.orderTop_ne_of_coeff_eq_zero hB0))
  have hUStrict : (↑(-4 * rho) : WithTop ℚ) < U.orderTop :=
    lt_of_le_of_ne hU (Ne.symm (HahnSeries.orderTop_ne_of_coeff_eq_zero hU0))
  exact ⟨rho, hrho, hrExact, hqStrict, hBStrict, hUStrict⟩

end WeightedInitialForms

section SourcePoleSpecialization

variable {k : Type*} [Field k] [CharZero k]

local instance sourceHahnCharZero46 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The inverse of a nonzero Hahn series negates its finite order. -/
theorem hahnOrderTop_inv_eq_neg46
    (x : HahnSeries ℚ k) (a : ℚ) (hx : x ≠ 0)
    (horder : x.orderTop = (↑a : WithTop ℚ)) :
    x⁻¹.orderTop = (↑(-a) : WithTop ℚ) := by
  have hinv : x⁻¹ ≠ 0 := inv_ne_zero hx
  have hxord : x.order = a := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hx, horder]
  have hmul : (x * x⁻¹).order = x.order + x⁻¹.order := by
    apply HahnSeries.order_mul_of_ne_zero
    simp [hx]
  rw [mul_inv_cancel₀ hx, HahnSeries.order_one, hxord] at hmul
  have hinvord : x⁻¹.order = -a := by linarith
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hinv, hinvord]

/-- A strictly positive Hahn series is either zero or has a finite positive
order, in the format expected by the finite-pole exclusions. -/
theorem positiveFiniteOrZero46_of_orderTop_pos
    (x : HahnSeries ℚ k) (hx : (0 : WithTop ℚ) < x.orderTop) :
    PositiveFiniteOrZero46 x := by
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · right
    refine ⟨x.order, ?_, ?_⟩
    · have hx' : (↑(0 : ℚ) : WithTop ℚ) <
          (↑x.order : WithTop ℚ) := by
        rw [HahnSeries.order_eq_orderTop_of_ne_zero hx0]
        exact hx
      exact WithTop.coe_lt_coe.mp hx'
    · exact (HahnSeries.order_eq_orderTop_of_ne_zero hx0).symm

/-- Positive finite-or-zero order survives division of all exponents by a
positive rational. -/
theorem normalizeHahnOrder46_positiveFiniteOrZero
    (rho : ℚ) (hrho : 0 < rho) (x : HahnSeries ℚ k)
    (hx : (0 : WithTop ℚ) < x.orderTop) :
    PositiveFiniteOrZero46 (normalizeHahnOrder46 rho hrho x) := by
  rcases positiveFiniteOrZero46_of_orderTop_pos x hx with hx0 | ⟨a, ha, horder⟩
  · left
    simp [hx0]
  · right
    refine ⟨a / rho, div_pos ha hrho, ?_⟩
    rw [normalizeHahnOrder46_orderTop, horder, WithTop.map_coe]
    rfl

/-- At any zero of the common core, the literal source package reaches the
unique weighted infinity point.  This is the source-level bridge consumed
by the scale-two closure. -/
theorem SquareConstantLSourceCurveData46.weightedInfinity_dominant_at_root
    {p q : k[X][X]} {j : k} {h0 : k[X]} {l : k}
    (S : SquareConstantLSourceCurveData46 p q j h0 l)
    (a : k) (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0) (hj : j ≠ 0) :
    ∃ rho : ℚ, 0 < rho ∧
      (ratFuncAtHahn46 a S.r).orderTop = (↑(-rho) : WithTop ℚ) ∧
      (↑(-2 * rho) : WithTop ℚ) <
        (ratFuncAtHahn46 a (translatedQ46 S.r S.A)).orderTop ∧
      (↑(-3 * rho) : WithTop ℚ) <
        (ratFuncAtHahn46 a S.B).orderTop ∧
      (↑(-4 * rho) : WithTop ℚ) <
        (ratFuncAtHahn46 a (S.A ^ 2 - 4 * S.C0)).orderTop := by
  let rH : HahnSeries ℚ k := ratFuncAtHahn46 a S.r
  let qH : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (translatedQ46 S.r S.A)
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 a S.A
  let BH : HahnSeries ℚ k := ratFuncAtHahn46 a S.B
  let UH : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (S.A ^ 2 - 4 * S.C0)
  let D : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) (p.coeff 0))
  let E : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k)
      (q.coeff 0 - C S.alpha * p.coeff 0 - C S.epsilon))
  have hA : AH = 2 * qH - 2 * rH ^ 2 := by
    dsimp only [AH, qH, rH]
    simp only [translatedQ46, map_add, map_sub, map_mul, map_pow,
      map_div₀, map_ofNat, map_one]
    ring
  have hDreg : (0 : WithTop ℚ) ≤ D.orderTop := by
    dsimp only [D]
    exact ratFuncAtHahn46_polynomial_orderTop_nonneg a (p.coeff 0)
  have hEreg : (0 : WithTop ℚ) ≤ E.orderTop := by
    dsimp only [E]
    exact ratFuncAtHahn46_polynomial_orderTop_nonneg a
      (q.coeff 0 - C S.alpha * p.coeff 0 - C S.epsilon)
  have hD : boundaryD46 rH qH BH UH = D := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.boundaryD
    simpa only [rH, qH, BH, UH, D, boundaryD46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_ofNat, map_one] using hmapped
  have hE : boundaryE46 (HahnSeries.C l) rH qH BH UH
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) = E := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.boundaryE
    simpa only [rH, qH, BH, UH, E, boundaryE46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C] using hmapped
  have hJ2A : coefficientCurveTwo46 (HahnSeries.C l) AH BH UH
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) = HahnSeries.C S.k2 := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.curveTwo
    simpa only [AH, BH, UH, coefficientCurveTwo46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C] using hmapped
  have hJ1A : coefficientCurveOne46 (HahnSeries.C l) AH BH UH
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) = HahnSeries.C S.k1 := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.curveOne
    simpa only [AH, BH, UH, coefficientCurveOne46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C] using hmapped
  have hJ2 : coefficientCurveTwo46 (HahnSeries.C l)
      (2 * qH - 2 * rH ^ 2) BH UH
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) = HahnSeries.C S.k2 := by
    rw [← hA]
    exact hJ2A
  have hJ1 : coefficientCurveOne46 (HahnSeries.C l)
      (2 * qH - 2 * rH ^ 2) BH UH
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) = HahnSeries.C S.k1 := by
    rw [← hA]
    exact hJ1A
  have hcoordinatePole : ¬ ((0 : WithTop ℚ) ≤ AH.orderTop ∧
      (0 : WithTop ℚ) ≤ BH.orderTop ∧
      (0 : WithTop ℚ) ≤ UH.orderTop) := by
    apply sourceLastRow_forces_coordinate_pole46
      a h0 j l S.beta S.gamma S.delta S.A S.B
        (S.A ^ 2 - 4 * S.C0) hh0 hroot hj
    simpa only [ratFuncDerivation46_apply] using S.lastRow
  have hpole : ¬ ((0 : WithTop ℚ) ≤ rH.orderTop ∧
      (0 : WithTop ℚ) ≤ qH.orderTop ∧
      (0 : WithTop ℚ) ≤ BH.orderTop ∧
      (0 : WithTop ℚ) ≤ UH.orderTop) := by
    rintro ⟨hr, hq, hB, hU⟩
    have htwo : (0 : WithTop ℚ) ≤
        (2 : HahnSeries ℚ k).orderTop := by
      simpa using hahnOrderTop_natDiv_nonneg46 (k := k) 2 1
    have hAreg : (0 : WithTop ℚ) ≤ AH.orderTop := by
      rw [hA]
      apply hahnOrderTop_sub_nonneg46
      · exact hahnOrderTop_mul_nonneg46 _ _ htwo hq
      · exact hahnOrderTop_mul_nonneg46 _ _ htwo
          (hahnOrderTop_pow_nonneg46 rH 2 hr)
    exact hcoordinatePole ⟨hAreg, hB, hU⟩
  simpa only [rH, qH, BH, UH] using
    (weightedInfinity_dominant_r46 l S.beta S.gamma S.delta S.k2 S.k1
      rH qH BH UH D E hpole hDreg hEreg hD hE hJ2 hJ1)

/-- In the mismatch stratum `l ≠ 0`, a zero of the common core produces a
normalized positive local trajectory, contradicting the exhaustive
regular-load finite-pole theorem. -/
theorem SquareConstantLSourceCurveData46.mismatch_impossible_at_root
    {p q : k[X][X]} {j : k} {h0 : k[X]} {l : k}
    (S : SquareConstantLSourceCurveData46 p q j h0 l)
    (a : k) (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0)
    (hj : j ≠ 0) (hl : l ≠ 0) : False := by
  let rH : HahnSeries ℚ k := ratFuncAtHahn46 a S.r
  let qH : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (translatedQ46 S.r S.A)
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 a S.A
  let BH : HahnSeries ℚ k := ratFuncAtHahn46 a S.B
  let UH : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (S.A ^ 2 - 4 * S.C0)
  let D : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) (p.coeff 0))
  let E : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k)
      (q.coeff 0 - C S.alpha * p.coeff 0 - C S.epsilon))
  have hA : AH = 2 * qH - 2 * rH ^ 2 := by
    dsimp only [AH, qH, rH]
    simp only [translatedQ46, map_add, map_mul, map_pow,
      map_div₀, map_ofNat, map_one]
    ring
  have hDreg : (0 : WithTop ℚ) ≤ D.orderTop := by
    dsimp only [D]
    exact ratFuncAtHahn46_polynomial_orderTop_nonneg a (p.coeff 0)
  have hEreg : (0 : WithTop ℚ) ≤ E.orderTop := by
    dsimp only [E]
    exact ratFuncAtHahn46_polynomial_orderTop_nonneg a
      (q.coeff 0 - C S.alpha * p.coeff 0 - C S.epsilon)
  have hD : boundaryD46 rH qH BH UH = D := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.boundaryD
    simpa only [rH, qH, BH, UH, D, boundaryD46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_ofNat, map_one] using hmapped
  have hE : boundaryE46 (HahnSeries.C l) rH qH BH UH
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) = E := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.boundaryE
    simpa only [rH, qH, BH, UH, E, boundaryE46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C] using hmapped
  have hJ2A : coefficientCurveTwo46 (HahnSeries.C l) AH BH UH
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) = HahnSeries.C S.k2 := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.curveTwo
    simpa only [AH, BH, UH, coefficientCurveTwo46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C] using hmapped
  have hJ1A : coefficientCurveOne46 (HahnSeries.C l) AH BH UH
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) = HahnSeries.C S.k1 := by
    have hmapped := congrArg (ratFuncAtHahn46 a) S.curveOne
    simpa only [AH, BH, UH, coefficientCurveOne46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one,
      RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C] using hmapped
  rcases S.weightedInfinity_dominant_at_root a hh0 hroot hj with
    ⟨rho, hrho, hrPole, hqPole, hBPole, hUPole⟩
  change rH.orderTop = (↑(-rho) : WithTop ℚ) at hrPole
  change (↑(-2 * rho) : WithTop ℚ) < qH.orderTop at hqPole
  change (↑(-3 * rho) : WithTop ℚ) < BH.orderTop at hBPole
  change (↑(-4 * rho) : WithTop ℚ) < UH.orderTop at hUPole
  have hrHne : rH ≠ 0 := by
    intro hr0
    rw [hr0, HahnSeries.orderTop_zero] at hrPole
    exact WithTop.coe_ne_top hrPole.symm
  let s0 : HahnSeries ℚ k := rH⁻¹
  let Q0 : HahnSeries ℚ k := qH * s0 ^ 2
  let Y0 : HahnSeries ℚ k := BH * s0 ^ 3
  let Z0 : HahnSeries ℚ k := UH * s0 ^ 4
  have hs0ne : s0 ≠ 0 := inv_ne_zero hrHne
  have hs0Order : s0.orderTop = (↑rho : WithTop ℚ) := by
    dsimp only [s0]
    simpa only [neg_neg] using
      hahnOrderTop_inv_eq_neg46 rH (-rho) hrHne hrPole
  have hs02 : (s0 ^ 2).orderTop = (↑(2 * rho) : WithTop ℚ) := by
    simpa using hahnOrderTop_pow_eq46 s0 rho 2 hs0Order
  have hs03 : (s0 ^ 3).orderTop = (↑(3 * rho) : WithTop ℚ) := by
    simpa using hahnOrderTop_pow_eq46 s0 rho 3 hs0Order
  have hs04 : (s0 ^ 4).orderTop = (↑(4 * rho) : WithTop ℚ) := by
    simpa using hahnOrderTop_pow_eq46 s0 rho 4 hs0Order
  have hQ0pos : (0 : WithTop ℚ) < Q0.orderTop := by
    dsimp only [Q0]
    rw [HahnSeries.orderTop_mul, hs02]
    have h : (↑(-2 * rho) : WithTop ℚ) + ↑(2 * rho) <
        qH.orderTop + ↑(2 * rho) :=
      (add_lt_add_iff_left_of_ne_top WithTop.coe_ne_top).mpr hqPole
    rw [← WithTop.coe_add, show -2 * rho + 2 * rho = 0 by ring] at h
    exact h
  have hY0pos : (0 : WithTop ℚ) < Y0.orderTop := by
    dsimp only [Y0]
    rw [HahnSeries.orderTop_mul, hs03]
    have h : (↑(-3 * rho) : WithTop ℚ) + ↑(3 * rho) <
        BH.orderTop + ↑(3 * rho) :=
      (add_lt_add_iff_left_of_ne_top WithTop.coe_ne_top).mpr hBPole
    rw [← WithTop.coe_add, show -3 * rho + 3 * rho = 0 by ring] at h
    exact h
  have hZ0pos : (0 : WithTop ℚ) < Z0.orderTop := by
    dsimp only [Z0]
    rw [HahnSeries.orderTop_mul, hs04]
    have h : (↑(-4 * rho) : WithTop ℚ) + ↑(4 * rho) <
        UH.orderTop + ↑(4 * rho) :=
      (add_lt_add_iff_left_of_ne_top WithTop.coe_ne_top).mpr hUPole
    rw [← WithTop.coe_add, show -4 * rho + 4 * rho = 0 by ring] at h
    exact h
  have hrRecover : localChartR46 s0 = rH := by
    simp [localChartR46, s0]
  have hqRecover : localChartQ46 s0 Q0 = qH := by
    dsimp only [localChartQ46, Q0, s0]
    field_simp [hrHne]
  have hBRecover : localChartB46 s0 Y0 = BH := by
    dsimp only [localChartB46, Y0, s0]
    field_simp [hrHne]
  have hURecover : localChartU46 s0 Z0 = UH := by
    dsimp only [localChartU46, Z0, s0]
    field_simp [hrHne]
  have hARecover : localChartA46 s0 Q0 = AH := by
    simp only [localChartA46, hqRecover, hrRecover]
    exact hA.symm
  have hF0 : localChartF46 s0 Q0 Y0 Z0 D = 0 := by
    rw [← clear_boundaryD46_localChart s0 Q0 Y0 Z0 D hs0ne,
      hrRecover, hqRecover, hBRecover, hURecover, hD, sub_self, mul_zero]
  have hG0 : localChartG46 (HahnSeries.C l) s0 Q0 Y0 Z0
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) E = 0 := by
    rw [← clear_boundaryE46_localChart (HahnSeries.C l) s0 Q0 Y0 Z0
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) E hs0ne,
      hrRecover, hqRecover, hBRecover, hURecover, hE, sub_self, mul_zero]
  have hJ20 : localChartJTwo46 (HahnSeries.C l) s0 Q0 Y0 Z0
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k2) = 0 := by
    rw [← clear_coefficientCurveTwo46_localChart (HahnSeries.C l)
      s0 Q0 Y0 Z0 (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k2) hs0ne,
      hARecover, hBRecover, hURecover, hJ2A, sub_self, mul_zero]
  have hJ10 : localChartJOne46 (HahnSeries.C l) s0 Q0 Y0 Z0
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k1) = 0 := by
    rw [← clear_coefficientCurveOne46_localChart (HahnSeries.C l)
      s0 Q0 Y0 Z0 (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k1) hs0ne,
      hARecover, hBRecover, hURecover, hJ1A, sub_self, mul_zero]
  let N := normalizeHahnOrder46 (k := k) rho hrho
  let s := N s0
  let Q := N Q0
  let Y := N Y0
  let Z := N Z0
  let DN := N D
  let EN := N E
  have hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
    dsimp only [s, N]
    exact normalizeHahnOrder46_orderTop_eq_one rho hrho s0 hs0Order
  have hQcase : PositiveFiniteOrZero46 Q := by
    dsimp only [Q, N]
    exact normalizeHahnOrder46_positiveFiniteOrZero rho hrho Q0 hQ0pos
  have hYcase : PositiveFiniteOrZero46 Y := by
    dsimp only [Y, N]
    exact normalizeHahnOrder46_positiveFiniteOrZero rho hrho Y0 hY0pos
  have hZcase : PositiveFiniteOrZero46 Z := by
    dsimp only [Z, N]
    exact normalizeHahnOrder46_positiveFiniteOrZero rho hrho Z0 hZ0pos
  have hDN : (0 : WithTop ℚ) ≤ DN.orderTop := by
    dsimp only [DN, N]
    exact normalizeHahnOrder46_orderTop_nonneg rho hrho D hDreg
  have hEN : (0 : WithTop ℚ) ≤ EN.orderTop := by
    dsimp only [EN, N]
    exact normalizeHahnOrder46_orderTop_nonneg rho hrho E hEreg
  have hF : localChartF46 s Q Y Z DN = 0 := by
    have hmapped := congrArg N hF0
    simpa only [s, Q, Y, Z, DN, N, localChartF46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_ofNat, map_one, map_zero] using hmapped
  have hG : localChartG46 (HahnSeries.C l) s Q Y Z
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) EN = 0 := by
    have hmapped := congrArg N hG0
    simpa only [s, Q, Y, Z, EN, N, localChartG46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one, map_zero,
      normalizeHahnOrder46_C] using hmapped
  have hJ2 : localChartJTwo46 (HahnSeries.C l) s Q Y Z
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k2) = 0 := by
    have hmapped := congrArg N hJ20
    simpa only [s, Q, Y, Z, N, localChartJTwo46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one, map_zero,
      normalizeHahnOrder46_C] using hmapped
  have hJ1 : localChartJOne46 (HahnSeries.C l) s Q Y Z
      (HahnSeries.C S.beta) (HahnSeries.C S.gamma)
      (HahnSeries.C S.delta) (HahnSeries.C S.k1) = 0 := by
    have hmapped := congrArg N hJ10
    simpa only [s, Q, Y, Z, N, localChartJOne46, map_add, map_sub,
      map_mul, map_pow, map_div₀, map_neg, map_ofNat, map_one, map_zero,
      normalizeHahnOrder46_C] using hmapped
  exact mismatchFinitePole46_exhaustive_regular
    l S.beta S.gamma S.delta DN EN S.k2 S.k1 s Q Y Z hl hDN hEN hs
      hQcase hYcase hZcase hF hG hJ2 hJ1

open scoped Polynomial.Bivariate

/-- The nonaligned square branch of a normalized scale-two `(4,6)` source
is impossible.  Its square root has degree one, so its unique finite root
feeds the weighted-infinity contradiction above. -/
theorem normalized46ScaleTwo_squareBranch_impossible
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]} {lambda : k}
    (hsource : Normalized46LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hlambda : lambda ≠ 0) (hH : H = h0 ^ 2)
    (hmismatch :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (3 : k[X]) * p.coeff 3 * H - (2 : k[X]) * q.coeff 5 =
        C lambda * h0 ^ 5) : False := by
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp4, hq6, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 6 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq6' : q.coeff 6 = H ^ 3 := by simpa only [q] using hq6
  have hmismatch' : (3 : k[X]) * p.coeff 3 * H -
      (2 : k[X]) * q.coeff 5 = C lambda * h0 ^ 5 := by
    simpa only [p, q] using hmismatch
  have hh0degree : h0.natDegree = 1 := by
    have hdeg := congrArg Polynomial.natDegree hH
    rw [hHdegree, natDegree_pow] at hdeg
    omega
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hh0degree
  let a : k := -d / c
  have hroot : h0.eval a = 0 := by
    rw [← hlinear]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    dsimp only [a]
    field_simp [hc]
    ring
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hmismatch'
  have hmapped' :
      3 * algebraMap k[X] (RatFunc k) (p.coeff 3) *
          (algebraMap k[X] (RatFunc k) h0) ^ 2 -
        2 * algebraMap k[X] (RatFunc k) (q.coeff 5) =
      RatFunc.C lambda * (algebraMap k[X] (RatFunc k) h0) ^ 5 := by
    simpa only [hH, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hhRat : algebraMap k[X] (RatFunc k) h0 ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh0
  have hLraw := depressedL46_eq_of_mismatch
    (algebraMap k[X] (RatFunc k) h0)
    (algebraMap k[X] (RatFunc k) (p.coeff 3))
    (algebraMap k[X] (RatFunc k) (q.coeff 5))
    (RatFunc.C lambda) hhRat hmapped'
  have hL : depressedL46
      (algebraMap k[X] (RatFunc k) h0)
      (quarticDepressionR46 (algebraMap k[X] (RatFunc k) h0)
        (algebraMap k[X] (RatFunc k) (p.coeff 3)))
      (algebraMap k[X] (RatFunc k) (q.coeff 5)) =
      algebraMap k (RatFunc k) (-lambda / 2) := by
    rw [hLraw]
    simp only [RatFunc.algebraMap_eq_C, map_neg, map_div₀, map_ofNat]
  obtain ⟨S⟩ := squareConstantLSourceCurveData46
    p q H h0 j (-lambda / 2) hp hq hh0 hH hp4' hq6' hL hD
  have hl : -lambda / 2 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hlambda) (by norm_num)
  exact S.mismatch_impossible_at_root a hh0 hroot hj hl

end SourcePoleSpecialization

end Max11DegreeRoutes
