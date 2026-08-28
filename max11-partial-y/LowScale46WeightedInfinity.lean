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

end SourcePoleSpecialization

end Max11DegreeRoutes
