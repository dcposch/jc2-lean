import LowScale46RegularLoads

/-! # Weighted-infinity specialization for the `(4,6)` coefficient curve

This module supplies the Hahn-series initial-form calculus needed to pass
from a genuine finite pole of the coefficient curve to its unique weighted
point at infinity.
-/

noncomputable section

namespace Max11DegreeRoutes

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

end Max11DegreeRoutes
