import FiniteDoubleSourceChart

/-! # Exact-order calculus in the regular Hahn local ring

Reusable valuation facts for residue, products, and strict sums of regular
Hahn series.  None of the statements is branch-specific.
-/

noncomputable section

namespace GCD369CubeHahnRegular

/-- A regular Hahn series with nonzero residue has exact order zero, and
its leading coefficient is that residue. -/
theorem orderTop_eq_zero_of_constantCoeff_ne_zero
    {k : Type*} [Field k] (x : GCD369CubeHahnRegular k)
    (hx : constantCoeff x ≠ 0) :
    x.1.orderTop = (↑(0 : ℚ) : WithTop ℚ) ∧
      x.1.leadingCoeff = constantCoeff x := by
  have hx0 : x.1 ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hx
  have horder : x.1.orderTop = (↑(0 : ℚ) : WithTop ℚ) :=
    le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hx) x.2
  refine ⟨horder, ?_⟩
  have hord : x.1.order = 0 := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hx0, horder]
  rw [HahnSeries.leadingCoeff_eq, hord]
  rfl

/-- Exact finite orders add under multiplication, and leading coefficients
multiply. -/
theorem mul_orderTop_and_leadingCoeff
    {k : Type*} [Field k]
    (x y : GCD369CubeHahnRegular k) (alpha beta : ℚ)
    (hx : x.1.orderTop = (↑alpha : WithTop ℚ))
    (hy : y.1.orderTop = (↑beta : WithTop ℚ)) :
    (x * y).1.orderTop = (↑(alpha + beta) : WithTop ℚ) ∧
      (x * y).1.leadingCoeff = x.1.leadingCoeff * y.1.leadingCoeff := by
  constructor
  · change (x.1 * y.1).orderTop = _
    rw [HahnSeries.orderTop_mul, hx, hy, ← WithTop.coe_add]
  · change (x.1 * y.1).leadingCoeff = _
    exact HahnSeries.leadingCoeff_mul x.1 y.1

/-- A strictly lower exact finite order is preserved by addition, with
unchanged leading coefficient. -/
theorem add_orderTop_eq_left_of_lt
    {k : Type*} [Field k]
    (x y : GCD369CubeHahnRegular k) (alpha beta : ℚ)
    (hx : x.1.orderTop = (↑alpha : WithTop ℚ))
    (hy : (↑beta : WithTop ℚ) ≤ y.1.orderTop)
    (hlt : alpha < beta) :
    (x + y).1.orderTop = (↑alpha : WithTop ℚ) ∧
      (x + y).1.leadingCoeff = x.1.leadingCoeff := by
  have hxy : x.1.orderTop < y.1.orderTop :=
    hx ▸ (WithTop.coe_lt_coe.mpr hlt).trans_le hy
  constructor
  · change (x.1 + y.1).orderTop = _
    rw [HahnSeries.orderTop_add_eq_left hxy, hx]
  · change (x.1 + y.1).leadingCoeff = _
    exact HahnSeries.leadingCoeff_add_eq_left hxy

/-- At an exact finite order, the coefficient is the leading coefficient. -/
theorem coeff_eq_leadingCoeff_of_orderTop_eq
    {k : Type*} [Field k]
    (x : GCD369CubeHahnRegular k) (alpha : ℚ)
    (hx : x.1.orderTop = (↑alpha : WithTop ℚ)) :
    x.1.coeff alpha = x.1.leadingCoeff := by
  have hxne : x.1 ≠ 0 := by
    intro hz
    rw [hz, HahnSeries.orderTop_zero] at hx
    exact WithTop.coe_ne_top hx.symm
  have hord : x.1.order = alpha := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hxne, hx]
  rw [HahnSeries.leadingCoeff_eq, hord]

end GCD369CubeHahnRegular

#print axioms GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
#print axioms GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
#print axioms GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
#print axioms GCD369CubeHahnRegular.coeff_eq_leadingCoeff_of_orderTop_eq
