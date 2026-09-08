import FiniteDoubleSourceOrderBasic

/-! # Order lower bounds in the regular Hahn local ring

Reusable valuation inequalities for products and sums of regular Hahn
series, together with the exact order of a packaged monomial.  None of
the statements is branch-specific.
-/

noncomputable section

namespace GCD369CubeHahnRegular

/-- Finite lower bounds on `orderTop` add under multiplication. -/
theorem mul_orderTop_lower
    {k : Type*} [Field k]
    (x y : GCD369CubeHahnRegular k) (alpha beta : ℚ)
    (hx : (↑alpha : WithTop ℚ) ≤ x.1.orderTop)
    (hy : (↑beta : WithTop ℚ) ≤ y.1.orderTop) :
    (↑(alpha + beta) : WithTop ℚ) ≤ (x * y).1.orderTop := by
  change (↑(alpha + beta) : WithTop ℚ) ≤ (x.1 * y.1).orderTop
  rw [HahnSeries.orderTop_mul]
  have h := add_le_add hx hy
  rw [← WithTop.coe_add] at h
  exact h

/-- A common finite lower bound on `orderTop` is preserved by addition. -/
theorem add_orderTop_lower
    {k : Type*} [Field k]
    (x y : GCD369CubeHahnRegular k) (alpha : ℚ)
    (hx : (↑alpha : WithTop ℚ) ≤ x.1.orderTop)
    (hy : (↑alpha : WithTop ℚ) ≤ y.1.orderTop) :
    (↑alpha : WithTop ℚ) ≤ (x + y).1.orderTop := by
  change (↑alpha : WithTop ℚ) ≤ (x.1 + y.1).orderTop
  exact (le_min hx hy).trans HahnSeries.min_orderTop_le_orderTop_add

/-- A packaged nonnegative monomial has exact finite order equal to its
exponent, and leading coefficient `1`. -/
theorem monomial_orderTop_and_leadingCoeff
    {k : Type*} [Field k]
    (delta : ℚ) (hdelta : 0 ≤ delta) :
    (monomial (k := k) delta hdelta).1.orderTop =
        (↑delta : WithTop ℚ) ∧
      (monomial (k := k) delta hdelta).1.leadingCoeff = 1 := by
  constructor
  · change (HahnSeries.single delta (1 : k)).orderTop = _
    rw [HahnSeries.orderTop_single one_ne_zero]
  · change (HahnSeries.single delta (1 : k)).leadingCoeff = _
    exact HahnSeries.leadingCoeff_of_single

/-- Exact finite orders and leading coefficients of three regular factors
multiply. -/
theorem mul_mul_orderTop_and_leadingCoeff
    {k : Type*} [Field k]
    (x y z : GCD369CubeHahnRegular k) (alpha beta gamma : ℚ)
    (hx : x.1.orderTop = (↑alpha : WithTop ℚ))
    (hy : y.1.orderTop = (↑beta : WithTop ℚ))
    (hz : z.1.orderTop = (↑gamma : WithTop ℚ)) :
    (x * y * z).1.orderTop = (↑(alpha + beta + gamma) : WithTop ℚ) ∧
      (x * y * z).1.leadingCoeff =
        x.1.leadingCoeff * y.1.leadingCoeff * z.1.leadingCoeff := by
  have hxy := mul_orderTop_and_leadingCoeff x y alpha beta hx hy
  have hxyz :=
    mul_orderTop_and_leadingCoeff (x * y) z (alpha + beta) gamma hxy.1 hz
  exact ⟨hxyz.1, by rw [hxyz.2, hxy.2]⟩

end GCD369CubeHahnRegular

#print axioms GCD369CubeHahnRegular.mul_orderTop_lower
#print axioms GCD369CubeHahnRegular.add_orderTop_lower
#print axioms GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
#print axioms GCD369CubeHahnRegular.mul_mul_orderTop_and_leadingCoeff
