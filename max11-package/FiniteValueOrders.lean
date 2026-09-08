import FiniteHahnOrder

/-! # Source-value order bounds at a finite common-cubic pole

The literal polynomial source makes the scaled sextic value divisible by the
sixth power of the selected pole monomial.  This file turns that divisibility
into a valuation statement for the moving cubic square plus its transverse
quadratic, and records the resulting leading-order cancellation alternative.
-/

noncomputable section

namespace GCD369CubeHahnPoleScale

/-- Multiplying a regular Hahn series by a weight-`w` pole monomial raises
its order by at least `w * p`. -/
theorem weightedRegular_orderTop_lower
    {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k)
    (w : ℕ) (x : GCD369CubeHahnRegular k) :
    (↑((w : ℚ) * S.p) : WithTop ℚ) ≤
      (S.weightedRegular w x).1.orderTop := by
  change (↑((w : ℚ) * S.p) : WithTop ℚ) ≤
    (S.t ^ w * x.1).orderTop
  by_cases hx : x.1 = 0
  · simp [hx]
  have ht : S.t ^ w ≠ 0 := by
    apply pow_ne_zero
    simp [GCD369CubeHahnPoleScale.t]
  rw [HahnSeries.orderTop_mul,
    ← HahnSeries.order_eq_orderTop_of_ne_zero ht,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hx]
  change (↑((w : ℚ) * S.p) : WithTop ℚ) ≤
    (↑((S.t ^ w).order + x.1.order) : WithTop ℚ)
  rw [WithTop.coe_le_coe]
  have hx0 : (0 : ℚ) ≤ x.1.order := by
    have := HahnSeries.zero_le_orderTop_iff.mp x.2
    exact this
  have htorder : (S.t ^ w).order = (w : ℚ) * S.p := by
    rw [HahnSeries.order_pow]
    have ht0 : S.t ≠ 0 := by simp [GCD369CubeHahnPoleScale.t]
    have hto : S.t.order = S.p := by
      apply WithTop.coe_injective
      rw [HahnSeries.order_eq_orderTop_of_ne_zero ht0,
        GCD369CubeHahnPoleScale.t, HahnSeries.orderTop_single]
      simp
    rw [hto, nsmul_eq_mul]
  rw [htorder]
  linarith

end GCD369CubeHahnPoleScale

namespace GCD369CubeHahnCommonValueData

/-- The recovered translation makes the moving common cubic vanish in the
residue field. -/
theorem constantCoeff_cubicValue_zero
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    GCD369CubeHahnRegular.constantCoeff S.cubicValue = 0 := by
  simp only [cubicValue, map_add, map_mul, map_pow,
    S.constantCoeff_cubicU, S.constantCoeff_cubicV]
  exact S.leadingCubicRoot

/-- A prescribed transverse factor pulls the same monomial out of the
transverse quadratic evaluated at the recovered coordinate. -/
theorem TransverseFactor.transverseValue_eq
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor) :
    S.transverseValue =
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le *
        (T.Xn * S.normal.sextic.regularX ^ 2 +
          T.Yn * S.normal.sextic.regularX + T.Zn) := by
  dsimp only [transverseValue]
  rw [T.hnormal2, T.hnormal1, T.hnormal0]
  ring

/-- The exact source sextic equation forces the common-normal value to have
order at least six times the pole scale. -/
theorem commonNormalEquation_orderTop_lower
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    (↑((6 : ℚ) * S.normal.sextic.scale.p) : WithTop ℚ) ≤
      (S.cubicValue ^ 2 + S.transverseValue).1.orderTop := by
  rw [S.commonNormalEquation]
  exact S.normal.sextic.scale.weightedRegular_orderTop_lower 6
    S.normal.sextic.value

/-- For finite exact orders of the moving cubic value and transverse value,
the source equation gives the basic Newton alternative: either their expected
minimum already lies beyond the sextic boundary, or equal orders cancel at
the leading coefficient. -/
theorem commonNormal_orderAlternative
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) (alpha beta : ℚ)
    (hK : S.cubicValue.1.orderTop = (↑alpha : WithTop ℚ))
    (hphi : S.transverseValue.1.orderTop = (↑beta : WithTop ℚ)) :
    (6 * S.normal.sextic.scale.p ≤ min (2 * alpha) beta) ∨
      (2 * alpha = beta ∧
        S.cubicValue.1.leadingCoeff ^ 2 +
          S.transverseValue.1.leadingCoeff = 0) := by
  rcases GCD369CubeHahn_squareAdd_orderDichotomy
      S.cubicValue.1 S.transverseValue.1 alpha beta hK hphi with
    hmin | hcancel
  · left
    have hsource := S.commonNormalEquation_orderTop_lower
    change (↑((6 : ℚ) * S.normal.sextic.scale.p) : WithTop ℚ) ≤
      (S.cubicValue.1 ^ 2 + S.transverseValue.1).orderTop at hsource
    rw [hmin, WithTop.coe_le_coe] at hsource
    exact hsource
  · exact Or.inr hcancel

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnPoleScale.weightedRegular_orderTop_lower
#print axioms GCD369CubeHahnCommonValueData.constantCoeff_cubicValue_zero
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.transverseValue_eq
#print axioms GCD369CubeHahnCommonValueData.commonNormalEquation_orderTop_lower
#print axioms GCD369CubeHahnCommonValueData.commonNormal_orderAlternative
