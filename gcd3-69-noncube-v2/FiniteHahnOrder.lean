import FiniteRootLift

/-! # Hahn-order dichotomy for a regular square plus a perturbation

The moving cubic value and its transverse quadratic are regular Hahn series.
If they have exact finite orders `alpha` and `beta`, then either
`orderTop (K ^ 2 + phi)` is `min (2 * alpha) beta`, or the two orders meet
and the leading coefficients cancel.  This is the valuation alternative
consumed by later estimates on `cubicValue` and `transverseValue`.
-/

noncomputable section

/-- Exact finite-order dichotomy for a square plus a regular perturbation.
Either the sum attains the expected minimum order, or the orders coincide
and the leading coefficients cancel. -/
theorem GCD369CubeHahn_squareAdd_orderDichotomy
    {k : Type*} [Field k]
    (K phi : HahnSeries ℚ k) (alpha beta : ℚ)
    (hK : K.orderTop = (↑alpha : WithTop ℚ))
    (hphi : phi.orderTop = (↑beta : WithTop ℚ)) :
    (K ^ 2 + phi).orderTop = (↑(min (2 * alpha) beta) : WithTop ℚ) ∨
      (2 * alpha = beta ∧
        K.leadingCoeff ^ 2 + phi.leadingCoeff = 0) := by
  have hKne : K ≠ 0 := by
    intro h
    rw [h, HahnSeries.orderTop_zero] at hK
    exact WithTop.coe_ne_top hK.symm
  have hphine : phi ≠ 0 := by
    intro h
    rw [h, HahnSeries.orderTop_zero] at hphi
    exact WithTop.coe_ne_top hphi.symm
  have hKorder : K.order = alpha := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hKne, hK]
  have hphiorder : phi.order = beta := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hphine, hphi]
  have hKsq_ne : K ^ 2 ≠ 0 := pow_ne_zero 2 hKne
  have hKsq_orderTop :
      (K ^ 2).orderTop = (↑(2 * alpha) : WithTop ℚ) := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hKsq_ne,
      HahnSeries.order_pow, hKorder, nsmul_eq_mul]
    norm_num
  by_cases hlo : 2 * alpha < beta
  · left
    have horders : (K ^ 2).orderTop < phi.orderTop := by
      rw [hKsq_orderTop, hphi]
      exact WithTop.coe_lt_coe.mpr hlo
    rw [HahnSeries.orderTop_add_eq_left horders, hKsq_orderTop,
      min_eq_left (le_of_lt hlo)]
  · by_cases hhi : beta < 2 * alpha
    · left
      have horders : phi.orderTop < (K ^ 2).orderTop := by
        rw [hKsq_orderTop, hphi]
        exact WithTop.coe_lt_coe.mpr hhi
      rw [HahnSeries.orderTop_add_eq_right horders, hphi,
        min_eq_right (le_of_lt hhi)]
    · have heq : 2 * alpha = beta :=
        le_antisymm (le_of_not_gt hhi) (le_of_not_gt hlo)
      by_cases hcancel :
          K.leadingCoeff ^ 2 + phi.leadingCoeff = 0
      · exact Or.inr ⟨heq, hcancel⟩
      · left
        have hKsq_coeff :
            (K ^ 2).coeff (2 * alpha) = K.leadingCoeff ^ 2 := by
          have hmul := HahnSeries.coeff_mul_order_add_order K K
          have hord : K.order + K.order = 2 * alpha := by
            rw [hKorder]
            ring
          rw [sq K, ← hord]
          simpa [pow_two] using hmul
        have hphi_coeff :
            phi.coeff (2 * alpha) = phi.leadingCoeff := by
          rw [HahnSeries.leadingCoeff_eq, hphiorder, heq]
        have hsum_coeff :
            (K ^ 2 + phi).coeff (2 * alpha) =
              K.leadingCoeff ^ 2 + phi.leadingCoeff := by
          rw [HahnSeries.coeff_add, hKsq_coeff, hphi_coeff]
        have hne : (K ^ 2 + phi).coeff (2 * alpha) ≠ 0 := by
          rwa [hsum_coeff]
        have hle :
            (K ^ 2 + phi).orderTop ≤
              (↑(2 * alpha) : WithTop ℚ) :=
          HahnSeries.orderTop_le_of_coeff_ne_zero hne
        have hge :
            (↑(2 * alpha) : WithTop ℚ) ≤
              (K ^ 2 + phi).orderTop := by
          have hmin :=
            HahnSeries.min_orderTop_le_orderTop_add
              (x := K ^ 2) (y := phi)
          rw [hKsq_orderTop, hphi, ← heq, min_self] at hmin
          exact hmin
        have hminval : min (2 * alpha) beta = 2 * alpha := by
          rw [heq, min_self]
        rw [hminval]
        exact le_antisymm hle hge

#print axioms GCD369CubeHahn_squareAdd_orderDichotomy
