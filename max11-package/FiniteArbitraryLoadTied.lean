import FiniteSourceElimination
import ArbitraryLoads

/-! # Cubic resonance forced by an arbitrary tied load

At a transverse factor carrying any of the eight audited nonzero source
loads, the arbitrary-load equations forbid a common root.  The transverse
quadratic evaluated at the recovered cubic root is therefore a unit after
the prescribed monomial has been removed.  Before the sextic source
boundary, the exact source equation then forces the moving cubic value to
have half the transverse order.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Any arbitrary nonzero Faber load on a transverse residue jet before the
weight-six source boundary forces exact cubic/transverse resonance. -/
theorem TransverseFactor.cubic_resonance_of_arbitraryEarlyLoad
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (load : GCD369CubeArbitraryEarlyFaberLoad
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v)
    (hbeforeSource : T.delta < 6 * S.normal.sextic.scale.p) :
    ∃ alpha : ℚ, ∃ a : k,
      0 < alpha ∧ a ≠ 0 ∧
      S.cubicValue.1.orderTop = (↑alpha : WithTop ℚ) ∧
      S.cubicValue.1.leadingCoeff = a ∧
      2 * alpha = T.delta := by
  have hnocommon := load.noCommonRoot
  let x : GCD369CubeHahnRegular k := S.normal.sextic.regularX
  let B : GCD369CubeHahnRegular k :=
    T.Xn * x ^ 2 + T.Yn * x + T.Zn
  have hB0 : GCD369CubeHahnRegular.constantCoeff B ≠ 0 := by
    intro hzero
    apply hnocommon (GCD369CubeHahnRegular.constantCoeff x)
    · simpa [x, GCD369CubeHahnRegular.constantCoeff,
        GCD369CubeHahnSexticValueData.regularX] using S.leadingCubicRoot
    · simpa only [B, x, map_add, map_mul, map_pow] using hzero
  have hBorder : B.1.orderTop = (↑(0 : ℚ) : WithTop ℚ) :=
    (GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero B hB0).1
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  have hH := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) T.delta T.hdelta.le
  have hphiEq : S.transverseValue = H * B := by
    simpa only [H, B, x] using T.transverseValue_eq
  have hHB := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    H B T.delta 0 hH.1 hBorder
  have hphiOrder : S.transverseValue.1.orderTop =
      (↑T.delta : WithTop ℚ) := by
    rw [hphiEq]
    simpa only [add_zero] using hHB.1
  have hKne : S.cubicValue.1 ≠ 0 := by
    intro hKzero
    have hsource := S.commonNormalEquation_orderTop_lower
    change (↑(6 * S.normal.sextic.scale.p) : WithTop ℚ) ≤
      (S.cubicValue.1 ^ 2 + S.transverseValue.1).orderTop at hsource
    rw [hKzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
      hphiOrder, WithTop.coe_le_coe] at hsource
    linarith
  let alpha : ℚ := S.cubicValue.1.order
  let a : k := S.cubicValue.1.leadingCoeff
  have hKorder : S.cubicValue.1.orderTop =
      (↑alpha : WithTop ℚ) := by
    exact (HahnSeries.order_eq_orderTop_of_ne_zero hKne).symm
  have halpha : 0 < alpha := by
    have hpos := GCD369CubeHahnRegular.orderTop_pos_of_constantCoeff_zero
      S.cubicValue S.constantCoeff_cubicValue_zero
    rw [hKorder, WithTop.coe_lt_coe] at hpos
    exact hpos
  have ha : a ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hKne
  have halt := S.commonNormal_orderAlternative alpha T.delta
    hKorder hphiOrder
  have hresonance : 2 * alpha = T.delta := by
    rcases halt with hfar | hcancel
    · have hmin : min (2 * alpha) T.delta ≤ T.delta := min_le_right _ _
      linarith
    · exact hcancel.1
  exact ⟨alpha, a, halpha, ha, hKorder, rfl, hresonance⟩

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.cubic_resonance_of_arbitraryEarlyLoad
