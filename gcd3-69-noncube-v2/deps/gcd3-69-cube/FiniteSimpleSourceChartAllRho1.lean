import FiniteSimpleSourceOrdersRho1

/-! # Complete simple-root pre-resonant split before `rho1` -/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- With `d = 0`, `c7 = 0`, `c5 = 0`, `c4 = 0`, `c3 = 0`, `c2 = 0`, `c1 = 0`
and the cubic transverse scale through the weight-nine cutoff, the simple-root
displacement is zero or begins at order at least `delta`. -/
theorem TransverseFactor.simpleRoot_source_zero_or_order_delta_of_coordinates_before_rho1
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (hc7 : S.normal.c7 = 0)
    (hc5 : S.normal.c5 = 0)
    (hc4 : S.normal.c4 = 0)
    (hc3 : S.normal.c3 = 0)
    (hc2 : S.normal.c2 = 0)
    (hc1 : S.normal.c1 = 0)
    (r0 A0 : k)
    (r w d e B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta ≤ 9 * S.normal.sextic.scale.p)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hw0 : GCD369CubeHahnRegular.constantCoeff w = 0)
    (hx : S.normal.sextic.regularX = -2 * r + w)
    (hU : S.cubicU = -3 * r ^ 2 +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * d)
    (hV : S.cubicV = 2 * r ^ 3 +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * e)
    (hre : 3 * e + 2 * d * r = 0)
    (hY : T.Yn = r * T.Xn +
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * B +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * B2)
    (hZ : T.Zn = -2 * r ^ 2 * T.Xn -
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * r * B +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * C2) :
    w = 0 ∨ (↑T.delta : WithTop ℚ) ≤ w.1.orderTop := by
  have hcharts := T.simpleRoot_chart_equations
    r w d e B B2 C2 hx hU hV hre hY hZ
  by_cases hwz : w = 0
  · exact Or.inl hwz
  · right
    rcases GCD369CubeHahnRegular.exists_pos_orderTop_eq_of_constantCoeff_zero
        w hw0 hwz with ⟨alpha, halpha, hw⟩
    have hdeltaOrder : T.delta ≤ alpha := by
      by_contra hnot
      have hbelow : alpha < T.delta := lt_of_not_ge hnot
      let M : GCD369CubeHahnRegular k :=
        GCD369CubeHahnRegular.monomial (T.delta / 2)
          (div_nonneg T.hdelta.le (by norm_num))
      let N : GCD369CubeHahnRegular k := M * B
      by_cases hNlower : (↑alpha : WithTop ℚ) ≤ N.1.orderTop
      · exact T.simpleRoot_sourceBelow_inconsistent_of_normal_lower_before_rho1
          hd hc7 hc5 hc4 alpha r0 A0 r w d B B2 C2 hr0 hA0 hp halpha hbelow
          hr hX hw (by simpa only [N, M] using hNlower)
          hcharts.1 hcharts.2
      · have hNlt : N.1.orderTop < (↑alpha : WithTop ℚ) :=
          lt_of_not_ge hNlower
        have hNne : N ≠ 0 := by
          intro hzero
          rw [hzero] at hNlt
          simp at hNlt
        have hNne' : N.1 ≠ 0 := by
          intro hzero
          apply hNne
          exact Subtype.ext hzero
        let gamma : ℚ := N.1.order
        have hN : N.1.orderTop = (↑gamma : WithTop ℚ) :=
          (HahnSeries.order_eq_orderTop_of_ne_zero hNne').symm
        have hgammaAlpha : gamma < alpha := by
          apply WithTop.coe_lt_coe.mp
          rw [← hN]
          exact hNlt
        let c : k := w.1.leadingCoeff
        have hc : c ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr (by
          intro hzero
          apply hwz
          exact Subtype.ext hzero)
        exact T.simpleRoot_sourceBelow_inconsistent_of_normal_exact_before_rho1
          hd hc7 hc5 hc4 hc3 hc2 hc1 alpha gamma r0 A0 c r w d B B2 C2 hr0 hA0 hc hp
          halpha hbelow hgammaAlpha hr hx hX hY hw rfl
          (by simpa only [N, M] using hN) hcharts.1 hcharts.2
    simpa only [hw] using WithTop.coe_le_coe.mpr hdeltaOrder

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_source_zero_or_order_delta_of_coordinates_before_rho1
