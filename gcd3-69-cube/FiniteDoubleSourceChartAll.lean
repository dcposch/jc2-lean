import FiniteDoubleSourceChartBridge
import FiniteDoubleSourceChartMiddle
import FiniteDoubleSourceChartLate
import FiniteDoubleSourceChartZero

/-! # Complete order split in the balanced double-root source chart

The zero deviation is separated first.  A nonzero deviation with zero residue
has an exact positive Hahn order, which lies in exactly one of the early,
middle, or late ranges already excluded by the source sextic and nonic.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Every root deviation in the exact balanced double-root chart is excluded.
The sole input about the deviation not already present in the chart equations
is that its residue vanishes. -/
theorem TransverseFactor.doubleRoot_source_inconsistent_of_chart
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r0 A0 : k)
    (r w d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : S.normal.sextic.scale.p = 3 * T.delta)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hw0 : GCD369CubeHahnRegular.constantCoeff w = 0)
    (hKchart : S.cubicValue = GCD369CubeDoubleSourceCubicChart
      T.delta T.hdelta.le r w d)
    (hphichart : S.transverseValue =
      GCD369CubeDoubleSourceTransverseChart
        T.delta T.hdelta.le T.Xn r w B B2 C2) : False := by
  by_cases hwz : w = 0
  · subst w
    exact T.doubleRoot_sourceZero_inconsistent_of_chart
      r0 A0 r d B B2 C2 hr0 hA0 hp hx hX hY hKchart hphichart
  · rcases GCD369CubeHahnRegular.exists_pos_orderTop_eq_of_constantCoeff_zero
        w hw0 hwz with ⟨nu, hnu, hw⟩
    let c : k := w.1.leadingCoeff
    have hc : c ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr (by
      intro hz
      apply hwz
      exact Subtype.ext hz)
    by_cases hearly : 2 * nu < T.delta
    · exact T.doubleRoot_sourceEarly_inconsistent_of_chart
        nu r0 A0 c r w d B B2 C2 hr0 hA0 hc hp hnu hearly
        hr hx hX hY hw rfl hKchart hphichart
    · by_cases hmiddle : nu < T.delta
      · exact T.doubleRoot_sourceMiddle_inconsistent_of_chart
          nu r0 A0 r w d B B2 C2 hr0 hA0 hp hnu
          (by linarith) hmiddle hr hX hw hKchart hphichart
      · exact T.doubleRoot_sourceLate_inconsistent_of_chart
          nu r0 A0 c r w d B B2 C2 hr0 hA0 hc hp hnu
          (le_of_not_gt hmiddle) hr hx hX hY hw rfl hKchart hphichart

/-- The complete exclusion stated directly in the expanded moving cubic and
normalized transverse coordinates.  The residue identities required by the
nonic obstruction are consequences of these expansions. -/
theorem TransverseFactor.doubleRoot_source_inconsistent_of_coordinates
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r0 A0 : k)
    (r w d e B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : S.normal.sextic.scale.p = 3 * T.delta)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hw0 : GCD369CubeHahnRegular.constantCoeff w = 0)
    (hxcoord : S.normal.sextic.regularX = r + w)
    (hU : S.cubicU = -3 * r ^ 2 +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * d)
    (hV : S.cubicV = 2 * r ^ 3 +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * e)
    (hre : 3 * e + 2 * d * r = 0)
    (hYn : T.Yn = r * T.Xn +
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * B +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * B2)
    (hZn : T.Zn = -2 * r ^ 2 * T.Xn -
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * r * B +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * C2) : False := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  have hH := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) T.delta T.hdelta.le
  have hM := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  have hH0 : GCD369CubeHahnRegular.constantCoeff H = 0 := by
    change H.1.coeff 0 = 0
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [show H.1.orderTop = (↑T.delta : WithTop ℚ) by
      simpa only [H] using hH.1]
    exact WithTop.coe_lt_coe.mpr T.hdelta
  have hM0 : GCD369CubeHahnRegular.constantCoeff M = 0 := by
    change M.1.coeff 0 = 0
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [show M.1.orderTop = (↑(T.delta / 2) : WithTop ℚ) by
      simpa only [M] using hM.1]
    exact WithTop.coe_lt_coe.mpr (by nlinarith [T.hdelta])
  have hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r0 := by
    rw [hxcoord]
    simp only [map_add, hr, hw0, add_zero]
  have hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0 := by
    rw [hYn]
    simp only [map_add, map_mul]
    rw [hr, hX]
    change r0 * A0 +
      GCD369CubeHahnRegular.constantCoeff M *
          GCD369CubeHahnRegular.constantCoeff B +
        GCD369CubeHahnRegular.constantCoeff H *
          GCD369CubeHahnRegular.constantCoeff B2 = r0 * A0
    rw [hM0, hH0]
    ring
  have hcharts := T.doubleRoot_chart_equations
    r w d e B B2 C2 hxcoord hU hV hre hYn hZn
  exact T.doubleRoot_source_inconsistent_of_chart
    r0 A0 r w d B B2 C2 hr0 hA0 hp hr hx hX hY hw0
    hcharts.1 hcharts.2

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_source_inconsistent_of_chart
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_source_inconsistent_of_coordinates
