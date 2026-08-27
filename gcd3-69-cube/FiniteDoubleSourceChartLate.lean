import FiniteDoubleSourceChartOrders

/-! # Late moving-root chart at the source double root

The complementary range `delta ≤ ord(w)` of the exact balanced chart is
excluded by term-by-term lower bounds: the moving cubic has order at least
`delta` and the transverse value has order at least `2 * delta`.  Those
bounds, together with `p = 3 * delta`, feed the abstract nonic
order-bounds contradiction.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- When `p ≥ 3 * delta`, a late nonzero root deviation of order at
least `delta` forces the cubic and transverse values into the abstract
nonic order-bounds contradiction. -/
theorem TransverseFactor.doubleRoot_sourceLate_inconsistent_of_chart
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (nu : ℚ) (r0 A0 c : k)
    (r w d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0) (_hc : c ≠ 0)
    (hp : 3 * T.delta ≤ S.normal.sextic.scale.p)
    (hnu : 0 < nu) (hlate : T.delta ≤ nu)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hw : w.1.orderTop = (↑nu : WithTop ℚ))
    (_hlcw : w.1.leadingCoeff = c)
    (hKchart : S.cubicValue = GCD369CubeDoubleSourceCubicChart
      T.delta T.hdelta.le r w d)
    (hphichart : S.transverseValue =
      GCD369CubeDoubleSourceTransverseChart
        T.delta T.hdelta.le T.Xn r w B B2 C2) : False := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  let Rw : GCD369CubeHahnRegular k := 3 * r + w
  have hw0 : GCD369CubeHahnRegular.constantCoeff w = 0 := by
    change w.1.coeff 0 = 0
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [hw]
    exact WithTop.coe_lt_coe.mpr hnu
  have hRwres : GCD369CubeHahnRegular.constantCoeff Rw = 3 * r0 := by
    dsimp only [Rw]
    simp only [map_add, map_mul, map_ofNat]
    rw [hr, hw0]
    ring
  have hRwne : GCD369CubeHahnRegular.constantCoeff Rw ≠ 0 := by
    rw [hRwres]
    exact mul_ne_zero (by norm_num) hr0
  have hRw :=
    GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
      Rw hRwne
  have hA :=
    GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
      T.Xn (hX ▸ hA0)
  have hH := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) T.delta T.hdelta.le
  have hM := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  have hw2 := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    w w nu nu hw hw
  have hw2order : (w ^ 2).1.orderTop =
      (↑(2 * nu) : WithTop ℚ) := by
    rw [pow_two]
    simpa only [show nu + nu = 2 * nu by ring] using hw2.1
  have hKmain := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    (w ^ 2) Rw (2 * nu) 0 hw2order hRw.1
  have hKmainOrder : (w ^ 2 * Rw).1.orderTop =
      (↑(2 * nu) : WithTop ℚ) := by simpa using hKmain.1
  have hKmain' : (↑T.delta : WithTop ℚ) ≤
      (w ^ 2 * Rw).1.orderTop := by
    rw [hKmainOrder]
    exact WithTop.coe_le_coe.mpr (by nlinarith [T.hdelta])
  have hKhigh : (↑T.delta : WithTop ℚ) ≤
      (H * (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r)).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r)
      T.delta 0 (by simpa only [H] using hH.1.ge)
      (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r).2
  have hKsum := GCD369CubeHahnRegular.add_orderTop_lower
    (w ^ 2 * Rw)
    (H * (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r))
    T.delta hKmain' hKhigh
  have hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop := by
    rw [hKchart]
    simpa only [GCD369CubeDoubleSourceCubicChart, H, Rw] using hKsum
  have hPmain := GCD369CubeHahnRegular.mul_mul_orderTop_and_leadingCoeff
    T.Xn w Rw 0 nu 0 hA.1 hw hRw.1
  have hPmainOrder : (T.Xn * w * Rw).1.orderTop =
      (↑nu : WithTop ℚ) := by simpa using hPmain.1
  have hPmain' : (↑T.delta : WithTop ℚ) ≤
      (T.Xn * w * Rw).1.orderTop := by
    rw [hPmainOrder]
    exact WithTop.coe_le_coe.mpr hlate
  have hMB := GCD369CubeHahnRegular.mul_orderTop_lower
    M B (T.delta / 2) 0 (by simpa only [M] using hM.1.ge) B.2
  have hMB' : (↑(T.delta / 2) : WithTop ℚ) ≤
      (M * B).1.orderTop := by simpa only [add_zero] using hMB
  have hMBw : (↑(T.delta / 2 + nu) : WithTop ℚ) ≤
      (M * B * w).1.orderTop := by
    exact GCD369CubeHahnRegular.mul_orderTop_lower
      (M * B) w (T.delta / 2) nu hMB' hw.ge
  have hMBw' : (↑T.delta : WithTop ℚ) ≤
      (M * B * w).1.orderTop :=
    (WithTop.coe_le_coe.mpr (by nlinarith [T.hdelta])).trans hMBw
  have hHtail0 := GCD369CubeHahnRegular.mul_orderTop_lower
    H (B2 * (r + w) + C2) T.delta 0
      (by simpa only [H] using hH.1.ge)
      (B2 * (r + w) + C2).2
  have hHtail : (↑T.delta : WithTop ℚ) ≤
      (H * (B2 * (r + w) + C2)).1.orderTop := by
    simpa only [add_zero] using hHtail0
  have hPtail := GCD369CubeHahnRegular.add_orderTop_lower
    (M * B * w) (H * (B2 * (r + w) + C2))
    T.delta hMBw' hHtail
  have hPsi := GCD369CubeHahnRegular.add_orderTop_lower
    (T.Xn * w * Rw)
    (M * B * w + H * (B2 * (r + w) + C2))
    T.delta hPmain' hPtail
  have hphiData := GCD369CubeHahnRegular.mul_orderTop_lower
    H (T.Xn * w * Rw +
      (M * B * w + H * (B2 * (r + w) + C2)))
    T.delta T.delta (by simpa only [H] using hH.1.ge) hPsi
  have hphi : (↑(2 * T.delta) : WithTop ℚ) ≤
      S.transverseValue.1.orderTop := by
    rw [hphichart]
    simpa only [GCD369CubeDoubleSourceTransverseChart, H, M, Rw,
      add_assoc, show T.delta + T.delta = 2 * T.delta by ring]
      using hphiData
  have hp_lt : 2 * T.delta < S.normal.sextic.scale.p := by
    nlinarith [T.hdelta, hp]
  exact T.doubleRoot_sourceNonic_inconsistent_of_orderBounds
    r0 A0 hr0 hA0 hx hX hY hp_lt hK hphi

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceLate_inconsistent_of_chart
