import FiniteDoubleSourceOrderCasesC7
import FiniteDoubleSourceNonicC7
import FiniteSimpleSourceOrdersC7
import FiniteDoubleSourceChartOrders
import FiniteDoubleSourceChartMiddle
import FiniteDoubleSourceChartLate
import FiniteDoubleSourceChartZero
import FiniteDoubleSourceChartAll

/-! # Double-root source chart split before `c7`

After the weight-one load vanishes, the same early/middle/late/zero chart
valuations apply once `3 * delta < 2 * p`.  The proofs are the existing
chart calculations; only the terminal sextic and nonic lemmas change.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- When `3 * delta < 2 * p` and `d = 0`, an early nonzero root deviation
has the orders and leading coefficients consumed by the abstract
early-source contradiction below the weight-two load. -/
theorem TransverseFactor.doubleRoot_sourceEarly_inconsistent_of_chart_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (nu : ℚ) (r0 A0 c : k)
    (r w d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0) (hc : c ≠ 0)
    (hp : 3 * T.delta < 2 * S.normal.sextic.scale.p)
    (hnu : 0 < nu) (hearly : 2 * nu < T.delta)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hw : w.1.orderTop = (↑nu : WithTop ℚ))
    (hlcw : w.1.leadingCoeff = c)
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
  have hw2lc : (w ^ 2).1.leadingCoeff = c ^ 2 := by
    rw [pow_two, hw2.2, hlcw]
    simp only [pow_two]
  have hKmain := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    (w ^ 2) Rw (2 * nu) 0 hw2order hRw.1
  have hKmainOrder : (w ^ 2 * Rw).1.orderTop =
      (↑(2 * nu) : WithTop ℚ) := by simpa using hKmain.1
  have hKmainLC : (w ^ 2 * Rw).1.leadingCoeff =
      3 * r0 * c ^ 2 := by
    rw [hKmain.2, hw2lc, hRw.2, hRwres]
    ring
  have hKhigh : (↑T.delta : WithTop ℚ) ≤
      (H * (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r)).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r)
      T.delta 0 (by simpa only [H] using hH.1.ge)
      (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r).2
  have hKdata := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    (w ^ 2 * Rw)
    (H * (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r))
    (2 * nu) T.delta hKmainOrder hKhigh hearly
  have hKorder : S.cubicValue.1.orderTop =
      (↑(2 * nu) : WithTop ℚ) := by
    rw [hKchart]
    simpa only [GCD369CubeDoubleSourceCubicChart, H, Rw] using hKdata.1
  have hKlc : S.cubicValue.1.leadingCoeff = 3 * r0 * c ^ 2 := by
    rw [hKchart]
    simpa only [GCD369CubeDoubleSourceCubicChart, H, Rw,
      hKmainLC] using hKdata.2
  have hPmain := GCD369CubeHahnRegular.mul_mul_orderTop_and_leadingCoeff
    T.Xn w Rw 0 nu 0 hA.1 hw hRw.1
  have hPmainOrder : (T.Xn * w * Rw).1.orderTop =
      (↑nu : WithTop ℚ) := by simpa using hPmain.1
  have hPmainLC : (T.Xn * w * Rw).1.leadingCoeff =
      3 * r0 * A0 * c := by
    rw [hPmain.2, hA.2, hX, hlcw, hRw.2, hRwres]
    ring
  have hMB := GCD369CubeHahnRegular.mul_orderTop_lower
    M B (T.delta / 2) 0 (by simpa only [M] using hM.1.ge) B.2
  have hMB' : (↑(T.delta / 2) : WithTop ℚ) ≤
      (M * B).1.orderTop := by simpa only [add_zero] using hMB
  have hMBw : (↑(T.delta / 2 + nu) : WithTop ℚ) ≤
      (M * B * w).1.orderTop := by
    exact GCD369CubeHahnRegular.mul_orderTop_lower
      (M * B) w (T.delta / 2) nu hMB' hw.ge
  have hHtail0 := GCD369CubeHahnRegular.mul_orderTop_lower
    H (B2 * (r + w) + C2) T.delta 0
      (by simpa only [H] using hH.1.ge)
      (B2 * (r + w) + C2).2
  have hHtail : (↑(T.delta / 2 + nu) : WithTop ℚ) ≤
      (H * (B2 * (r + w) + C2)).1.orderTop := by
    exact (WithTop.coe_le_coe.mpr (by nlinarith)).trans hHtail0
  have hPtail := GCD369CubeHahnRegular.add_orderTop_lower
    (M * B * w) (H * (B2 * (r + w) + C2))
    (T.delta / 2 + nu) hMBw hHtail
  have hPsi := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    (T.Xn * w * Rw)
    (M * B * w + H * (B2 * (r + w) + C2))
    nu (T.delta / 2 + nu) hPmainOrder hPtail (by nlinarith [T.hdelta])
  have hphiData := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    H (T.Xn * w * Rw +
      (M * B * w + H * (B2 * (r + w) + C2)))
    T.delta nu hH.1 hPsi.1
  have hphiOrder : S.transverseValue.1.orderTop =
      (↑(T.delta + nu) : WithTop ℚ) := by
    rw [hphichart]
    simpa only [GCD369CubeDoubleSourceTransverseChart, H, M,
      Rw, add_assoc] using hphiData.1
  have hphilc : S.transverseValue.1.leadingCoeff =
      3 * r0 * A0 * c := by
    rw [hphichart]
    simpa only [GCD369CubeDoubleSourceTransverseChart, H, M,
      Rw, add_assoc, hphiData.2, hH.2, one_mul, hPsi.2,
      hPmainLC]
  exact T.doubleRoot_sourceEarly_inconsistent_of_exactOrders_before_c7
    hd nu r0 A0 c hr0 hA0 hc hp hnu hearly hx hX hY
    hKorder hKlc hphiOrder hphilc

/-- When `3 * delta < 2 * p` and `d = 0`, a middle-range nonzero root
deviation makes the cubic value have order at least `delta` and the
transverse value have exact order `delta + nu`, which the source sextic
excludes. -/
theorem TransverseFactor.doubleRoot_sourceMiddle_inconsistent_of_chart_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (nu : ℚ) (r0 A0 : k)
    (r w d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta < 2 * S.normal.sextic.scale.p)
    (hnu : 0 < nu) (hmiddle : T.delta ≤ 2 * nu)
    (hbelow : nu < T.delta)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hw : w.1.orderTop = (↑nu : WithTop ℚ))
    (hKchart : S.cubicValue = GCD369CubeDoubleSourceCubicChart
      T.delta T.hdelta.le r w d)
    (hphichart : S.transverseValue =
      GCD369CubeDoubleSourceTransverseChart
        T.delta T.hdelta.le T.Xn r w B B2 C2) : False := by
  let _ := hd
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
  have hKmainLower : (↑T.delta : WithTop ℚ) ≤
      (w ^ 2 * Rw).1.orderTop := by
    rw [hKmainOrder]
    exact WithTop.coe_le_coe.mpr hmiddle
  have hKhigh : (↑T.delta : WithTop ℚ) ≤
      (H * (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r)).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r)
      T.delta 0 (by simpa only [H] using hH.1.ge)
      (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r).2
  have hKdata := GCD369CubeHahnRegular.add_orderTop_lower
    (w ^ 2 * Rw)
    (H * (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r))
    T.delta hKmainLower hKhigh
  have hKorder : (↑T.delta : WithTop ℚ) ≤
      S.cubicValue.1.orderTop := by
    rw [hKchart]
    simpa only [GCD369CubeDoubleSourceCubicChart, H, Rw] using hKdata
  have hPmain := GCD369CubeHahnRegular.mul_mul_orderTop_and_leadingCoeff
    T.Xn w Rw 0 nu 0 hA.1 hw hRw.1
  have hPmainOrder : (T.Xn * w * Rw).1.orderTop =
      (↑nu : WithTop ℚ) := by simpa using hPmain.1
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
    (WithTop.coe_le_coe.mpr (by nlinarith [hmiddle])).trans hMBw
  have hHtail : (↑T.delta : WithTop ℚ) ≤
      (H * (B2 * (r + w) + C2)).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H (B2 * (r + w) + C2) T.delta 0
        (by simpa only [H] using hH.1.ge)
        (B2 * (r + w) + C2).2
  have hPtail := GCD369CubeHahnRegular.add_orderTop_lower
    (M * B * w) (H * (B2 * (r + w) + C2))
    T.delta hMBw' hHtail
  have hPsi := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    (T.Xn * w * Rw)
    (M * B * w + H * (B2 * (r + w) + C2))
    nu T.delta hPmainOrder hPtail hbelow
  have hphiData := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    H (T.Xn * w * Rw +
      (M * B * w + H * (B2 * (r + w) + C2)))
    T.delta nu hH.1 hPsi.1
  have hphiOrder : S.transverseValue.1.orderTop =
      (↑(T.delta + nu) : WithTop ℚ) := by
    rw [hphichart]
    simpa only [GCD369CubeDoubleSourceTransverseChart, H, M,
      Rw, add_assoc] using hphiData.1
  exact T.sourceSextic_inconsistent_of_transverse_below_twiceDelta_before_c7
    (T.delta + nu) (le_of_lt hp) hKorder hphiOrder (by nlinarith [hbelow])

/-- When `3 * delta < 2 * p` and `d = 0`, a late nonzero root deviation of
order at least `delta` forces the cubic and transverse values into the
abstract nonic order-bounds contradiction below the weight-two load. -/
theorem TransverseFactor.doubleRoot_sourceLate_inconsistent_of_chart_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (nu : ℚ) (r0 A0 c : k)
    (r w d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0) (_hc : c ≠ 0)
    (hp : 3 * T.delta < 2 * S.normal.sextic.scale.p)
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
  exact T.doubleRoot_sourceNonic_inconsistent_of_orderBounds_before_c7
    r0 A0 hr0 hA0 hx hX hY hd hp hK hphi

/-- When `3 * delta < 2 * p` and `d = 0`, a vanishing root deviation forces
the moving cubic to have order at least `delta` and the transverse value to
have order at least `2 * delta`.  The source nonic excludes the branch. -/
theorem TransverseFactor.doubleRoot_sourceZero_inconsistent_of_chart_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (r0 A0 : k)
    (r d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta < 2 * S.normal.sextic.scale.p)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hKchart : S.cubicValue = GCD369CubeDoubleSourceCubicChart
      T.delta T.hdelta.le r 0 d)
    (hphichart : S.transverseValue =
      GCD369CubeDoubleSourceTransverseChart
        T.delta T.hdelta.le T.Xn r 0 B B2 C2) : False := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  have hH := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) T.delta T.hdelta.le
  have hKzero : (↑T.delta : WithTop ℚ) ≤
      ((0 : GCD369CubeHahnRegular k) ^ 2 * (3 * r + 0)).1.orderTop := by
    simp
  have hKhigh : (↑T.delta : WithTop ℚ) ≤
      (H * (d * 0 + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r)).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H (d * 0 + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r)
      T.delta 0 (by simpa only [H] using hH.1.ge)
      (d * 0 + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r).2
  have hKsum := GCD369CubeHahnRegular.add_orderTop_lower
    ((0 : GCD369CubeHahnRegular k) ^ 2 * (3 * r + 0))
    (H * (d * 0 + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r))
    T.delta hKzero hKhigh
  have hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop := by
    rw [hKchart]
    simpa only [GCD369CubeDoubleSourceCubicChart, H] using hKsum
  have hP1 : (↑T.delta : WithTop ℚ) ≤
      (T.Xn * (0 : GCD369CubeHahnRegular k) * (3 * r + 0)).1.orderTop := by
    simp
  have hP2 : (↑T.delta : WithTop ℚ) ≤
      (M * B * (0 : GCD369CubeHahnRegular k)).1.orderTop := by
    have hz : M * B * (0 : GCD369CubeHahnRegular k) = 0 := by
      simp only [mul_zero]
    simp [hz]
  have hP3 : (↑T.delta : WithTop ℚ) ≤
      (H * (B2 * (r + 0) + C2)).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H (B2 * (r + 0) + C2) T.delta 0
      (by simpa only [H] using hH.1.ge)
      (B2 * (r + 0) + C2).2
  have hP12 := GCD369CubeHahnRegular.add_orderTop_lower
    (T.Xn * (0 : GCD369CubeHahnRegular k) * (3 * r + 0))
    (M * B * (0 : GCD369CubeHahnRegular k)) T.delta hP1 hP2
  have hPinner := GCD369CubeHahnRegular.add_orderTop_lower
    (T.Xn * (0 : GCD369CubeHahnRegular k) * (3 * r + 0) +
      M * B * (0 : GCD369CubeHahnRegular k))
    (H * (B2 * (r + 0) + C2)) T.delta hP12 hP3
  have hphi0 := GCD369CubeHahnRegular.mul_orderTop_lower
    H (T.Xn * (0 : GCD369CubeHahnRegular k) * (3 * r + 0) +
        M * B * (0 : GCD369CubeHahnRegular k) +
        H * (B2 * (r + 0) + C2))
    T.delta T.delta
    (by simpa only [H] using hH.1.ge) hPinner
  have hphi : (↑(2 * T.delta) : WithTop ℚ) ≤
      S.transverseValue.1.orderTop := by
    rw [hphichart]
    simpa only [GCD369CubeDoubleSourceTransverseChart, H, M,
      show T.delta + T.delta = 2 * T.delta by ring] using hphi0
  exact T.doubleRoot_sourceNonic_inconsistent_of_orderBounds_before_c7
    r0 A0 hr0 hA0 hx hX hY hd hp hK hphi

/-- Every root deviation in the double-root chart with `d = 0` and
`3 * delta < 2 * p` is excluded.  The sole input about the deviation not
already present in the chart equations is that its residue vanishes. -/
theorem TransverseFactor.doubleRoot_source_inconsistent_of_chart_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (r0 A0 : k)
    (r w d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta < 2 * S.normal.sextic.scale.p)
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
    exact T.doubleRoot_sourceZero_inconsistent_of_chart_before_c7
      hd r0 A0 r d B B2 C2 hr0 hA0 hp hx hX hY hKchart hphichart
  · rcases GCD369CubeHahnRegular.exists_pos_orderTop_eq_of_constantCoeff_zero
        w hw0 hwz with ⟨nu, hnu, hw⟩
    let c : k := w.1.leadingCoeff
    have hc : c ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr (by
      intro hz
      apply hwz
      exact Subtype.ext hz)
    by_cases hearly : 2 * nu < T.delta
    · exact T.doubleRoot_sourceEarly_inconsistent_of_chart_before_c7
        hd nu r0 A0 c r w d B B2 C2 hr0 hA0 hc hp hnu hearly
        hr hx hX hY hw rfl hKchart hphichart
    · by_cases hmiddle : nu < T.delta
      · exact T.doubleRoot_sourceMiddle_inconsistent_of_chart_before_c7
          hd nu r0 A0 r w d B B2 C2 hr0 hA0 hp hnu
          (by linarith) hmiddle hr hX hw hKchart hphichart
      · exact T.doubleRoot_sourceLate_inconsistent_of_chart_before_c7
          hd nu r0 A0 c r w d B B2 C2 hr0 hA0 hc hp hnu
          (le_of_not_gt hmiddle) hr hx hX hY hw rfl hKchart hphichart

/-- Expanded moving-root coordinates realize the complete double-root chart
before the weight-two load. -/
theorem TransverseFactor.doubleRoot_source_inconsistent_of_coordinates_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (r0 A0 : k)
    (r w d e B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta < 2 * S.normal.sextic.scale.p)
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
  exact T.doubleRoot_source_inconsistent_of_chart_before_c7
    hd r0 A0 r w d B B2 C2 hr0 hA0 hp hr hx hX hY hw0
      hcharts.1 hcharts.2

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceEarly_inconsistent_of_chart_before_c7
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceMiddle_inconsistent_of_chart_before_c7
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceLate_inconsistent_of_chart_before_c7
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceZero_inconsistent_of_chart_before_c7
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_source_inconsistent_of_chart_before_c7
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_source_inconsistent_of_coordinates_before_c7
