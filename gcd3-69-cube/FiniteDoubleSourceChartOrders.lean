import FiniteDoubleSourceOrderCases
import FiniteDoubleSourceOrderLower

/-! # Valuations of the moving double-root source chart

These definitions package the exact chart identities into the form used by
the source order split.  The first theorem treats the fractional early range
`ord(w) < delta / 2`.
-/

noncomputable section

/-- The moving cubic after translation to its double root. -/
def GCD369CubeDoubleSourceCubicChart
    {k : Type*} [Field k] [CharZero k]
    (delta : ℚ) (hdelta : 0 ≤ delta)
    (r w d : GCD369CubeHahnRegular k) : GCD369CubeHahnRegular k :=
  w ^ 2 * (3 * r + w) +
    GCD369CubeHahnRegular.monomial delta hdelta *
      (d * w + GCD369CubeHahnRegular.ratCast (1 / 3) * d * r)

/-- The transverse value after the balanced half-scale correction. -/
def GCD369CubeDoubleSourceTransverseChart
    {k : Type*} [Field k] [CharZero k]
    (delta : ℚ) (hdelta : 0 ≤ delta)
    (A r w B B2 C2 : GCD369CubeHahnRegular k) :
    GCD369CubeHahnRegular k :=
  GCD369CubeHahnRegular.monomial delta hdelta *
    (A * w * (3 * r + w) +
      (GCD369CubeHahnRegular.monomial (delta / 2)
        (div_nonneg hdelta (by norm_num))) * B * w +
      GCD369CubeHahnRegular.monomial delta hdelta *
        (B2 * (r + w) + C2))

namespace GCD369CubeHahnCommonValueData

/-- In the exact balanced chart, an early nonzero root deviation has the
orders and leading coefficients consumed by the abstract early-source
contradiction. -/
theorem TransverseFactor.doubleRoot_sourceEarly_inconsistent_of_chart
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (nu : ℚ) (r0 A0 c : k)
    (r w d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0) (hc : c ≠ 0)
    (hp : S.normal.sextic.scale.p = 3 * T.delta)
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
  exact T.doubleRoot_sourceEarly_inconsistent_of_exactOrders
    nu r0 A0 c hr0 hA0 hc hp hnu hearly hx hX hY
    hKorder hKlc hphiOrder hphilc

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceEarly_inconsistent_of_chart
