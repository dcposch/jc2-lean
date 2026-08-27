import FiniteSimpleSourceChart
import FiniteC7SourceElimination

/-! # Pre-resonant orders in the simple-root source chart before `c7`

After the weight-one load has vanished, the same pre-resonant split applies
once `3 * delta < 2 * p`.  The literal sextic source equation still excludes a
transverse value of exact order below `2 * delta`.  Splitting on the order
of the half-scale normal deviation then gives two short contradictions:
either the cubic square uniquely leads the sextic, or the reduced
ninth-Faber equation has a unique leading cubic term below the weight-two
load.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If `K` has order at least `delta` but the transverse value has exact order
strictly below `2 * delta`, their sum cannot have the source-required order
`6 * p` when `3 * delta < 2 * p`. -/
theorem TransverseFactor.sourceSextic_inconsistent_of_transverse_below_twiceDelta_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (beta : ℚ)
    (hp : 3 * T.delta < 2 * S.normal.sextic.scale.p)
    (hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop)
    (hphi : S.transverseValue.1.orderTop =
      (↑beta : WithTop ℚ))
    (hbeta : beta < 2 * T.delta) : False := by
  have hKsq : (↑(2 * T.delta) : WithTop ℚ) ≤
      (S.cubicValue.1 ^ 2).orderTop := by
    by_cases hz : S.cubicValue.1 = 0
    · simp [hz]
    rw [pow_two, HahnSeries.orderTop_mul]
    rw [show 2 * T.delta = T.delta + T.delta by ring,
      WithTop.coe_add]
    exact add_le_add hK hK
  have horders : S.transverseValue.1.orderTop <
      (S.cubicValue.1 ^ 2).orderTop := by
    apply lt_of_eq_of_lt hphi
    exact (WithTop.coe_lt_coe.mpr hbeta).trans_le hKsq
  have hsource := S.commonNormalEquation_orderTop_lower
  change (↑((6 : ℚ) * S.normal.sextic.scale.p) : WithTop ℚ) ≤
    (S.cubicValue.1 ^ 2 + S.transverseValue.1).orderTop at hsource
  rw [HahnSeries.orderTop_add_eq_right horders, hphi,
    WithTop.coe_le_coe] at hsource
  nlinarith [T.hdelta, hp]

/-- If the half-scale normal deviation starts no earlier than the simple-root
displacement, the cubic square uniquely leads the literal sextic equation,
already below the weight-two load. -/
theorem TransverseFactor.simpleRoot_sourceBelow_inconsistent_of_normal_lower_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (alpha : ℚ) (r0 A0 : k)
    (r w d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta < 2 * S.normal.sextic.scale.p)
    (halpha : 0 < alpha) (hbelow : alpha < T.delta)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hw : w.1.orderTop = (↑alpha : WithTop ℚ))
    (hN : (↑alpha : WithTop ℚ) ≤
      ((GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num))) * B).1.orderTop)
    (hKchart : S.cubicValue = GCD369CubeSimpleSourceCubicChart
      T.delta T.hdelta.le r w d)
    (hphichart : S.transverseValue =
      GCD369CubeSimpleSourceTransverseChart
        T.delta T.hdelta.le T.Xn r w B B2 C2) : False := by
  let _ := hd
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  let N : GCD369CubeHahnRegular k := M * B
  let Rw : GCD369CubeHahnRegular k :=
    9 * r ^ 2 - 6 * r * w + w ^ 2
  let Us : GCD369CubeHahnRegular k := w - 3 * r
  let Tail : GCD369CubeHahnRegular k := B2 * (-2 * r + w) + C2
  change (↑alpha : WithTop ℚ) ≤ N.1.orderTop at hN
  have hw0 : GCD369CubeHahnRegular.constantCoeff w = 0 := by
    change w.1.coeff 0 = 0
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [hw]
    exact WithTop.coe_lt_coe.mpr halpha
  have hRwres : GCD369CubeHahnRegular.constantCoeff Rw = 9 * r0 ^ 2 := by
    dsimp only [Rw]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [hr, hw0]
    ring
  have hRw := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    Rw (by rw [hRwres]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0))
  have hUsres : GCD369CubeHahnRegular.constantCoeff Us = -3 * r0 := by
    dsimp only [Us]
    simp only [map_sub, map_mul, map_ofNat]
    rw [hr, hw0]
    ring
  have hUs := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    Us (by rw [hUsres]; exact mul_ne_zero (by norm_num) hr0)
  have hA := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    T.Xn (hX ▸ hA0)
  have hH := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) T.delta T.hdelta.le
  have hwRw := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    w Rw alpha 0 hw hRw.1
  have hmain : (w * Rw).1.orderTop = (↑alpha : WithTop ℚ) := by
    simpa only [add_zero] using hwRw.1
  have hhigh : (↑T.delta : WithTop ℚ) ≤
      (H * (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)
      T.delta 0 (by simpa only [H] using hH.1.ge)
      (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r).2
  have hKdata := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    (w * Rw)
    (H * (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r))
    alpha T.delta hmain hhigh hbelow
  have hK : S.cubicValue.1.orderTop = (↑alpha : WithTop ℚ) := by
    rw [hKchart]
    simpa only [GCD369CubeSimpleSourceCubicChart, H, Rw] using hKdata.1
  have hAw := GCD369CubeHahnRegular.mul_orderTop_lower
    T.Xn w 0 alpha hA.1.ge hw.ge
  have hAw' : (↑alpha : WithTop ℚ) ≤ (T.Xn * w).1.orderTop := by
    simpa only [zero_add] using hAw
  have hsum := GCD369CubeHahnRegular.add_orderTop_lower
    (T.Xn * w) N alpha hAw' hN
  have hprod := GCD369CubeHahnRegular.mul_orderTop_lower
    (T.Xn * w + N) Us alpha 0 hsum hUs.1.ge
  have hprod' : (↑alpha : WithTop ℚ) ≤
      ((T.Xn * w + N) * Us).1.orderTop := by
    simpa only [add_zero] using hprod
  have htailDelta : (↑T.delta : WithTop ℚ) ≤
      (H * Tail).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H Tail T.delta 0 (by simpa only [H] using hH.1.ge) Tail.2
  have htail : (↑alpha : WithTop ℚ) ≤ (H * Tail).1.orderTop :=
    (WithTop.coe_le_coe.mpr hbelow.le).trans htailDelta
  have hinner := GCD369CubeHahnRegular.add_orderTop_lower
    ((T.Xn * w + N) * Us) (H * Tail) alpha hprod' htail
  have hphi0 := GCD369CubeHahnRegular.mul_orderTop_lower
    H ((T.Xn * w + N) * Us + H * Tail)
    T.delta alpha (by simpa only [H] using hH.1.ge) hinner
  have hphi : (↑(T.delta + alpha) : WithTop ℚ) ≤
      S.transverseValue.1.orderTop := by
    rw [hphichart]
    simpa only [GCD369CubeSimpleSourceTransverseChart, H, M, N, Us, Tail]
      using hphi0
  exact T.sourceSextic_inconsistent_of_cubic_dominant
    alpha (T.delta + alpha) hK hphi (by linarith)
    (by nlinarith [T.hdelta, hp, hbelow])

/-- If the half-scale normal deviation starts strictly before the
simple-root displacement, the sextic equation fixes its Newton order.  The
reduced ninth-Faber equation then has a unique leading cubic term below the
weight-two load. -/
theorem TransverseFactor.simpleRoot_sourceBelow_inconsistent_of_normal_exact_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (alpha gamma : ℚ) (r0 A0 c : k)
    (r w d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0) (hc : c ≠ 0)
    (hp : 3 * T.delta < 2 * S.normal.sextic.scale.p)
    (halpha : 0 < alpha) (hbelow : alpha < T.delta)
    (hgammaAlpha : gamma < alpha)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hx : S.normal.sextic.regularX = -2 * r + w)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : T.Yn = r * T.Xn +
      (GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num))) * B +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * B2)
    (hw : w.1.orderTop = (↑alpha : WithTop ℚ))
    (hlcw : w.1.leadingCoeff = c)
    (hN : ((GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))) * B).1.orderTop =
        (↑gamma : WithTop ℚ))
    (hKchart : S.cubicValue = GCD369CubeSimpleSourceCubicChart
      T.delta T.hdelta.le r w d)
    (hphichart : S.transverseValue =
      GCD369CubeSimpleSourceTransverseChart
        T.delta T.hdelta.le T.Xn r w B B2 C2) : False := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  let N : GCD369CubeHahnRegular k := M * B
  let Rw : GCD369CubeHahnRegular k :=
    9 * r ^ 2 - 6 * r * w + w ^ 2
  let Us : GCD369CubeHahnRegular k := w - 3 * r
  let Tail : GCD369CubeHahnRegular k := B2 * (-2 * r + w) + C2
  change N.1.orderTop = (↑gamma : WithTop ℚ) at hN
  have hw0 : GCD369CubeHahnRegular.constantCoeff w = 0 := by
    change w.1.coeff 0 = 0
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [hw]
    exact WithTop.coe_lt_coe.mpr halpha
  have hRwres : GCD369CubeHahnRegular.constantCoeff Rw = 9 * r0 ^ 2 := by
    dsimp only [Rw]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [hr, hw0]
    ring
  have hRw := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    Rw (by rw [hRwres]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0))
  have hUsres : GCD369CubeHahnRegular.constantCoeff Us = -3 * r0 := by
    dsimp only [Us]
    simp only [map_sub, map_mul, map_ofNat]
    rw [hr, hw0]
    ring
  have hUs := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    Us (by rw [hUsres]; exact mul_ne_zero (by norm_num) hr0)
  have hA := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    T.Xn (hX ▸ hA0)
  have hH := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) T.delta T.hdelta.le
  have hwRw := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    w Rw alpha 0 hw hRw.1
  have hmain : (w * Rw).1.orderTop = (↑alpha : WithTop ℚ) := by
    simpa only [add_zero] using hwRw.1
  have hmainLC : (w * Rw).1.leadingCoeff = c * (9 * r0 ^ 2) := by
    rw [hwRw.2, hlcw, hRw.2, hRwres]
  have hhigh : (↑T.delta : WithTop ℚ) ≤
      (H * (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)
      T.delta 0 (by simpa only [H] using hH.1.ge)
      (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r).2
  have hKdata := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    (w * Rw)
    (H * (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r))
    alpha T.delta hmain hhigh hbelow
  have hK : S.cubicValue.1.orderTop = (↑alpha : WithTop ℚ) := by
    rw [hKchart]
    simpa only [GCD369CubeSimpleSourceCubicChart, H, Rw] using hKdata.1
  have hKlc : S.cubicValue.1.leadingCoeff = c * (9 * r0 ^ 2) := by
    rw [hKchart]
    simpa only [GCD369CubeSimpleSourceCubicChart, H, Rw, hmainLC]
      using hKdata.2
  have hAw := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    T.Xn w 0 alpha hA.1 hw
  have hAwOrder : (T.Xn * w).1.orderTop = (↑alpha : WithTop ℚ) := by
    simpa only [zero_add] using hAw.1
  have hsum0 := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    N (T.Xn * w) gamma alpha hN hAwOrder.ge hgammaAlpha
  have hsum : (T.Xn * w + N).1.orderTop =
      (↑gamma : WithTop ℚ) := by
    rw [add_comm]
    exact hsum0.1
  have hprod := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    (T.Xn * w + N) Us gamma 0 hsum hUs.1
  have hprodOrder : ((T.Xn * w + N) * Us).1.orderTop =
      (↑gamma : WithTop ℚ) := by
    simpa only [add_zero] using hprod.1
  have htailDelta : (↑T.delta : WithTop ℚ) ≤
      (H * Tail).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H Tail T.delta 0 (by simpa only [H] using hH.1.ge) Tail.2
  have hinner := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    ((T.Xn * w + N) * Us) (H * Tail) gamma T.delta
    hprodOrder htailDelta (by linarith)
  have hphiData := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    H ((T.Xn * w + N) * Us + H * Tail)
    T.delta gamma hH.1 hinner.1
  have hphi : S.transverseValue.1.orderTop =
      (↑(T.delta + gamma) : WithTop ℚ) := by
    rw [hphichart]
    simpa only [GCD369CubeSimpleSourceTransverseChart, H, M, N, Us, Tail]
      using hphiData.1
  have hresonance : 2 * alpha = T.delta + gamma := by
    rcases S.commonNormal_orderAlternative alpha (T.delta + gamma)
        hK hphi with hfar | hcancel
    · have hle : min (2 * alpha) (T.delta + gamma) ≤ 2 * alpha :=
        min_le_left _ _
      have := hfar.trans hle
      nlinarith [T.hdelta, hp, hbelow]
    · exact hcancel.1
  let L : GCD369CubeHahnRegular k :=
    T.Xn * S.normal.sextic.regularX + 2 * T.Yn
  have hLchart : L = T.Xn * w + 2 * N + 2 * H * B2 := by
    dsimp only [L, N, H, M]
    rw [hx, hY]
    ring
  have htwo := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    (2 : GCD369CubeHahnRegular k) (by
      simp only [map_ofNat]
      norm_num)
  have h2Ndata := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    (2 : GCD369CubeHahnRegular k) N 0 gamma htwo.1 hN
  have h2N : (2 * N).1.orderTop = (↑gamma : WithTop ℚ) := by
    simpa only [zero_add] using h2Ndata.1
  have hHB2 : (↑T.delta : WithTop ℚ) ≤ (H * B2).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H B2 T.delta 0 (by simpa only [H] using hH.1.ge) B2.2
  have h2HB2 : (↑T.delta : WithTop ℚ) ≤ (2 * H * B2).1.orderTop := by
    have hm := GCD369CubeHahnRegular.mul_orderTop_lower
      (2 : GCD369CubeHahnRegular k) (H * B2) 0 T.delta
      htwo.1.ge hHB2
    simpa only [zero_add, mul_assoc] using hm
  have hrest := GCD369CubeHahnRegular.add_orderTop_lower
    (T.Xn * w) (2 * H * B2) alpha hAwOrder.ge
      ((WithTop.coe_le_coe.mpr hbelow.le).trans h2HB2)
  have hLdata := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    (2 * N) (T.Xn * w + 2 * H * B2) gamma alpha
    h2N hrest hgammaAlpha
  have hL : L.1.orderTop = (↑gamma : WithTop ℚ) := by
    rw [hLchart, show T.Xn * w + 2 * N + 2 * H * B2 =
      2 * N + (T.Xn * w + 2 * H * B2) by ring]
    exact hLdata.1
  let E : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn * L
  have hscalar := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    (GCD369CubeHahnRegular.ratCast (3 / 8) : GCD369CubeHahnRegular k)
    (by simp only [GCD369CubeHahnRegular.constantCoeff_ratCast]; norm_num)
  have hqA := GCD369CubeHahnRegular.mul_orderTop_lower
    (GCD369CubeHahnRegular.ratCast (3 / 8) : GCD369CubeHahnRegular k)
    T.Xn 0 0 hscalar.1.ge hA.1.ge
  have hE0 := GCD369CubeHahnRegular.mul_orderTop_lower
    (GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn) L
    0 gamma (by simpa only [zero_add] using hqA) hL.ge
  have hE : (↑gamma : WithTop ℚ) ≤ E.1.orderTop := by
    simpa only [E, zero_add] using hE0
  exact T.reducedFaberNine_inconsistent_of_exact_cubic_order_before_c7
    hd alpha gamma (c * (9 * r0 ^ 2)) halpha
    (mul_ne_zero hc (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)))
    hK hKlc (by simpa only [E, L] using hE)
    (by nlinarith [hresonance, hbelow])
    (by nlinarith [hp, hbelow, T.hdelta])

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.sourceSextic_inconsistent_of_transverse_below_twiceDelta_before_c7
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_sourceBelow_inconsistent_of_normal_lower_before_c7
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_sourceBelow_inconsistent_of_normal_exact_before_c7
