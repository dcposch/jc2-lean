import FiniteSimpleSourceOrdersC1

/-! # Half-scale order bound before the weight-eight load

After the weight-one, weight-two, weight-four, and weight-five loads vanish,
the late simple-root normal correction still lifts from the nominal half
scale whenever `3 * delta < 8 * p`.  The proof uses only the literal sextic
source equation, so the weight-eight cutoff is enough.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- In the late simple-root chart below the `c1` load, the half-scale
correction starts no earlier than order `delta / 2`. -/
theorem TransverseFactor.simpleRoot_sourceLate_normal_order_half_lower_before_c1
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r0 A0 : k)
    (r w d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta ≤ 8 * S.normal.sextic.scale.p)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hw0 : GCD369CubeHahnRegular.constantCoeff w = 0)
    (hw : (↑T.delta : WithTop ℚ) ≤ w.1.orderTop)
    (hKchart : S.cubicValue = GCD369CubeSimpleSourceCubicChart
      T.delta T.hdelta.le r w d)
    (hphichart : S.transverseValue =
      GCD369CubeSimpleSourceTransverseChart
        T.delta T.hdelta.le T.Xn r w B B2 C2) :
    (↑(T.delta / 2) : WithTop ℚ) ≤ B.1.orderTop := by
  by_contra hnot
  have hlt : B.1.orderTop < (↑(T.delta / 2) : WithTop ℚ) :=
    lt_of_not_ge hnot
  have hBne : B ≠ 0 := by
    intro hzero
    rw [hzero] at hlt
    simp at hlt
  have hBne' : B.1 ≠ 0 := by
    intro hzero
    apply hBne
    exact Subtype.ext hzero
  let gamma : ℚ := B.1.order
  have hB : B.1.orderTop = (↑gamma : WithTop ℚ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hBne').symm
  have hgamma_lt : gamma < T.delta / 2 := by
    apply WithTop.coe_lt_coe.mp
    rw [← hB]
    exact hlt
  have hgamma0 : (0 : ℚ) ≤ gamma := by
    apply WithTop.coe_le_coe.mp
    rw [← hB]
    exact B.2
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
  have hM := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  have hmain := GCD369CubeHahnRegular.mul_orderTop_lower
    w Rw T.delta 0 hw hRw.1.ge
  have hmain' : (↑T.delta : WithTop ℚ) ≤ (w * Rw).1.orderTop := by
    simpa only [add_zero] using hmain
  have hhigh : (↑T.delta : WithTop ℚ) ≤
      (H * (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)).1.orderTop := by
    simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
      H (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)
      T.delta 0 (by simpa only [H] using hH.1.ge)
      (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r).2
  have hKsum := GCD369CubeHahnRegular.add_orderTop_lower
    (w * Rw)
    (H * (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r))
    T.delta hmain' hhigh
  have hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop := by
    rw [hKchart]
    simpa only [GCD369CubeSimpleSourceCubicChart, H, Rw] using hKsum
  have hNdata := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    M B (T.delta / 2) gamma hM.1 hB
  have hN : N.1.orderTop = (↑(T.delta / 2 + gamma) : WithTop ℚ) := by
    simpa only [N] using hNdata.1
  have hAw0 := GCD369CubeHahnRegular.mul_orderTop_lower
    T.Xn w 0 T.delta hA.1.ge hw
  have hAw : (↑T.delta : WithTop ℚ) ≤ (T.Xn * w).1.orderTop := by
    simpa only [zero_add] using hAw0
  have hsum0 := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    N (T.Xn * w) (T.delta / 2 + gamma) T.delta hN hAw
      (by nlinarith [T.hdelta, hgamma_lt, hgamma0])
  have hsum : (T.Xn * w + N).1.orderTop =
      (↑(T.delta / 2 + gamma) : WithTop ℚ) := by
    rw [add_comm]
    exact hsum0.1
  have hprod := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    (T.Xn * w + N) Us (T.delta / 2 + gamma) 0 hsum hUs.1
  have hprodOrder : ((T.Xn * w + N) * Us).1.orderTop =
      (↑(T.delta / 2 + gamma) : WithTop ℚ) := by
    simpa only [add_zero] using hprod.1
  have htail0 := GCD369CubeHahnRegular.mul_orderTop_lower
    H Tail T.delta 0 (by simpa only [H] using hH.1.ge) Tail.2
  have htail : (↑T.delta : WithTop ℚ) ≤ (H * Tail).1.orderTop := by
    simpa only [add_zero] using htail0
  have hinner := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    ((T.Xn * w + N) * Us) (H * Tail)
    (T.delta / 2 + gamma) T.delta hprodOrder htail
      (by nlinarith [T.hdelta, hgamma_lt, hgamma0])
  have hphiData := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    H ((T.Xn * w + N) * Us + H * Tail)
    T.delta (T.delta / 2 + gamma) hH.1 hinner.1
  have hphi : S.transverseValue.1.orderTop =
      (↑(T.delta + (T.delta / 2 + gamma)) : WithTop ℚ) := by
    rw [hphichart]
    simpa only [GCD369CubeSimpleSourceTransverseChart, H, M, N, Us, Tail]
      using hphiData.1
  exact T.sourceSextic_inconsistent_of_transverse_below_twiceDelta_before_c1
    (T.delta + (T.delta / 2 + gamma)) hp hK hphi
      (by nlinarith [T.hdelta, hgamma_lt, hgamma0])

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_sourceLate_normal_order_half_lower_before_c1
