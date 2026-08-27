import FiniteSimpleSourceChartAll

/-! # First tied-scale consequence at the source simple root

Once the simple-root displacement starts at order `delta`, a nonzero residue
of the nominal half-scale normal correction would make the transverse value
start at `3 * delta / 2`.  The moving cubic starts no earlier than `delta`,
so the literal sextic source equation excludes that possibility.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- In the late simple-root chart, the half-scale correction itself has zero
residue and therefore lifts to the full `delta` scale. -/
theorem TransverseFactor.simpleRoot_sourceLate_normal_residue_zero
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r0 A0 : k)
    (r w d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta ≤ S.normal.sextic.scale.p)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hw0 : GCD369CubeHahnRegular.constantCoeff w = 0)
    (hw : (↑T.delta : WithTop ℚ) ≤ w.1.orderTop)
    (hKchart : S.cubicValue = GCD369CubeSimpleSourceCubicChart
      T.delta T.hdelta.le r w d)
    (hphichart : S.transverseValue =
      GCD369CubeSimpleSourceTransverseChart
        T.delta T.hdelta.le T.Xn r w B B2 C2) :
    GCD369CubeHahnRegular.constantCoeff B = 0 := by
  by_contra hB0
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
  have hB := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    B hB0
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
    M B (T.delta / 2) 0 hM.1 hB.1
  have hN : N.1.orderTop = (↑(T.delta / 2) : WithTop ℚ) := by
    simpa only [N, add_zero] using hNdata.1
  have hAw0 := GCD369CubeHahnRegular.mul_orderTop_lower
    T.Xn w 0 T.delta hA.1.ge hw
  have hAw : (↑T.delta : WithTop ℚ) ≤ (T.Xn * w).1.orderTop := by
    simpa only [zero_add] using hAw0
  have hsum0 := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    N (T.Xn * w) (T.delta / 2) T.delta hN hAw
      (by nlinarith [T.hdelta])
  have hsum : (T.Xn * w + N).1.orderTop =
      (↑(T.delta / 2) : WithTop ℚ) := by
    rw [add_comm]
    exact hsum0.1
  have hprod := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    (T.Xn * w + N) Us (T.delta / 2) 0 hsum hUs.1
  have hprodOrder : ((T.Xn * w + N) * Us).1.orderTop =
      (↑(T.delta / 2) : WithTop ℚ) := by
    simpa only [add_zero] using hprod.1
  have htail0 := GCD369CubeHahnRegular.mul_orderTop_lower
    H Tail T.delta 0 (by simpa only [H] using hH.1.ge) Tail.2
  have htail : (↑T.delta : WithTop ℚ) ≤ (H * Tail).1.orderTop := by
    simpa only [add_zero] using htail0
  have hinner := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
    ((T.Xn * w + N) * Us) (H * Tail)
    (T.delta / 2) T.delta hprodOrder htail
      (by nlinarith [T.hdelta])
  have hphiData := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    H ((T.Xn * w + N) * Us + H * Tail)
    T.delta (T.delta / 2) hH.1 hinner.1
  have hphi : S.transverseValue.1.orderTop =
      (↑(T.delta + T.delta / 2) : WithTop ℚ) := by
    rw [hphichart]
    simpa only [GCD369CubeSimpleSourceTransverseChart, H, M, N, Us, Tail]
      using hphiData.1
  exact T.sourceSextic_inconsistent_of_transverse_below_twiceDelta
    (T.delta + T.delta / 2) hp hK hphi
      (by nlinarith [T.hdelta])

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_sourceLate_normal_residue_zero
