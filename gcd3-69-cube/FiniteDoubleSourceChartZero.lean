import FiniteDoubleSourceChartOrders

/-! # Zero-deviation chart exclusion at the source double root

Specializing the balanced cubic and transverse chart identities to a
vanishing root deviation yields the two order bounds consumed by the
source nonic contradiction.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- In the exact balanced chart, a vanishing root deviation forces the
moving cubic to have order at least `delta` and the transverse value to
have order at least `2 * delta`.  Combined with `p = 3 * delta`, the
source nonic excludes the branch. -/
theorem TransverseFactor.doubleRoot_sourceZero_inconsistent_of_chart
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r0 A0 : k)
    (r d B B2 C2 : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : S.normal.sextic.scale.p = 3 * T.delta)
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
  have hearly : 2 * T.delta < S.normal.sextic.scale.p := by
    rw [hp]
    nlinarith [T.hdelta]
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
  exact T.doubleRoot_sourceNonic_inconsistent_of_orderBounds
    r0 A0 hr0 hA0 hx hX hY hearly hK hphi

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceZero_inconsistent_of_chart
