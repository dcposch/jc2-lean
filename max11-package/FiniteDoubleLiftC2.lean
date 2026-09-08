import FiniteDoubleRow123C2

/-! # The moving double-root half lift below the weight-seven load

After the weight-one, weight-two, weight-four, weight-five, and weight-six
parameters vanish, the same quadratic row argument used before `d` remains
valid below the `c2` load.  In the range `3 * delta < 7 * p`, this is
enough to promote all three moving-root deviations to order at least
`delta / 2`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- On the `d = c7 = c5 = c4 = c3 = 0` stratum with `3 * delta < 7 * p`,
the first nonzero common moving-root deviation cannot occur below the
half scale. -/
theorem TransverseFactor.doubleRoot_firstCommonScale_not_below_half_before_c2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0)
    (hc3 : F.c3 = 0)
    (hp : 3 * T.delta < 7 * F.scale.p)
    (r : GCD369CubeHahnRegular k)
    (hA : GCD369CubeHahnRegular.constantCoeff T.Xn ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r ≠ 0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (J : GCD369CubeHahnRegular.TripleScale
      (S.cubicU + 3 * r ^ 2)
      (T.Yn - r * T.Xn)
      (T.Zn + 2 * r ^ 2 * T.Xn)) :
    ¬ J.mu < T.delta / 2 := by
  intro hsmall
  let A : GCD369CubeHahnRegular k := T.Xn
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  change GCD369CubeHahnRegular.TripleScale D B C at J
  let Row1 : GCD369CubeHahnRegular k :=
    A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
  let Row2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * D - 3 * B * C
  let Row3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D + 3 * C ^ 2
  have htwoMuDelta : 2 * J.mu < T.delta := by nlinarith
  have hR1 : (↑(2 * J.mu) : WithTop ℚ) ≤ Row1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' : q < 2 * J.mu := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hrows := T.doubleRoot_row123Coeffs_zero_before_c2 F hscale hd hc7
        hc5 hc4 hc3 r hroot q hq0 (by linarith) (by nlinarith [T.hdelta, hp])
      simpa only [Row1, A, D, B, C] using hrows.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
        (lt_of_not_ge hq0)
  have hR2 : (↑(2 * J.mu) : WithTop ℚ) ≤ Row2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' : q < 2 * J.mu := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hrows := T.doubleRoot_row123Coeffs_zero_before_c2 F hscale hd hc7
        hc5 hc4 hc3 r hroot q hq0 (by linarith) (by nlinarith [T.hdelta, hp])
      simpa only [Row2, A, D, B, C] using hrows.2.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row2
        (lt_of_not_ge hq0)
  have hrows2 := T.doubleRoot_row123Coeffs_zero_before_c2 F hscale hd hc7
    hc5 hc4 hc3 r hroot (2 * J.mu) (by linarith [J.hmu]) htwoMuDelta
    (by nlinarith [T.hdelta, hp])
  have hz1 : Row1.1.coeff (2 * J.mu) = 0 := by
    simpa only [Row1, A, D, B, C] using hrows2.1
  have hz2 : Row2.1.coeff (2 * J.mu) = 0 := by
    simpa only [Row2, A, D, B, C] using hrows2.2.1
  have hz3 : Row3.1.coeff (2 * J.mu) = 0 := by
    simpa only [Row3, A, D, B, C] using hrows2.2.2
  exact GCD369CubeHahnRegular.doubleBlowup_quadratic_inconsistent
    A r D B C J (by simpa only [A] using hA) hr
    (by simpa only [Row1] using hR1) (by simpa only [Row2] using hR2)
    (by simpa only [Row1] using hz1) (by simpa only [Row2] using hz2)
    (by simpa only [Row3] using hz3)

/-- The pre-`c2` scale exclusion supplies simultaneous half-scale order
bounds for the three canonical moving-root deviations. -/
theorem TransverseFactor.doubleRoot_deviations_order_half_lower_before_c2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0)
    (hc3 : F.c3 = 0)
    (hp : 3 * T.delta < 7 * F.scale.p)
    (r : GCD369CubeHahnRegular k) (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hu : GCD369CubeHahnRegular.constantCoeff S.cubicU = -3 * r0 ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r0 ^ 2 * A0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0) :
    (↑(T.delta / 2) : WithTop ℚ) ≤
        (S.cubicU + 3 * r ^ 2).1.orderTop ∧
      (↑(T.delta / 2) : WithTop ℚ) ≤
        (T.Yn - r * T.Xn).1.orderTop ∧
      (↑(T.delta / 2) : WithTop ℚ) ≤
        (T.Zn + 2 * r ^ 2 * T.Xn).1.orderTop := by
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * T.Xn
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * T.Xn
  have hD0 : GCD369CubeHahnRegular.constantCoeff D = 0 := by
    dsimp only [D]
    simp only [map_add, map_mul, map_pow, map_ofNat, hu, hr]
    ring
  have hB0 : GCD369CubeHahnRegular.constantCoeff B = 0 := by
    dsimp only [B]
    simp only [map_sub, map_mul, hY, hr, hX]
    ring
  have hC0 : GCD369CubeHahnRegular.constantCoeff C = 0 := by
    dsimp only [C]
    simp only [map_add, map_mul, map_pow, map_ofNat, hZ, hr, hX]
    ring
  by_cases hnonzero : D ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0
  · let J : GCD369CubeHahnRegular.TripleScale D B C :=
      GCD369CubeHahnRegular.tripleScale D B C hD0 hB0 hC0 hnonzero
    have hnot := T.doubleRoot_firstCommonScale_not_below_half_before_c2
      F hscale hd hc7 hc5 hc4 hc3 hp r (by rw [hX]; exact hA0)
      (by rw [hr]; exact hr0) hroot J
    have hmu : T.delta / 2 ≤ J.mu := le_of_not_gt hnot
    have hDmu : (↑J.mu : WithTop ℚ) ≤ D.1.orderTop := by
      have hm := GCD369CubeHahnRegular.monomial_mul_orderTop_lower
        J.mu J.hmu.le J.Dn
      exact hm.trans_eq (congrArg (fun z : GCD369CubeHahnRegular k =>
        z.1.orderTop) J.hD).symm
    have hBmu : (↑J.mu : WithTop ℚ) ≤ B.1.orderTop := by
      have hm := GCD369CubeHahnRegular.monomial_mul_orderTop_lower
        J.mu J.hmu.le J.Bn
      exact hm.trans_eq (congrArg (fun z : GCD369CubeHahnRegular k =>
        z.1.orderTop) J.hB).symm
    have hCmu : (↑J.mu : WithTop ℚ) ≤ C.1.orderTop := by
      have hm := GCD369CubeHahnRegular.monomial_mul_orderTop_lower
        J.mu J.hmu.le J.Cn
      exact hm.trans_eq (congrArg (fun z : GCD369CubeHahnRegular k =>
        z.1.orderTop) J.hC).symm
    have hcoe : (↑(T.delta / 2) : WithTop ℚ) ≤ (↑J.mu : WithTop ℚ) :=
      WithTop.coe_le_coe.mpr hmu
    exact ⟨by simpa only [D] using hcoe.trans hDmu,
      by simpa only [B] using hcoe.trans hBmu,
      by simpa only [C] using hcoe.trans hCmu⟩
  · simp only [not_or, not_ne_iff] at hnonzero
    rcases hnonzero with ⟨hDz, hBz, hCz⟩
    constructor
    · rw [show S.cubicU + 3 * r ^ 2 = D by rfl, hDz]
      simp
    constructor
    · rw [show T.Yn - r * T.Xn = B by rfl, hBz]
      simp
    · rw [show T.Zn + 2 * r ^ 2 * T.Xn = C by rfl, hCz]
      simp

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_firstCommonScale_not_below_half_before_c2
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_deviations_order_half_lower_before_c2
