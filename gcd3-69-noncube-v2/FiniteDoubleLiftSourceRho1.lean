import FiniteDoubleLiftRho1
import FiniteDoubleRow12Rho1

/-! # Source-facing deviation lift before the weight-ten load

The half-scale moving-root lift below `rho1` combines with the first two
primitive rows to promote the cubic deviation and corrected transverse
deviation to the full intrinsic scale.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- With `d = c7 = c5 = c4 = c3 = c2 = c1 = 0` and `3 * delta < 10 * p`,
the source-facing moving-root deviations lift from the half scale to the
full `delta` scale. -/
theorem TransverseFactor.doubleRoot_deviations_order_delta_from_source_before_rho1
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0)
    (hc3 : F.c3 = 0)
    (hc2 : F.c2 = 0)
    (hc1 : F.c1 = 0)
    (hp : 3 * T.delta ≤ 10 * F.scale.p)
    (r : GCD369CubeHahnRegular k) (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hu : GCD369CubeHahnRegular.constantCoeff S.cubicU = -3 * r0 ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r0 ^ 2 * A0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0) :
    (↑T.delta : WithTop ℚ) ≤
        (S.cubicU + 3 * r ^ 2).1.orderTop ∧
      ∃ B : GCD369CubeHahnRegular k,
        T.Yn = r * T.Xn +
          GCD369CubeHahnRegular.monomial (T.delta / 2)
            (div_nonneg T.hdelta.le (by norm_num)) * B ∧
        (↑T.delta : WithTop ℚ) ≤
          (T.Zn + 2 * r ^ 2 * T.Xn +
            GCD369CubeHahnRegular.monomial (T.delta / 2)
              (div_nonneg T.hdelta.le (by norm_num)) * r * B).1.orderTop := by
  have hhalf : (↑(T.delta / 2) : WithTop ℚ) ≤
      (S.cubicU + 3 * r ^ 2).1.orderTop ∧
    (↑(T.delta / 2) : WithTop ℚ) ≤
      (T.Yn - r * T.Xn).1.orderTop ∧
    (↑(T.delta / 2) : WithTop ℚ) ≤
      (T.Zn + 2 * r ^ 2 * T.Xn).1.orderTop := by
    by_cases hlt : 3 * T.delta < 10 * F.scale.p
    · exact T.doubleRoot_deviations_order_half_lower_before_rho1
        F hscale hd hc7 hc5 hc4 hc3 hc2 hc1 (le_of_lt hlt) r r0 A0 hr0 hA0 hr hu hX hY hZ
        hroot
    · let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
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
        have hnot : ¬ J.mu < T.delta / 2 := by
          intro hsmall
          let A : GCD369CubeHahnRegular k := T.Xn
          let Row1 : GCD369CubeHahnRegular k :=
            A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
          let Row2 : GCD369CubeHahnRegular k :=
            2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
              3 * A * B * D - 3 * B * C
          let Row3 : GCD369CubeHahnRegular k :=
            -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
              2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D +
              3 * C ^ 2
          have htwoMuDelta : 2 * J.mu < T.delta := by nlinarith
          have hR1 : (↑(2 * J.mu) : WithTop ℚ) ≤ Row1.1.orderTop := by
            rw [HahnSeries.le_orderTop_iff_forall]
            intro q hq
            have hq' : q < 2 * J.mu := WithTop.coe_lt_coe.mp hq
            by_cases hq0 : 0 ≤ q
            · have hrows :=
                T.doubleRoot_row123Coeffs_zero_before_rho1 F hscale hd
                  hc7 hc5 hc4 hc3 hc2 hc1 r hroot q hq0 (by linarith)
                  (by nlinarith [T.hdelta, hp])
              simpa only [Row1, A, D, B, C] using hrows.1
            · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
                (lt_of_not_ge hq0)
          have hR2 : (↑(2 * J.mu) : WithTop ℚ) ≤ Row2.1.orderTop := by
            rw [HahnSeries.le_orderTop_iff_forall]
            intro q hq
            have hq' : q < 2 * J.mu := WithTop.coe_lt_coe.mp hq
            by_cases hq0 : 0 ≤ q
            · have hrows :=
                T.doubleRoot_row123Coeffs_zero_before_rho1 F hscale hd
                  hc7 hc5 hc4 hc3 hc2 hc1 r hroot q hq0 (by linarith)
                  (by nlinarith [T.hdelta, hp])
              simpa only [Row2, A, D, B, C] using hrows.2.1
            · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row2
                (lt_of_not_ge hq0)
          have hrows2 := T.doubleRoot_row123Coeffs_zero_before_rho1
            F hscale hd hc7 hc5 hc4 hc3 hc2 hc1 r hroot (2 * J.mu)
            (by linarith [J.hmu]) htwoMuDelta
            (by nlinarith [T.hdelta, hp])
          have hz1 : Row1.1.coeff (2 * J.mu) = 0 := by
            simpa only [Row1, A, D, B, C] using hrows2.1
          have hz2 : Row2.1.coeff (2 * J.mu) = 0 := by
            simpa only [Row2, A, D, B, C] using hrows2.2.1
          have hz3 : Row3.1.coeff (2 * J.mu) = 0 := by
            simpa only [Row3, A, D, B, C] using hrows2.2.2
          exact GCD369CubeHahnRegular.doubleBlowup_quadratic_inconsistent
            A r D B C J (by simpa only [A] using (by rw [hX]; exact hA0))
            (by rw [hr]; exact hr0)
            (by simpa only [Row1] using hR1)
            (by simpa only [Row2] using hR2)
            (by simpa only [Row1] using hz1)
            (by simpa only [Row2] using hz2)
            (by simpa only [Row3] using hz3)
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
  let mu : ℚ := T.delta / 2
  have hmu : 0 < mu := by dsimp only [mu]; linarith [T.hdelta]
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial mu hmu.le
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let Bdev : GCD369CubeHahnRegular k := T.Yn - r * T.Xn
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * T.Xn
  have hDhalf : (↑mu : WithTop ℚ) ≤ D.1.orderTop := by
    simpa only [mu, D] using hhalf.1
  have hBhalf : (↑mu : WithTop ℚ) ≤ Bdev.1.orderTop := by
    simpa only [mu, Bdev] using hhalf.2.1
  have hChalf : (↑mu : WithTop ℚ) ≤ C.1.orderTop := by
    simpa only [mu, C] using hhalf.2.2
  let Dn : GCD369CubeHahnRegular k := GCD369CubeHahnRegular.shift D mu hDhalf
  let Bn : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Bdev mu hBhalf
  let Cn : GCD369CubeHahnRegular k := GCD369CubeHahnRegular.shift C mu hChalf
  have hDfact : M * Dn = D := by
    simpa only [M, Dn] using GCD369CubeHahnRegular.monomial_mul_shift
      D mu hmu.le hDhalf
  have hBfact : M * Bn = Bdev := by
    simpa only [M, Bn] using GCD369CubeHahnRegular.monomial_mul_shift
      Bdev mu hmu.le hBhalf
  have hCfact : M * Cn = C := by
    simpa only [M, Cn] using GCD369CubeHahnRegular.monomial_mul_shift
      C mu hmu.le hChalf
  let Qn : GCD369CubeHahnRegular k := Cn + r * Bn
  let Row1 : GCD369CubeHahnRegular k :=
    T.Xn ^ 2 * D - 2 * T.Xn * Bdev * r - Bdev ^ 2 - 2 * T.Xn * C
  let Row2 : GCD369CubeHahnRegular k :=
    2 * T.Xn ^ 2 * r * D - 3 * T.Xn * Bdev * r ^ 2 - 3 * T.Xn * C * r +
      3 * T.Xn * Bdev * D - 3 * Bdev * C
  have hRow1 : (↑T.delta : WithTop ℚ) ≤ Row1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' : q < T.delta := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hrows := T.doubleRoot_row12Coeffs_zero_before_rho1 F hscale hd hc7
        hc5 hc4 hc3 hc2 hc1 r hroot q hq0 (by nlinarith [T.hdelta, hp])
      simpa only [Row1, D, Bdev, C] using hrows.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
        (lt_of_not_ge hq0)
  have hRow2 : (↑T.delta : WithTop ℚ) ≤ Row2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' : q < T.delta := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hrows := T.doubleRoot_row12Coeffs_zero_before_rho1 F hscale hd hc7
        hc5 hc4 hc3 hc2 hc1 r hroot q hq0 (by nlinarith [T.hdelta, hp])
      simpa only [Row2, D, Bdev, C] using hrows.2
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row2
        (lt_of_not_ge hq0)
  let FRow1 : GCD369CubeHahnRegular k :=
    M * (T.Xn ^ 2 * Dn - 2 * T.Xn * Qn) - M ^ 2 * Bn ^ 2
  let FRow2 : GCD369CubeHahnRegular k :=
    M * (2 * T.Xn ^ 2 * r * Dn - 3 * T.Xn * r * Qn) +
      M ^ 2 * (3 * T.Xn * Bn * Dn - 3 * Bn * Cn)
  have hfac1 : Row1 = FRow1 := by
    dsimp only [Row1, FRow1, Qn]
    rw [← hDfact, ← hBfact, ← hCfact]
    ring
  have hfac2 : Row2 = FRow2 := by
    dsimp only [Row2, FRow2, Qn]
    rw [← hDfact, ← hBfact, ← hCfact]
    ring
  have hFRow1 : (↑(2 * mu) : WithTop ℚ) ≤ FRow1.1.orderTop := by
    have ht : (2 * mu : ℚ) = T.delta := by dsimp only [mu]; ring
    rw [ht]
    exact hRow1.trans_eq (congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.orderTop) hfac1)
  have hFRow2 : (↑(2 * mu) : WithTop ℚ) ≤ FRow2.1.orderTop := by
    have ht : (2 * mu : ℚ) = T.delta := by dsimp only [mu]; ring
    rw [ht]
    exact hRow2.trans_eq (congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.orderTop) hfac2)
  have hlift :=
    GCD369CubeHahnRegular.doubleBlowup_kernelRemainders_order_lower_of_factoredRows
      mu hmu T.Xn r Dn Bn Cn (by rw [hX]; exact hA0)
      (by rw [hr]; exact hr0)
      (by simpa only [FRow1, M, Qn] using hFRow1)
      (by simpa only [FRow2, M, Qn] using hFRow2)
  have hMorder : (↑mu : WithTop ℚ) ≤ M.1.orderTop := by
    exact (GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
      mu hmu.le).1.ge
  have hDfull0 := GCD369CubeHahnRegular.mul_orderTop_lower
    M Dn mu mu hMorder hlift.1
  have hDfull : (↑T.delta : WithTop ℚ) ≤ D.1.orderTop := by
    have ht : mu + mu = T.delta := by dsimp only [mu]; ring
    rw [ht] at hDfull0
    exact hDfull0.trans_eq (congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.orderTop) hDfact)
  have hQfull0 := GCD369CubeHahnRegular.mul_orderTop_lower
    M Qn mu mu hMorder hlift.2
  have hcorrected : C + M * r * Bn = M * Qn := by
    dsimp only [Qn]
    rw [← hCfact]
    ring
  have hQfull : (↑T.delta : WithTop ℚ) ≤
      (C + M * r * Bn).1.orderTop := by
    have ht : mu + mu = T.delta := by dsimp only [mu]; ring
    rw [ht] at hQfull0
    exact hQfull0.trans_eq (congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.orderTop) hcorrected.symm)
  have hYcoord : T.Yn = r * T.Xn + M * Bn := by
    dsimp only [Bdev] at hBfact
    linear_combination -hBfact
  refine ⟨by simpa only [D] using hDfull, ⟨Bn, ?_, ?_⟩⟩
  · simpa only [M, mu] using hYcoord
  · simpa only [C, M, mu] using hQfull

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_deviations_order_delta_from_source_before_rho1
