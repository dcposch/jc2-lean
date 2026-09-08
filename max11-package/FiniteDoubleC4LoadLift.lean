import FiniteDoubleLiftQuadratic
import FiniteDoubleRow12C4
import FiniteDoubleRow123C4
import FiniteDoubleC4Load
import FiniteDoubleC7LoadRow4
import FiniteDoubleC4LoadSourceCoeff

/-! # Lifting the active weight-five load on the double-root chart

In the strict window `delta < (5 * p) / 2` and `5 * p < 3 * delta`, the
weight-five load arrives at residual exponent `5 * p - 2 * delta`, before
the intrinsic cubic.  The zero-load rows first force every moving-root
deviation to order at least `(5 * p) / 2 - delta`; a second linear lift
then exposes the loaded quadratic residue system.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- In the strict active-`c4` window, the first common nonzero moving-root
deviation cannot occur before half the residual load exponent. -/
theorem TransverseFactor.doubleRoot_firstCommonScale_not_below_c4Load_half
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (_hdeltaP : T.delta < (5 * F.scale.p) / 2)
    (hpDelta : 5 * F.scale.p < 3 * T.delta)
    (r : GCD369CubeHahnRegular k)
    (hA : GCD369CubeHahnRegular.constantCoeff T.Xn ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r ≠ 0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (J : GCD369CubeHahnRegular.TripleScale
      (S.cubicU + 3 * r ^ 2)
      (T.Yn - r * T.Xn)
      (T.Zn + 2 * r ^ 2 * T.Xn)) :
    ¬ J.mu < (5 * F.scale.p) / 2 - T.delta := by
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
  have htwoMuDelta : 2 * J.mu < T.delta := by
    have htwice : 2 * ((5 * F.scale.p) / 2 - T.delta) =
        5 * F.scale.p - 2 * T.delta := by ring
    nlinarith
  have hR1 : (↑(2 * J.mu) : WithTop ℚ) ≤ Row1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' : q < 2 * J.mu := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hrows := T.doubleRoot_row123Coeffs_zero_before_c4 F hscale hd hc7
        hc5 r hroot q hq0 (by linarith) (by
          have htwice : 2 * ((5 * F.scale.p) / 2 - T.delta) =
              5 * F.scale.p - 2 * T.delta := by ring
          linarith)
      simpa only [Row1, A, D, B, C] using hrows.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
        (lt_of_not_ge hq0)
  have hR2 : (↑(2 * J.mu) : WithTop ℚ) ≤ Row2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' : q < 2 * J.mu := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hrows := T.doubleRoot_row123Coeffs_zero_before_c4 F hscale hd hc7
        hc5 r hroot q hq0 (by linarith) (by
          have htwice : 2 * ((5 * F.scale.p) / 2 - T.delta) =
              5 * F.scale.p - 2 * T.delta := by ring
          linarith)
      simpa only [Row2, A, D, B, C] using hrows.2.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row2
        (lt_of_not_ge hq0)
  have hrows2 := T.doubleRoot_row123Coeffs_zero_before_c4 F hscale hd hc7
    hc5 r hroot (2 * J.mu) (by linarith [J.hmu]) htwoMuDelta (by
      have htwice : 2 * ((5 * F.scale.p) / 2 - T.delta) =
          5 * F.scale.p - 2 * T.delta := by ring
      linarith)
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

/-- The scale exclusion supplies simultaneous `(5 * p) / 2 - delta` order
bounds for the three canonical moving-root deviations. -/
theorem TransverseFactor.doubleRoot_deviations_order_c4Load_half_lower
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hdeltaP : T.delta < (5 * F.scale.p) / 2)
    (hpDelta : 5 * F.scale.p < 3 * T.delta)
    (r : GCD369CubeHahnRegular k) (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hu : GCD369CubeHahnRegular.constantCoeff S.cubicU = -3 * r0 ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r0 ^ 2 * A0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0) :
    (↑((5 * F.scale.p) / 2 - T.delta) : WithTop ℚ) ≤
        (S.cubicU + 3 * r ^ 2).1.orderTop ∧
      (↑((5 * F.scale.p) / 2 - T.delta) : WithTop ℚ) ≤
        (T.Yn - r * T.Xn).1.orderTop ∧
      (↑((5 * F.scale.p) / 2 - T.delta) : WithTop ℚ) ≤
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
    have hnot := T.doubleRoot_firstCommonScale_not_below_c4Load_half
      F hscale hd hc7 hc5 hdeltaP hpDelta r
      (by rw [hX]; exact hA0) (by rw [hr]; exact hr0) hroot J
    have hmu : (5 * F.scale.p) / 2 - T.delta ≤ J.mu := le_of_not_gt hnot
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
    have hcoe : (↑((5 * F.scale.p) / 2 - T.delta) : WithTop ℚ) ≤
        (↑J.mu : WithTop ℚ) := WithTop.coe_le_coe.mpr hmu
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

/-- In the strict active-`c4` window, the literal source equations and the
two-stage moving-root lift realize the loaded quadratic system, which is
inconsistent when the weight-five parameter is nonzero. -/
theorem TransverseFactor.doubleRoot_c4Load_source_inconsistent_of_lt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hC4 : C4 ≠ 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r : GCD369CubeHahnRegular k) (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hu : S.u = -3 * r0 ^ 2) (hv : S.v = 2 * r0 ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r0 ^ 2 * A0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hdeltaP : T.delta < (5 * F.scale.p) / 2)
    (hpDelta : 5 * F.scale.p < 3 * T.delta) : False := by
  have hd0 : F.d = 0 := by simpa using hd
  have hc70 : F.c7 = 0 := by simpa using hc7
  have hc50 : F.c5 = 0 := by simpa using hc5
  have huc : GCD369CubeHahnRegular.constantCoeff S.cubicU = -3 * r0 ^ 2 := by
    rw [S.constantCoeff_cubicU, hu]
  have hhalf := T.doubleRoot_deviations_order_c4Load_half_lower
    F hscale hd0 hc70 hc50 hdeltaP hpDelta r r0 A0 hr0 hA0 hr huc hX hY hZ
    hroot
  let mu : ℚ := (5 * F.scale.p) / 2 - T.delta
  have hmu : 0 < mu := by dsimp only [mu]; linarith
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial mu hmu.le
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * T.Xn
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * T.Xn
  have hDhalf : (↑mu : WithTop ℚ) ≤ D.1.orderTop := by
    simpa only [mu, D] using hhalf.1
  have hBhalf : (↑mu : WithTop ℚ) ≤ B.1.orderTop := by
    simpa only [mu, B] using hhalf.2.1
  have hChalf : (↑mu : WithTop ℚ) ≤ C.1.orderTop := by
    simpa only [mu, C] using hhalf.2.2
  let Dn : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift D mu hDhalf
  let Bn : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift B mu hBhalf
  let Cn : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift C mu hChalf
  have hDfact : M * Dn = D := by
    simpa only [M, Dn] using GCD369CubeHahnRegular.monomial_mul_shift
      D mu hmu.le hDhalf
  have hBfact : M * Bn = B := by
    simpa only [M, Bn] using GCD369CubeHahnRegular.monomial_mul_shift
      B mu hmu.le hBhalf
  have hCfact : M * Cn = C := by
    simpa only [M, Cn] using GCD369CubeHahnRegular.monomial_mul_shift
      C mu hmu.le hChalf
  let Qn : GCD369CubeHahnRegular k := Cn + r * Bn
  let Row1 : GCD369CubeHahnRegular k :=
    T.Xn ^ 2 * D - 2 * T.Xn * B * r - B ^ 2 - 2 * T.Xn * C
  let Row2 : GCD369CubeHahnRegular k :=
    2 * T.Xn ^ 2 * r * D - 3 * T.Xn * B * r ^ 2 - 3 * T.Xn * C * r +
      3 * T.Xn * B * D - 3 * B * C
  have hRow1 : (↑(2 * mu) : WithTop ℚ) ≤ Row1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < 2 * mu := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · have hrows := T.doubleRoot_row12Coeffs_zero_before_c4 F hscale hd0
        hc70 hc50 r hroot e he0 (by
          dsimp only [mu] at he'
          have htwice : 2 * ((5 * F.scale.p) / 2 - T.delta) =
              5 * F.scale.p - 2 * T.delta := by ring
          linarith)
      simpa only [Row1, D, B, C] using hrows.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
        (lt_of_not_ge he0)
  have hRow2 : (↑(2 * mu) : WithTop ℚ) ≤ Row2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < 2 * mu := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · have hrows := T.doubleRoot_row12Coeffs_zero_before_c4 F hscale hd0
        hc70 hc50 r hroot e he0 (by
          dsimp only [mu] at he'
          have htwice : 2 * ((5 * F.scale.p) / 2 - T.delta) =
              5 * F.scale.p - 2 * T.delta := by ring
          linarith)
      simpa only [Row2, D, B, C] using hrows.2
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row2
        (lt_of_not_ge he0)
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
  have hFRow1 : (↑(2 * mu) : WithTop ℚ) ≤ FRow1.1.orderTop :=
    hRow1.trans_eq (congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.orderTop) hfac1)
  have hFRow2 : (↑(2 * mu) : WithTop ℚ) ≤ FRow2.1.orderTop :=
    hRow2.trans_eq (congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.orderTop) hfac2)
  have hlift :=
    GCD369CubeHahnRegular.doubleBlowup_kernelRemainders_order_lower_of_factoredRows
      mu hmu T.Xn r Dn Bn Cn (by rw [hX]; exact hA0)
      (by rw [hr]; exact hr0)
      (by simpa only [FRow1, M, Qn] using hFRow1)
      (by simpa only [FRow2, M, Qn] using hFRow2)
  let d : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Dn mu hlift.1
  let q : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Qn mu hlift.2
  have hdnfact : M * d = Dn := by
    simpa only [M, d] using GCD369CubeHahnRegular.monomial_mul_shift
      Dn mu hmu.le hlift.1
  have hqnfact : M * q = Qn := by
    simpa only [M, q] using GCD369CubeHahnRegular.monomial_mul_shift
      Qn mu hmu.le hlift.2
  let Dq : GCD369CubeHahnRegular k := M ^ 2 * d
  let Bq : GCD369CubeHahnRegular k := M * Bn
  let Cq : GCD369CubeHahnRegular k := M ^ 2 * q - M * r * Bn
  have hDq : D = Dq := by
    calc
      D = M * Dn := hDfact.symm
      _ = M * (M * d) := congrArg (fun z => M * z) hdnfact.symm
      _ = Dq := by dsimp only [Dq]; ring
  have hBq : B = Bq := by simpa only [Bq] using hBfact.symm
  have hCn : Cn = M * q - r * Bn := by
    dsimp only [Qn] at hqnfact
    linear_combination -hqnfact
  have hCq : C = Cq := by
    calc
      C = M * Cn := hCfact.symm
      _ = M * (M * q - r * Bn) := congrArg (fun z => M * z) hCn
      _ = Cq := by dsimp only [Cq]; ring
  let Row3 : GCD369CubeHahnRegular k :=
    -2 * T.Xn ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
      2 * T.Xn ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * T.Xn * C * D + 3 * C ^ 2
  let Row4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * r ^ 2 + D) *
      (T.Xn * B * r ^ 2 + 2 * B ^ 2 * r + T.Xn * C * r +
        3 * T.Xn * B * D - 3 * B * C)
  have hu' : S.u = -3 * GCD369CubeHahnRegular.constantCoeff r ^ 2 := by
    rw [hr]
    exact hu
  have hv' : S.v = 2 * GCD369CubeHahnRegular.constantCoeff r ^ 3 := by
    rw [hr]
    exact hv
  have hload := T.doubleRoot_c4Load_source_coeff_of_lt F hscale
    C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r hroot hu' hv' hdeltaP hpDelta
  dsimp only at hload
  have hlambda : 5 * F.scale.p - 2 * T.delta = 2 * mu := by
    dsimp only [mu]
    ring
  rw [hlambda, hr] at hload
  have hload1 : (-32 * (729 * Row1)).1.coeff (2 * mu) +
      C4 * (-165888 * r0 ^ 5) = 0 := by
    simpa only [Row1, D, B, C] using hload.1
  have hload2 : (32 * (-1458 * Row2)).1.coeff (2 * mu) +
      C4 * (414720 * r0 ^ 6) = 0 := by
    simpa only [Row2, D, B, C] using hload.2.1
  have hload3 : (128 * Row3).1.coeff (2 * mu) = 0 := by
    simpa only [Row3, D, B, C] using hload.2.2.1
  have hload4 : (32 * Row4).1.coeff (2 * mu) +
      C4 * (-4665600 * r0 ^ 8) = 0 := by
    simpa only [Row4, D, B, C] using hload.2.2.2
  dsimp only [Row1, Row2, Row3, Row4] at hload1 hload2 hload3 hload4
  rw [hDq, hBq, hCq] at hload1 hload2 hload3 hload4
  let QR1 : GCD369CubeHahnRegular k :=
    T.Xn ^ 2 * Dq - 2 * T.Xn * Bq * r - Bq ^ 2 - 2 * T.Xn * Cq
  let QR2 : GCD369CubeHahnRegular k :=
    2 * T.Xn ^ 2 * r * Dq - 3 * T.Xn * Bq * r ^ 2 -
      3 * T.Xn * Cq * r + 3 * T.Xn * Bq * Dq - 3 * Bq * Cq
  let QR3 : GCD369CubeHahnRegular k :=
    -2 * T.Xn ^ 2 * r ^ 2 * Dq + 6 * Bq ^ 2 * r ^ 2 +
      2 * T.Xn ^ 2 * Dq ^ 2 - 2 * Bq ^ 2 * Dq -
        4 * T.Xn * Cq * Dq + 3 * Cq ^ 2
  let QR4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * r ^ 2 + Dq) *
      (T.Xn * Bq * r ^ 2 + 2 * Bq ^ 2 * r + T.Xn * Cq * r +
        3 * T.Xn * Bq * Dq - 3 * Bq * Cq)
  have hload1q : (-32 * (729 * QR1)).1.coeff (2 * mu) +
      C4 * (-165888 * r0 ^ 5) = 0 := by
    simpa only [QR1] using hload1
  have hload2q : (32 * (-1458 * QR2)).1.coeff (2 * mu) +
      C4 * (414720 * r0 ^ 6) = 0 := by
    simpa only [QR2] using hload2
  have hload3q : (128 * QR3).1.coeff (2 * mu) = 0 := by
    simpa only [QR3] using hload3
  have hload4q : (32 * QR4).1.coeff (2 * mu) +
      C4 * (-4665600 * r0 ^ 8) = 0 := by
    simpa only [QR4] using hload4
  have hquad := GCD369CubeHahnRegular.doubleBlowup_quadratic_coefficients
    mu hmu T.Xn r d Bn q
  have hq1 : QR1.1.coeff (2 * mu) =
      A0 ^ 2 * GCD369CubeHahnRegular.constantCoeff d -
        2 * A0 * GCD369CubeHahnRegular.constantCoeff q -
          GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR1, Dq, Bq, Cq, M, hX, hr] using hquad.1
  have hq2 : QR2.1.coeff (2 * mu) =
      2 * A0 ^ 2 * r0 * GCD369CubeHahnRegular.constantCoeff d -
        3 * A0 * r0 * GCD369CubeHahnRegular.constantCoeff q +
          3 * r0 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR2, Dq, Bq, Cq, M, hX, hr] using hquad.2.1
  have hq3 : QR3.1.coeff (2 * mu) =
      -2 * A0 ^ 2 * r0 ^ 2 * GCD369CubeHahnRegular.constantCoeff d +
        9 * r0 ^ 2 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR3, Dq, Bq, Cq, M, hX, hr] using hquad.2.2
  have hq4 : QR4.1.coeff (2 * mu) =
      -13122 * A0 * r0 ^ 3 * GCD369CubeHahnRegular.constantCoeff q -
        65610 * r0 ^ 3 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR4, Dq, Bq, Cq, M, hX, hr] using
      (GCD369CubeHahnRegular.doubleBlowup_quadratic_row4_coefficient
        mu hmu T.Xn r d Bn q)
  have hs1 : -32 * (729 * QR1) = (-23328 : ℤ) * QR1 := by ring
  have hs2 : 32 * (-1458 * QR2) = (-46656 : ℤ) * QR2 := by ring
  rw [hs1, GCD369CubeHahnRegular.coeff_int_mul, hq1] at hload1q
  rw [hs2, GCD369CubeHahnRegular.coeff_int_mul, hq2] at hload2q
  have hs3 : (128 * QR3).1.coeff (2 * mu) =
      (128 : k) * QR3.1.coeff (2 * mu) :=
    GCD369CubeHahnRegular.coeff_nat_mul 128 QR3 (2 * mu)
  rw [hs3, hq3] at hload3q
  have hs4 : (32 * QR4).1.coeff (2 * mu) =
      (32 : k) * QR4.1.coeff (2 * mu) :=
    GCD369CubeHahnRegular.coeff_nat_mul 32 QR4 (2 * mu)
  rw [hs4, hq4] at hload4q
  apply GCD369CubeDoubleBlowup_c4Load_quadratic_beforeCubic_inconsistent
    A0 (GCD369CubeHahnRegular.constantCoeff Bn)
      (GCD369CubeHahnRegular.constantCoeff q) r0
      (GCD369CubeHahnRegular.constantCoeff d) C4 hr0 hC4
  · linear_combination hload1q
  · linear_combination hload2q
  · exact (mul_eq_zero.mp hload3q).resolve_left (by norm_num)
  · linear_combination hload4q

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_firstCommonScale_not_below_c4Load_half
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_deviations_order_c4Load_half_lower
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_c4Load_source_inconsistent_of_lt
