import InfinityC7Balanced
import InfinityC7LateRows
import InfinityC7MiddleRows
import FiniteDoubleC7LoadSourceCoeff

/-! # Assembly of the balanced singular c7 branch at infinity

At `2 p = 3 delta`, the weight-two load, the quadratic double-root
correction, and the intrinsic cubic term occur at the same Hahn exponent.
This file extracts the three source rows needed by the balanced terminal
certificate and closes the source-facing branch.
-/

noncomputable section

namespace GCD369CubeHahnCommonCoefficientData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- At the balanced `c7` resonance, rows one, two, and four are the
residual normal-row coefficients, the pure weight-two load, and, in row
four, the intrinsic cubic coefficient. -/
theorem TransverseScale.c7LoadedNormalRowsAt_balanced
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r A0 : k)
    (hu : D.u = -3 * r ^ 2) (hv : D.v = 2 * r ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A0)
    (htie : 2 * D.faber.scale.p = 3 * T.delta) :
    ((-32 * GCD369CubeNormalRow1
        T.Xn T.Yn T.Zn D.cubicU).1.coeff T.delta -
          532224 * r ^ 8 * C7 = 0) ∧
    ((32 * GCD369CubeNormalRow2
        T.Xn T.Yn T.Zn D.cubicU D.cubicV).1.coeff T.delta +
          1419264 * r ^ 9 * C7 = 0) ∧
    ((32 * GCD369CubeNormalRow4
        T.Xn T.Yn T.Zn D.cubicU D.cubicV).1.coeff T.delta -
          314928 * r * A0 ^ 3 - 17418240 * r ^ 11 * C7 = 0) := by
  let F := D.faber
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let N1 : GCD369CubeHahnRegular k := GCD369CubeFaberN1
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
  let N2 : GCD369CubeHahnRegular k := GCD369CubeFaberN2
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
  let N4 : GCD369CubeHahnRegular k := GCD369CubeFaberN4
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
  let Row1 : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU
  let Row2 : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow2 T.Xn T.Yn T.Zn D.cubicU D.cubicV
  let Row4 : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow4 T.Xn T.Yn T.Zn D.cubicU D.cubicV
  let P1 : GCD369CubeHahnRegular k :=
    12096 * F.scale.regular0 * F.scale.regular4 +
      12096 * F.scale.regular1 * F.scale.regular3 +
      6048 * F.scale.regular2 ^ 2 -
      5040 * F.scale.regular2 * F.scale.regular4 ^ 2 -
      5040 * F.scale.regular3 ^ 2 * F.scale.regular4 +
      770 * F.scale.regular4 ^ 4
  let P2 : GCD369CubeHahnRegular k :=
    36288 * F.scale.regular0 * F.scale.regular3 +
      36288 * F.scale.regular1 * F.scale.regular2 -
      15120 * F.scale.regular1 * F.scale.regular4 ^ 2 -
      30240 * F.scale.regular2 * F.scale.regular3 * F.scale.regular4 -
      5040 * F.scale.regular3 ^ 3 +
      9240 * F.scale.regular3 * F.scale.regular4 ^ 3
  let P4 : GCD369CubeHahnRegular k :=
    326592 * F.scale.regular0 * F.scale.regular1 -
      108864 * F.scale.regular0 * F.scale.regular3 * F.scale.regular4 -
      163296 * F.scale.regular1 * F.scale.regular2 * F.scale.regular4 -
      81648 * F.scale.regular1 * F.scale.regular3 ^ 2 +
      37800 * F.scale.regular1 * F.scale.regular4 ^ 3 -
      108864 * F.scale.regular2 ^ 2 * F.scale.regular3 +
      136080 * F.scale.regular2 * F.scale.regular3 * F.scale.regular4 ^ 2 +
      45360 * F.scale.regular3 ^ 3 * F.scale.regular4 -
      27720 * F.scale.regular3 * F.scale.regular4 ^ 4
  let c7w : GCD369CubeHahnRegular k :=
    F.scale.weightedRegular 2 (GCD369CubeHahnRegular.constant C7)
  have hload1 : GCD369CubeHahnRegular.constantCoeff P1 =
      -532224 * r ^ 8 := by
    dsimp only [P1, F]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    change
      12096 * F.scale.leading0 * F.scale.leading4 +
        12096 * F.scale.leading1 * F.scale.leading3 +
        6048 * F.scale.leading2 ^ 2 -
        5040 * F.scale.leading2 * F.scale.leading4 ^ 2 -
        5040 * F.scale.leading3 ^ 2 * F.scale.leading4 +
        770 * F.scale.leading4 ^ 4 = _
    rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4, hu, hv]
    ring
  have hload2 : GCD369CubeHahnRegular.constantCoeff P2 =
      1419264 * r ^ 9 := by
    dsimp only [P2, F]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    change
      36288 * F.scale.leading0 * F.scale.leading3 +
        36288 * F.scale.leading1 * F.scale.leading2 -
        15120 * F.scale.leading1 * F.scale.leading4 ^ 2 -
        30240 * F.scale.leading2 * F.scale.leading3 * F.scale.leading4 -
        5040 * F.scale.leading3 ^ 3 +
        9240 * F.scale.leading3 * F.scale.leading4 ^ 3 = _
    rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4, hu, hv]
    ring
  have hload4 : GCD369CubeHahnRegular.constantCoeff P4 =
      -17418240 * r ^ 11 := by
    dsimp only [P4, F]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    change
      326592 * F.scale.leading0 * F.scale.leading1 -
        108864 * F.scale.leading0 * F.scale.leading3 * F.scale.leading4 -
        163296 * F.scale.leading1 * F.scale.leading2 * F.scale.leading4 -
        81648 * F.scale.leading1 * F.scale.leading3 ^ 2 +
        37800 * F.scale.leading1 * F.scale.leading4 ^ 3 -
        108864 * F.scale.leading2 ^ 2 * F.scale.leading3 +
        136080 * F.scale.leading2 * F.scale.leading3 * F.scale.leading4 ^ 2 +
        45360 * F.scale.leading3 ^ 3 * F.scale.leading4 -
        27720 * F.scale.leading3 * F.scale.leading4 ^ 4 = _
    rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4, hu, hv]
    ring
  have hweight1 : (c7w * P1).1.coeff (2 * F.scale.p) =
      C7 * GCD369CubeHahnRegular.constantCoeff P1 := by
    simpa only [c7w] using
      F.scale.weightedRegular_two_constant_mul_coeff C7 P1
  have hweight2 : (c7w * P2).1.coeff (2 * F.scale.p) =
      C7 * GCD369CubeHahnRegular.constantCoeff P2 := by
    simpa only [c7w] using
      F.scale.weightedRegular_two_constant_mul_coeff C7 P2
  have hweight4 : (c7w * P4).1.coeff (2 * F.scale.p) =
      C7 * GCD369CubeHahnRegular.constantCoeff P4 := by
    simpa only [c7w] using
      F.scale.weightedRegular_two_constant_mul_coeff C7 P4
  have hz := F.c7NCoeff_zero C5 C4 C3 C2 C1
    Rho1 Rho2 Rho3 Rho4 hd hc5 hc4 hc3 hc2 hc1
    hrho1 hrho2 hrho3 hrho4
  have hz1 := hz.1
  have hz2 := hz.2.1
  have hz4 := hz.2.2.2
  rw [hc7] at hz1 hz2 hz4
  change (729 * N1).1.coeff (2 * F.scale.p) +
      (c7w * P1).1.coeff (2 * F.scale.p) = 0 at hz1
  change (2187 * N2).1.coeff (2 * F.scale.p) +
      (c7w * P2).1.coeff (2 * F.scale.p) = 0 at hz2
  change (6561 * N4).1.coeff (2 * F.scale.p) +
      (c7w * P4).1.coeff (2 * F.scale.p) = 0 at hz4
  rw [hweight1, hload1] at hz1
  rw [hweight2, hload2] at hz2
  rw [hweight4, hload4] at hz4
  have hexp1 := T.zeroHighN1Expansion
  have hexp2 := T.zeroHighN2Expansion
  have hexp4 := T.zeroHighN4Expansion
  rw [monomial_eq_regularMonomial] at hexp1 hexp2 hexp4
  have hc1 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * F.scale.p)) hexp1
  have hc2 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * F.scale.p)) hexp2
  have hc4 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * F.scale.p)) hexp4
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * Row1) T.delta T.delta T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * Row2) T.delta T.delta T.hdelta.le 2
  have hshift4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * Row4) T.delta T.delta T.hdelta.le 2
  change ((-32 * Row1) * H ^ 2).1.coeff
      (T.delta + (2 : ℚ) * T.delta) = (-32 * Row1).1.coeff T.delta
    at hshift1
  change ((32 * Row2) * H ^ 2).1.coeff
      (T.delta + (2 : ℚ) * T.delta) = (32 * Row2).1.coeff T.delta
    at hshift2
  change ((32 * Row4) * H ^ 2).1.coeff
      (T.delta + (2 : ℚ) * T.delta) = (32 * Row4).1.coeff T.delta
    at hshift4
  have hcubic := GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
    T.delta T.hdelta 3 (314928 * T.Yn * T.Xn ^ 2)
  change ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff
      (3 * T.delta) = GCD369CubeHahnRegular.constantCoeff
        (314928 * T.Yn * T.Xn ^ 2) at hcubic
  have hcubicval :
      ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff
          (2 * F.scale.p) = 314928 * r * A0 ^ 3 := by
    rw [htie, hcubic]
    simp only [map_mul, map_pow, map_ofNat, hY, hX]
    ring
  change (729 * N1).1.coeff (2 * F.scale.p) =
      ((-32 * Row1) * H ^ 2).1.coeff (2 * F.scale.p) at hc1
  change (2187 * N2).1.coeff (2 * F.scale.p) =
      ((32 * Row2) * H ^ 2).1.coeff (2 * F.scale.p) at hc2
  change (6561 * N4).1.coeff (2 * F.scale.p) =
      ((32 * Row4) * H ^ 2).1.coeff (2 * F.scale.p) -
        ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff
          (2 * F.scale.p) at hc4
  rw [htie, show 3 * T.delta = T.delta + (2 : ℚ) * T.delta by ring,
    hshift1] at hc1
  rw [htie, show 3 * T.delta = T.delta + (2 : ℚ) * T.delta by ring,
    hshift2] at hc2
  rw [htie, show 3 * T.delta = T.delta + (2 : ℚ) * T.delta by ring,
    hshift4] at hc4
  have hcubicval' :
      ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff
          (T.delta + 2 * T.delta) = 314928 * r * A0 ^ 3 := by
    rw [← show 3 * T.delta = T.delta + 2 * T.delta by ring,
      ← htie]
    exact hcubicval
  rw [hcubicval'] at hc4
  rw [htie, show 3 * T.delta = T.delta + 2 * T.delta by ring]
    at hz1 hz2 hz4
  rw [hc1] at hz1
  rw [hc2] at hz2
  rw [hc4] at hz4
  constructor
  · linear_combination hz1
  constructor
  · linear_combination hz2
  · linear_combination hz4

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- After `d = 0`, the singular resonance `2 p = 3 delta` is impossible
for a constant-core infinity source.  No nonvanishing assumption on `c7`
is required. -/
theorem infinity_c7_singular_balanced_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (htie :
      2 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p =
        3 * T.delta) :
    False := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hdD : D.faber.d = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hd0] using hd
  have hc7D : D.faber.c7 = GCD369CubeHahnRegular.constant P.c7 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc7
  have hc5D : D.faber.c5 = GCD369CubeHahnRegular.constant P.c5 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc5
  have hc4D : D.faber.c4 = GCD369CubeHahnRegular.constant P.c4 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc4
  have hc3D : D.faber.c3 = GCD369CubeHahnRegular.constant P.c3 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc3
  have hc2D : D.faber.c2 = GCD369CubeHahnRegular.constant P.c2 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc2
  have hc1D : D.faber.c1 = GCD369CubeHahnRegular.constant P.c1 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc1
  have hr1D : D.faber.rho1 = GCD369CubeHahnRegular.constant R.rho1 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr1
  have hr2D : D.faber.rho2 = GCD369CubeHahnRegular.constant R.rho2 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr2
  have hr3D : D.faber.rho3 = GCD369CubeHahnRegular.constant R.rho3 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr3
  have hr4D : D.faber.rho4 = GCD369CubeHahnRegular.constant R.rho4 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr4
  have hearly : 2 * T.delta < 2 * D.faber.scale.p := by
    linarith [T.hdelta]
  obtain ⟨hz1, hz2, hz3, hz4⟩ :=
    S.infinity_zeroLoadLeadingRows_before_c7 hsdegree T hd0 hearly
  obtain ⟨r, hA0, hu, hv, hY, hZ⟩ :=
    GCD369CubeZeroLoadNormal_parametrization
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn)
      D.u D.v T.hleading hz1 hz2 hz3 hz4
  let A0 : k := GCD369CubeHahnRegular.constantCoeff T.Xn
  have hr : r ≠ 0 := by
    intro hr0
    have hu0 : D.u = 0 := by rw [hu, hr0]; norm_num
    have hv0 : D.v = 0 := by rw [hv, hr0]; norm_num
    exact D.hprojective.elim (fun h => h hu0) (fun h => h hv0)
  have hdisc : 4 * D.u ^ 3 + 27 * D.v ^ 2 = 0 := by
    rw [hu, hv]
    ring
  have hU : GCD369CubeHahnRegular.constantCoeff D.cubicU ≠ 0 := by
    rw [D.constantCoeff_cubicU, hu]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)
  let rr : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.movingDoubleRoot D.cubicU D.cubicV hU
  have hrr : GCD369CubeHahnRegular.constantCoeff rr = r := by
    exact GCD369CubeHahnRegular.constantCoeff_movingDoubleRoot
      D.cubicU D.cubicV hU r
      (by rw [D.constantCoeff_cubicU, hu])
      (by rw [D.constantCoeff_cubicV, hv]) hr
  have hroot : 2 * D.cubicU * rr + 3 * D.cubicV = 0 :=
    GCD369CubeHahnRegular.movingDoubleRoot_relation D.cubicU D.cubicV hU
  let A : GCD369CubeHahnRegular k := T.Xn
  let ddev : GCD369CubeHahnRegular k := D.cubicU + 3 * rr ^ 2
  let Bdev : GCD369CubeHahnRegular k := T.Yn - rr * A
  let Cdev : GCD369CubeHahnRegular k := T.Zn + 2 * rr ^ 2 * A
  let Row1 : GCD369CubeHahnRegular k :=
    A ^ 2 * ddev - 2 * A * Bdev * rr - Bdev ^ 2 - 2 * A * Cdev
  let Row2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * rr * ddev - 3 * A * Bdev * rr ^ 2 -
      3 * A * Cdev * rr + 3 * A * Bdev * ddev - 3 * Bdev * Cdev
  let Row3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * rr ^ 2 * ddev + 6 * Bdev ^ 2 * rr ^ 2 +
      2 * A ^ 2 * ddev ^ 2 - 2 * Bdev ^ 2 * ddev -
      4 * A * Cdev * ddev + 3 * Cdev ^ 2
  let Row4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * rr ^ 2 + ddev) *
      (A * Bdev * rr ^ 2 + 2 * Bdev ^ 2 * rr + A * Cdev * rr +
        3 * A * Bdev * ddev - 3 * Bdev * Cdev)
  have hddev0 : GCD369CubeHahnRegular.constantCoeff ddev = 0 := by
    dsimp only [ddev]
    simp only [map_add, map_mul, map_pow, map_ofNat,
      D.constantCoeff_cubicU, hrr, hu]
    ring
  have hBdev0 : GCD369CubeHahnRegular.constantCoeff Bdev = 0 := by
    dsimp only [Bdev, A, A0]
    simp only [map_sub, map_mul, hY, hrr]
    ring
  have hCdev0 : GCD369CubeHahnRegular.constantCoeff Cdev = 0 := by
    dsimp only [Cdev, A, A0]
    simp only [map_add, map_mul, map_pow, map_ofNat, hZ, hrr]
    ring
  have hdDz : D.faber.d = 0 := by
    rw [hdD]
    apply Subtype.ext
    simp
  have hrows : ∀ e : ℚ, 0 ≤ e → e < T.delta →
      Row1.1.coeff e = 0 ∧ Row2.1.coeff e = 0 ∧
        Row3.1.coeff e = 0 := by
    intro e he hedelta
    have hearly' : 2 * T.factor.delta + e < 2 * D.faber.scale.p := by
      change 2 * T.delta + e < 2 * D.faber.scale.p
      rw [htie]
      linarith
    have h := T.factor.doubleRoot_row123Coeffs_zero_before_c7_coeff
      hdDz rr hroot e he hedelta hearly'
    simpa only [GCD369CubeHahnCommonCoefficientData.TransverseScale.factor,
      Row1, Row2, Row3, A, ddev, Bdev, Cdev] using h
  have hhalf :=
    GCD369CubeHahnRegular.doubleBlowup_deviations_order_half_lower_of_rows
      T.delta T.hdelta A rr ddev Bdev Cdev hddev0 hBdev0 hCdev0
      (by simpa only [A, A0] using hA0)
      (by simpa only [hrr] using hr)
      (by
        intro e he hedelta
        simpa only [Row1, Row2, Row3] using hrows e he hedelta)
  have hR1 : (↑T.delta : WithTop ℚ) ≤ Row1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < T.delta := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · exact (hrows e he0 he').1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
        (lt_of_not_ge he0)
  have hR2 : (↑T.delta : WithTop ℚ) ≤ Row2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < T.delta := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · exact (hrows e he0 he').2.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row2
        (lt_of_not_ge he0)
  let mu : ℚ := T.delta / 2
  have hmu : 0 < mu := by dsimp only [mu]; linarith [T.hdelta]
  have htwomu : 2 * mu = T.delta := by dsimp only [mu]; ring
  obtain ⟨d0, b0, q0, hq1, hq2, hq4⟩ :=
    GCD369CubeHahnRegular.doubleBlowup_balanced_coefficients_of_order
      mu hmu A rr ddev Bdev Cdev
      (by simpa only [A, A0] using hA0)
      (by simpa only [hrr] using hr)
      (by simpa only [mu] using hhalf.1)
      (by simpa only [mu] using hhalf.2.1)
      (by simpa only [mu] using hhalf.2.2)
      (by simpa only [htwomu, Row1] using hR1)
      (by simpa only [htwomu, Row2] using hR2)
  rw [htwomu] at hq1 hq2 hq4
  have hYeq : T.Yn = rr * A + Bdev := by
    dsimp only [Bdev, A]
    ring
  have hZeq : T.Zn = -2 * rr ^ 2 * A + Cdev := by
    dsimp only [Cdev, A]
    ring
  have hUeq : D.cubicU = -3 * rr ^ 2 + ddev := by
    dsimp only [ddev]
    ring
  let e : GCD369CubeHahnRegular k := D.cubicV - 2 * rr ^ 3
  have hVeq : D.cubicV = 2 * rr ^ 3 + e := by
    dsimp only [e]
    ring
  have hre : 3 * e + 2 * ddev * rr = 0 := by
    dsimp only [e, ddev]
    linear_combination hroot
  have hrow1 : GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU =
      729 * Row1 := by
    rw [show T.Xn = A by rfl, hYeq, hZeq, hUeq]
    simpa only [Row1] using
      (GCD369CubeDoubleBlowupRow1 A Bdev Cdev rr ddev)
  have hrow2 : GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
      D.cubicU D.cubicV = -1458 * Row2 := by
    rw [show T.Xn = A by rfl, hYeq, hZeq, hUeq, hVeq]
    simpa only [Row2] using
      (GCD369CubeDoubleBlowupRow2 A Bdev Cdev rr ddev e hre)
  have hrow4 : GCD369CubeNormalRow4 T.Xn T.Yn T.Zn
      D.cubicU D.cubicV = Row4 := by
    rw [show T.Xn = A by rfl, hYeq, hZeq, hUeq, hVeq]
    simpa only [Row4] using
      (GCD369CubeDoubleBlowupRow4 A Bdev Cdev rr ddev e hre)
  have hord1 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU).1.orderTop := by
    rw [hrow1]
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hz : Row1.1.coeff q = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (hq.trans_le hR1)
    have hs : 729 * Row1 = (729 : ℤ) * Row1 := by ring
    rw [hs, GCD369CubeHahnRegular.coeff_int_mul, hz, mul_zero]
  have hord2 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        D.cubicU D.cubicV).1.orderTop := by
    rw [hrow2]
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hz : Row2.1.coeff q = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (hq.trans_le hR2)
    have hs : -1458 * Row2 = (-1458 : ℤ) * Row2 := by ring
    rw [hs, GCD369CubeHahnRegular.coeff_int_mul, hz, mul_zero]
  have hcoeff1 :
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU).1.coeff T.delta =
        729 * (A0 ^ 2 * d0 - 2 * A0 * q0 - b0 ^ 2) := by
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff T.delta) hrow1
    have hn : (729 * Row1).1.coeff T.delta =
        (729 : k) * Row1.1.coeff T.delta :=
      GCD369CubeHahnRegular.coeff_nat_mul 729 Row1 T.delta
    rw [hn, hq1] at hc
    simpa only [A, A0] using hc
  have hcoeff2 :
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        D.cubicU D.cubicV).1.coeff T.delta =
        -1458 * (2 * A0 ^ 2 * r * d0 - 3 * A0 * r * q0 +
          3 * r * b0 ^ 2) := by
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff T.delta) hrow2
    have hs : -1458 * Row2 = (-1458 : ℤ) * Row2 := by ring
    rw [hs, GCD369CubeHahnRegular.coeff_int_mul, hq2] at hc
    norm_num at hc
    simp only [A, hrr] at hc
    linear_combination hc
  obtain ⟨hload1, hload2, hload4⟩ := T.c7LoadedNormalRowsAt_balanced
    P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
      R.rho1 R.rho2 R.rho3 R.rho4
    hdD hc7D hc5D hc4D hc3D hc2D hc1D
      hr1D hr2D hr3D hr4D
    r A0 hu hv rfl hY htie
  have hcoeff32 : (32 * Row4).1.coeff T.delta =
      (32 : k) * Row4.1.coeff T.delta :=
    GCD369CubeHahnRegular.coeff_nat_mul 32 Row4 T.delta
  rw [hrow1] at hload1
  rw [hrow2] at hload2
  rw [hrow4, hcoeff32, hq4] at hload4
  have hs1 : -32 * (729 * Row1) = (-23328 : ℤ) * Row1 := by ring
  have hs2 : 32 * (-1458 * Row2) = (-46656 : ℤ) * Row2 := by ring
  rw [hs1, GCD369CubeHahnRegular.coeff_int_mul, hq1] at hload1
  rw [hs2, GCD369CubeHahnRegular.coeff_int_mul, hq2] at hload2
  simp only [A, A0, hrr] at hload1 hload2 hload4
  have h5 := S.infinity_c7LoadedTerminalEquation_at_balanced
    hsdegree hdisc T
    P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
    hdD hc7D hc5D hc4D hc3D hc2D hc1D
    r A0 d0 b0 q0 hu hv rfl hY hZ htie
    hord1 hord2 hcoeff1 hcoeff2
  apply GCD369Cube_c7Load_balanced_terminal_inconsistent
    A0 r d0 b0 q0 P.c7 hA0 hr
  · linear_combination hload1
  · linear_combination hload2
  · linear_combination hload4
  · exact h5

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c7LoadedNormalRowsAt_balanced
#print axioms
  GCD369CubePolynomialSource.infinity_c7_singular_balanced_inconsistent
