import FiniteDoubleRow12C2
import FiniteDoubleRow123C2
import FiniteDoubleC2Load
import FiniteDoubleC7LoadRow4
import FiniteDoubleC2LoadEndpointCoeff

/-! # Closing the balanced `c2` resonance from exact quadratic coordinates

At the equality `7 * p = 3 * delta`, the residual load exponent is the
intrinsic half-scale `delta`.  Given the exact quadratic factorization of
the moving-root deviations, the four literal `c2` equations reduce to the
finite residue system that is inconsistent once the half-scale `B`
coefficient vanishes.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- At the balanced active-`c2` resonance, exact quadratic coordinates with
vanishing half-scale `B` residue make the loaded source equations
inconsistent. -/
theorem TransverseFactor.doubleRoot_c2Load_source_inconsistent_of_eq
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
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
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hEq : 7 * F.scale.p = 3 * T.delta)
    (d Bn q : GCD369CubeHahnRegular k)
    (hBn0 : GCD369CubeHahnRegular.constantCoeff Bn = 0)
    (hD : S.cubicU + 3 * r ^ 2 =
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) ^ 2 * d)
    (hB : T.Yn - r * T.Xn =
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * Bn)
    (hC : T.Zn + 2 * r ^ 2 * T.Xn =
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) ^ 2 * q -
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * r * Bn) : False := by
  let mu : ℚ := T.delta / 2
  have hmu : 0 < mu := by dsimp only [mu]; linarith [T.hdelta]
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial mu hmu.le
  have hM : GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num)) = M := by
    apply Subtype.ext
    rfl
  rw [hM] at hD hB hC
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * T.Xn
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * T.Xn
  let Dq : GCD369CubeHahnRegular k := M ^ 2 * d
  let Bq : GCD369CubeHahnRegular k := M * Bn
  let Cq : GCD369CubeHahnRegular k := M ^ 2 * q - M * r * Bn
  have hDq : D = Dq := by simpa only [D, Dq] using hD
  have hBq : B = Bq := by simpa only [B, Bq] using hB
  have hCq : C = Cq := by simpa only [C, Cq] using hC
  let Row1 : GCD369CubeHahnRegular k :=
    T.Xn ^ 2 * D - 2 * T.Xn * B * r - B ^ 2 - 2 * T.Xn * C
  let Row2 : GCD369CubeHahnRegular k :=
    2 * T.Xn ^ 2 * r * D - 3 * T.Xn * B * r ^ 2 - 3 * T.Xn * C * r +
      3 * T.Xn * B * D - 3 * B * C
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
  have hY' : GCD369CubeHahnRegular.constantCoeff T.Yn =
      GCD369CubeHahnRegular.constantCoeff r * A0 := by
    rw [hr]
    exact hY
  have hload := T.doubleRoot_c2Load_source_coeff_of_eq F hscale
    C2 C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r A0 hroot hu' hv' hX hY' hEq
  dsimp only at hload
  have hlambda : 7 * F.scale.p - 2 * T.delta = 2 * mu := by
    dsimp only [mu]
    linarith [hEq]
  rw [hlambda, hr] at hload
  have hload1 : (-32 * (729 * Row1)).1.coeff (2 * mu) +
      C2 * (82944 * r0 ^ 3) = 0 := by
    simpa only [Row1, D, B, C] using hload.1
  have hload2 : (32 * (-1458 * Row2)).1.coeff (2 * mu) +
      C2 * (-186624 * r0 ^ 4) = 0 := by
    simpa only [Row2, D, B, C] using hload.2.1
  have hload3 : (128 * Row3).1.coeff (2 * mu) - 64 * A0 ^ 3 = 0 := by
    simpa only [Row3, D, B, C] using hload.2.2.1
  have hload4 : (32 * Row4).1.coeff (2 * mu) - 314928 * r0 * A0 ^ 3 +
      C2 * (1866240 * r0 ^ 6) = 0 := by
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
      C2 * (82944 * r0 ^ 3) = 0 := by
    simpa only [QR1] using hload1
  have hload2q : (32 * (-1458 * QR2)).1.coeff (2 * mu) +
      C2 * (-186624 * r0 ^ 4) = 0 := by
    simpa only [QR2] using hload2
  have hload3q : (128 * QR3).1.coeff (2 * mu) - 64 * A0 ^ 3 = 0 := by
    simpa only [QR3] using hload3
  have hload4q : (32 * QR4).1.coeff (2 * mu) - 314928 * r0 * A0 ^ 3 +
      C2 * (1866240 * r0 ^ 6) = 0 := by
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
  apply GCD369CubeDoubleBlowup_c2Load_balanced_resonance_Bzero_inconsistent
    A0 (GCD369CubeHahnRegular.constantCoeff Bn)
      (GCD369CubeHahnRegular.constantCoeff q) r0
      (GCD369CubeHahnRegular.constantCoeff d) C2 hA0 hr0 hBn0
  · linear_combination hload1q
  · linear_combination hload2q
  · linear_combination hload3q
  · linear_combination hload4q

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_c2Load_source_inconsistent_of_eq
