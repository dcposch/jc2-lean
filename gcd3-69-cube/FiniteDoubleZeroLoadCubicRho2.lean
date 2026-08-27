import FiniteDoubleLiftSourceRho2
import FiniteDoubleZeroLoadCubicAlgebra
import FiniteDoubleC7LoadRow4

/-! # The zero-load balanced cubic before `rho2`

Once the canonical double-root deviations have reached the half/full
quadratic chart, the intrinsic cubic appears at total exponent
`3 * delta`.  Strictly before the weight-eleven load all four primitive
rows vanish there.  Their quadratic residues and intrinsic cubic constants
form an inconsistent finite system, without any further source-root
analysis.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

set_option maxHeartbeats 4000000

/-- Exact quadratic double-root coordinates are inconsistent whenever the
intrinsic cubic lies strictly below the `rho2` cutoff. -/
theorem TransverseFactor.doubleRoot_zeroLoad_balanced_cubic_inconsistent_before_rho2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hd : F.d = 0) (hc7 : F.c7 = 0) (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0) (hc3 : F.c3 = 0) (hc2 : F.c2 = 0)
    (hc1 : F.c1 = 0) (hr1 : F.rho1 = 0)
    (hp : 3 * T.delta < 11 * F.scale.p)
    (r d Bn q : GCD369CubeHahnRegular k) (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
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
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let A : GCD369CubeHahnRegular k := T.Xn
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let R1 : GCD369CubeHahnRegular k :=
    A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
  let R2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * D - 3 * B * C
  let R3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D + 3 * C ^ 2
  let R4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * r ^ 2 + D) *
      (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
        3 * A * B * D - 3 * B * C)
  let N1 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  let N2 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  let N3 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  let N4 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  have hz := F.zeroHighNCoeff_zero_before_rho2 hd hc7 hc5 hc4 hc3 hc2 hc1 hr1
    (3 * T.delta) (by nlinarith [T.hdelta]) hp
  rw [← hscale] at hz
  have hexp := T.doubleRoot_zeroHigh_expansions r hroot
  have hexp1 : 729 * N1 = (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [N1, R1, A, D, B, C, H] using hexp.1
  have hexp2 : 2187 * N2 = (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [N2, R2, A, D, B, C, H] using hexp.2.1
  have hexp3 : N3 = (128 * R3) * H ^ 2 - (64 * A ^ 3) * H ^ 3 := by
    simpa only [N3, R3, A, D, B, C, H] using hexp.2.2.1
  have hexp4 : 6561 * N4 =
      (32 * R4) * H ^ 2 - (314928 * (r * A + B) * A ^ 2) * H ^ 3 := by
    simpa only [N4, R4, A, D, B, C, H] using hexp.2.2.2
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * (729 * R1)) T.delta T.delta T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * (-1458 * R2)) T.delta T.delta T.hdelta.le 2
  have hshift3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (128 * R3) T.delta T.delta T.hdelta.le 2
  have hshift4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * R4) T.delta T.delta T.hdelta.le 2
  have hshift1' : ((-32 * (729 * R1)) * H ^ 2).1.coeff
      (3 * T.delta) = (-32 * (729 * R1)).1.coeff T.delta := by
    simpa only [H, Nat.cast_ofNat,
      show T.delta + (2 : ℚ) * T.delta = 3 * T.delta by ring]
      using hshift1
  have hshift2' : ((32 * (-1458 * R2)) * H ^ 2).1.coeff
      (3 * T.delta) = (32 * (-1458 * R2)).1.coeff T.delta := by
    simpa only [H, Nat.cast_ofNat,
      show T.delta + (2 : ℚ) * T.delta = 3 * T.delta by ring]
      using hshift2
  have hshift3' : ((128 * R3) * H ^ 2).1.coeff
      (3 * T.delta) = (128 * R3).1.coeff T.delta := by
    simpa only [H, Nat.cast_ofNat,
      show T.delta + (2 : ℚ) * T.delta = 3 * T.delta by ring]
      using hshift3
  have hshift4' : ((32 * R4) * H ^ 2).1.coeff
      (3 * T.delta) = (32 * R4).1.coeff T.delta := by
    simpa only [H, Nat.cast_ofNat,
      show T.delta + (2 : ℚ) * T.delta = 3 * T.delta by ring]
      using hshift4
  have hcoeff1 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (3 * T.delta)) hexp1
  have hcoeff2 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (3 * T.delta)) hexp2
  have hcoeff3 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (3 * T.delta)) hexp3
  have hcoeff4 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (3 * T.delta)) hexp4
  rw [hshift1'] at hcoeff1
  rw [hshift2'] at hcoeff2
  have hB0 : GCD369CubeHahnRegular.constantCoeff B = 0 := by
    dsimp only [B, A]
    simp only [map_sub, map_mul, hY, hr, hX]
    ring
  have hcubic3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
    T.delta T.hdelta 3 (64 * A ^ 3)
  have hcubic4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
    T.delta T.hdelta 3 (314928 * (r * A + B) * A ^ 2)
  change ((64 * A ^ 3) * H ^ 3).1.coeff (3 * T.delta) =
      GCD369CubeHahnRegular.constantCoeff (64 * A ^ 3) at hcubic3
  change ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
      (3 * T.delta) = GCD369CubeHahnRegular.constantCoeff
        (314928 * (r * A + B) * A ^ 2) at hcubic4
  have hcubic3val : ((64 * A ^ 3) * H ^ 3).1.coeff (3 * T.delta) =
      64 * A0 ^ 3 := by
    rw [hcubic3]
    simp only [map_mul, map_pow, map_ofNat, A, hX]
  have hcubic4val :
      ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
          (3 * T.delta) = 314928 * r0 * A0 ^ 3 := by
    rw [hcubic4]
    simp only [map_mul, map_add, map_pow, map_ofNat, A, hX, hB0, hr]
    ring
  change N3.1.coeff (3 * T.delta) =
      ((128 * R3) * H ^ 2).1.coeff (3 * T.delta) -
        ((64 * A ^ 3) * H ^ 3).1.coeff (3 * T.delta) at hcoeff3
  rw [hshift3', hcubic3val] at hcoeff3
  change (6561 * N4).1.coeff (3 * T.delta) =
      ((32 * R4) * H ^ 2).1.coeff (3 * T.delta) -
        ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
          (3 * T.delta) at hcoeff4
  rw [hshift4', hcubic4val] at hcoeff4
  have hz1 : (-32 * (729 * R1)).1.coeff T.delta = 0 := by
    calc
      _ = (729 * N1).1.coeff (3 * T.delta) := hcoeff1.symm
      _ = 0 := by simpa only [N1] using hz.1
  have hz2 : (32 * (-1458 * R2)).1.coeff T.delta = 0 := by
    calc
      _ = (2187 * N2).1.coeff (3 * T.delta) := hcoeff2.symm
      _ = 0 := by simpa only [N2] using hz.2.1
  have hz3N : N3.1.coeff (3 * T.delta) = 0 := by
    have hn : (243 * N3).1.coeff (3 * T.delta) =
        (243 : k) * N3.1.coeff (3 * T.delta) :=
      GCD369CubeHahnRegular.coeff_nat_mul 243 N3 (3 * T.delta)
    have hs : (243 * N3).1.coeff (3 * T.delta) = 0 := by
      simpa only [N3] using hz.2.2.1
    rw [hn] at hs
    exact (mul_eq_zero.mp hs).resolve_left (by norm_num)
  have hz3 : (128 * R3).1.coeff T.delta - 64 * A0 ^ 3 = 0 := by
    linear_combination -hcoeff3 + hz3N
  have hz4N : (6561 * N4).1.coeff (3 * T.delta) = 0 := by
    simpa only [N4] using hz.2.2.2
  have hz4 : (32 * R4).1.coeff T.delta - 314928 * r0 * A0 ^ 3 = 0 := by
    linear_combination -hcoeff4 + hz4N
  let Dq : GCD369CubeHahnRegular k := M ^ 2 * d
  let Bq : GCD369CubeHahnRegular k := M * Bn
  let Cq : GCD369CubeHahnRegular k := M ^ 2 * q - M * r * Bn
  have hDq : D = Dq := by simpa only [D, Dq] using hD
  have hBq : B = Bq := by simpa only [B, A, Bq] using hB
  have hCq : C = Cq := by simpa only [C, A, Cq] using hC
  dsimp only [R1, R2, R3, R4] at hz1 hz2 hz3 hz4
  rw [hDq, hBq, hCq] at hz1 hz2 hz3 hz4
  let QR1 : GCD369CubeHahnRegular k :=
    A ^ 2 * Dq - 2 * A * Bq * r - Bq ^ 2 - 2 * A * Cq
  let QR2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * Dq - 3 * A * Bq * r ^ 2 - 3 * A * Cq * r +
      3 * A * Bq * Dq - 3 * Bq * Cq
  let QR3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * Dq + 6 * Bq ^ 2 * r ^ 2 +
      2 * A ^ 2 * Dq ^ 2 - 2 * Bq ^ 2 * Dq -
        4 * A * Cq * Dq + 3 * Cq ^ 2
  let QR4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * r ^ 2 + Dq) *
      (A * Bq * r ^ 2 + 2 * Bq ^ 2 * r + A * Cq * r +
        3 * A * Bq * Dq - 3 * Bq * Cq)
  have hz1q : (-32 * (729 * QR1)).1.coeff T.delta = 0 := by
    simpa only [QR1, A] using hz1
  have hz2q : (32 * (-1458 * QR2)).1.coeff T.delta = 0 := by
    simpa only [QR2, A] using hz2
  have hz3q : (128 * QR3).1.coeff T.delta - 64 * A0 ^ 3 = 0 := by
    simpa only [QR3, A] using hz3
  have hz4q : (32 * QR4).1.coeff T.delta - 314928 * r0 * A0 ^ 3 = 0 := by
    simpa only [QR4, A] using hz4
  have hdelta : (2 : ℚ) * mu = T.delta := by dsimp only [mu]; ring
  have hquad := GCD369CubeHahnRegular.doubleBlowup_quadratic_coefficients
    mu hmu A r d Bn q
  have hq1 : QR1.1.coeff T.delta =
      A0 ^ 2 * GCD369CubeHahnRegular.constantCoeff d -
        2 * A0 * GCD369CubeHahnRegular.constantCoeff q -
          GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    rw [← hdelta]
    simpa only [QR1, Dq, Bq, Cq, M, A, hX, hr] using hquad.1
  have hq2 : QR2.1.coeff T.delta =
      2 * A0 ^ 2 * r0 * GCD369CubeHahnRegular.constantCoeff d -
        3 * A0 * r0 * GCD369CubeHahnRegular.constantCoeff q +
          3 * r0 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    rw [← hdelta]
    simpa only [QR2, Dq, Bq, Cq, M, A, hX, hr] using hquad.2.1
  have hq3 : QR3.1.coeff T.delta =
      -2 * A0 ^ 2 * r0 ^ 2 * GCD369CubeHahnRegular.constantCoeff d +
        9 * r0 ^ 2 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    rw [← hdelta]
    simpa only [QR3, Dq, Bq, Cq, M, A, hX, hr] using hquad.2.2
  have hq4 : QR4.1.coeff T.delta =
      -13122 * A0 * r0 ^ 3 * GCD369CubeHahnRegular.constantCoeff q -
        65610 * r0 ^ 3 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    rw [← hdelta]
    simpa only [QR4, Dq, Bq, Cq, M, A, hX, hr] using
      (GCD369CubeHahnRegular.doubleBlowup_quadratic_row4_coefficient
        mu hmu A r d Bn q)
  have hs1 : -32 * (729 * QR1) = (-23328 : ℤ) * QR1 := by ring
  have hs2 : 32 * (-1458 * QR2) = (-46656 : ℤ) * QR2 := by ring
  rw [hs1, GCD369CubeHahnRegular.coeff_int_mul, hq1] at hz1q
  rw [hs2, GCD369CubeHahnRegular.coeff_int_mul, hq2] at hz2q
  have hs3 : (128 * QR3).1.coeff T.delta =
      (128 : k) * QR3.1.coeff T.delta :=
    GCD369CubeHahnRegular.coeff_nat_mul 128 QR3 T.delta
  have hs4 : (32 * QR4).1.coeff T.delta =
      (32 : k) * QR4.1.coeff T.delta :=
    GCD369CubeHahnRegular.coeff_nat_mul 32 QR4 T.delta
  rw [hs3, hq3] at hz3q
  rw [hs4, hq4] at hz4q
  apply GCD369CubeDoubleBlowup_zeroLoad_balanced_cubic_inconsistent
    A0 (GCD369CubeHahnRegular.constantCoeff Bn)
      (GCD369CubeHahnRegular.constantCoeff q) r0
      (GCD369CubeHahnRegular.constantCoeff d) hA0 hr0
  · linear_combination hz1q
  · linear_combination hz2q
  · linear_combination hz3q
  · linear_combination hz4q

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_zeroLoad_balanced_cubic_inconsistent_before_rho2
