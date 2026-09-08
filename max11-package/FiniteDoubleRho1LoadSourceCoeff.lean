import FiniteDoubleLoadSourceCoeff
import FiniteRho1Extraction
import FiniteDoubleRho1LoadPolys

/-! # The moving double-root coefficient at the active `rho1` load

In the strict window `delta < (10 * p) / 2` and `10 * p < 3 * delta`, the
quadratic double-root jet occurs before the weight-ten load, while the
intrinsic cubic occurs after it.  This file extracts the four literal `rho1`
equations at the remaining exponent `10 * p - 2 * delta`.  Unlike a source
coefficient, `rho1` is a target value: only the first primitive row carries
the sparse remainder `62208 * R`.
-/

noncomputable section

namespace GCD369CubeHahnPoleScale

/-- At exponent `10 * p`, a weight-ten ground-field constant times a regular
factor contributes the constant times the factor's residue. -/
theorem weightedRegular_ten_constant_mul_coeff
    {k : Type*} [Field k]
    (S : GCD369CubeHahnPoleScale k) (C : k)
    (P : GCD369CubeHahnRegular k) :
    (S.weightedRegular 10 (GCD369CubeHahnRegular.constant C) * P).1.coeff
        (10 * S.p) = C * GCD369CubeHahnRegular.constantCoeff P := by
  rw [S.weightedRegular_constant_eq_monomial_sq 10 (by norm_num) C]
  have h10p2 : 0 < (10 * S.p) / 2 :=
    div_pos (mul_pos (by norm_num) S.hp) (by norm_num)
  have hcoeff :=
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      ((10 * S.p) / 2) h10p2 C P
  refine (congrArg₂
      (fun m e =>
        (m ^ 2 * GCD369CubeHahnRegular.constant C * P).1.coeff e)
      ?monomial ?exp).trans hcoeff
  · apply Subtype.ext
    simp only [GCD369CubeHahnRegular.monomial]
    congr 1
  · ring

end GCD369CubeHahnPoleScale

#print axioms
  GCD369CubeHahnPoleScale.weightedRegular_ten_constant_mul_coeff

namespace GCD369CubeHahnCommonValueData

/-- In the strict active-`rho1` window `delta < (10 * p) / 2` and
`10 * p < 3 * delta`, the four primitive numerators at exponent `10 * p`
are the shifted double-root rows at residual exponent `10 * p - 2 * delta`,
plus the pure weight-ten load.  The intrinsic cubic terms do not yet
contribute.  The sparse packet is `62208 * R` in the first row and zero in
the remaining three. -/
theorem TransverseFactor.doubleRoot_rho1Load_source_coeff_of_lt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (Rho1 Rho2 Rho3 Rho4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant 0)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hu : S.u = -3 * GCD369CubeHahnRegular.constantCoeff r ^ 2)
    (hv : S.v = 2 * GCD369CubeHahnRegular.constantCoeff r ^ 3)
    (hpLT : T.delta < (10 * F.scale.p) / 2)
    (hpGT : 10 * F.scale.p < 3 * T.delta) :
    let A := T.Xn
    let D := S.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    let R1 := A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
    let R2 :=
      2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C
    let R3 :=
      -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
        2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D + 3 * C ^ 2
    let R4 :=
      4374 * (-3 * r ^ 2 + D) *
        (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
          3 * A * B * D - 3 * B * C)
    let lambda := 10 * F.scale.p - 2 * T.delta
    let r0 := GCD369CubeHahnRegular.constantCoeff r
    ((-32 * (729 * R1)).1.coeff lambda - 62208 * Rho1 = 0) ∧
    ((32 * (-1458 * R2)).1.coeff lambda = 0) ∧
    ((128 * R3).1.coeff lambda = 0) ∧
    ((32 * R4).1.coeff lambda = 0) := by
  dsimp only
  let A : GCD369CubeHahnRegular k := T.Xn
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
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
  let lambda : ℚ := 10 * F.scale.p - 2 * T.delta
  let r0 : k := GCD369CubeHahnRegular.constantCoeff r
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
  let P1 : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.constant (62208 : k)
  let P2 : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.constant (0 : k)
  let P3 : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.constant (0 : k)
  let P4 : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.constant (0 : k)
  let rho1w : GCD369CubeHahnRegular k :=
    S.normal.sextic.scale.weightedRegular 10
      (GCD369CubeHahnRegular.constant Rho1)
  have hpS : S.normal.sextic.scale.p = F.scale.p := by rw [hscale]
  have hlambda : 10 * F.scale.p = lambda + (2 : ℚ) * T.delta := by
    dsimp only [lambda]
    ring
  have hlambda_pos : 0 < lambda := by
    dsimp only [lambda]
    linarith [hpLT]
  have hexp := T.doubleRoot_zeroHigh_expansions r hroot
  have hexp1 : 729 * N1 = (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [N1, R1, A, D, B, C, H] using hexp.1
  have hexp2 : 2187 * N2 = (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [N2, R2, A, D, B, C, H] using hexp.2.1
  have hexp3 : N3 = (128 * R3) * H ^ 2 - (64 * A ^ 3) * H ^ 3 := by
    simpa only [N3, R3, A, D, B, C, H] using hexp.2.2.1
  have hexp4 :
      6561 * N4 =
        (32 * R4) * H ^ 2 -
          (314928 * (r * A + B) * A ^ 2) * H ^ 3 := by
    simpa only [N4, R4, A, D, B, C, H] using hexp.2.2.2
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * (729 * R1)) T.delta lambda T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * (-1458 * R2)) T.delta lambda T.hdelta.le 2
  have hshift3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (128 * R3) T.delta lambda T.hdelta.le 2
  have hshift4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * R4) T.delta lambda T.hdelta.le 2
  change ((-32 * (729 * R1)) * H ^ 2).1.coeff
      (lambda + (2 : ℚ) * T.delta) =
        (-32 * (729 * R1)).1.coeff lambda at hshift1
  change ((32 * (-1458 * R2)) * H ^ 2).1.coeff
      (lambda + (2 : ℚ) * T.delta) =
        (32 * (-1458 * R2)).1.coeff lambda at hshift2
  change ((128 * R3) * H ^ 2).1.coeff
      (lambda + (2 : ℚ) * T.delta) =
        (128 * R3).1.coeff lambda at hshift3
  change ((32 * R4) * H ^ 2).1.coeff
      (lambda + (2 : ℚ) * T.delta) =
        (32 * R4).1.coeff lambda at hshift4
  have hcubic3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (64 * A ^ 3) T.delta (10 * F.scale.p - 3 * T.delta) T.hdelta.le 3
  have hcubic4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (314928 * (r * A + B) * A ^ 2) T.delta
    (10 * F.scale.p - 3 * T.delta) T.hdelta.le 3
  change ((64 * A ^ 3) * H ^ 3).1.coeff
      ((10 * F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta) =
        (64 * A ^ 3).1.coeff (10 * F.scale.p - 3 * T.delta) at hcubic3
  change ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
      ((10 * F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta) =
        (314928 * (r * A + B) * A ^ 2).1.coeff
          (10 * F.scale.p - 3 * T.delta) at hcubic4
  have hneg : 10 * F.scale.p - 3 * T.delta < 0 := by linarith [hpGT]
  have hcubic3zero :
      ((64 * A ^ 3) * H ^ 3).1.coeff (10 * F.scale.p) = 0 := by
    have hrew : (10 * F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta =
        10 * F.scale.p := by ring
    rw [← hrew, hcubic3]
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg _ hneg
  have hcubic4zero :
      ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
          (10 * F.scale.p) = 0 := by
    have hrew : (10 * F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta =
        10 * F.scale.p := by ring
    rw [← hrew, hcubic4]
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg _ hneg
  have hload1 :
      GCD369CubeHahnRegular.constantCoeff P1 = 62208 := by
    have hP := S.rho1LoadPoly1_constantCoeff
    simpa only [P1] using
      (hP.trans (GCD369Cube_rho1LoadRemainders_doubleRoot r0).1)
  have hload2 : GCD369CubeHahnRegular.constantCoeff P2 = 0 := by
    have hP := S.rho1LoadPoly2_constantCoeff
    simpa only [P2] using
      (hP.trans (GCD369Cube_rho1LoadRemainders_doubleRoot r0).2.1)
  have hload3 : GCD369CubeHahnRegular.constantCoeff P3 = 0 := by
    have hP := S.rho1LoadPoly3_constantCoeff
    simpa only [P3] using
      (hP.trans (GCD369Cube_rho1LoadRemainders_doubleRoot r0).2.2.1)
  have hload4 : GCD369CubeHahnRegular.constantCoeff P4 = 0 := by
    have hP := S.rho1LoadPoly4_constantCoeff
    simpa only [P4] using
      (hP.trans (GCD369Cube_rho1LoadRemainders_doubleRoot r0).2.2.2)
  have hweight1 :
      (rho1w * P1).1.coeff (10 * S.normal.sextic.scale.p) =
        Rho1 * GCD369CubeHahnRegular.constantCoeff P1 := by
    simpa only [rho1w] using
      S.normal.sextic.scale.weightedRegular_ten_constant_mul_coeff Rho1 P1
  have hweight2 :
      (rho1w * P2).1.coeff (10 * S.normal.sextic.scale.p) =
        Rho1 * GCD369CubeHahnRegular.constantCoeff P2 := by
    simpa only [rho1w] using
      S.normal.sextic.scale.weightedRegular_ten_constant_mul_coeff Rho1 P2
  have hweight3 :
      (rho1w * P3).1.coeff (10 * S.normal.sextic.scale.p) =
        Rho1 * GCD369CubeHahnRegular.constantCoeff P3 := by
    simpa only [rho1w] using
      S.normal.sextic.scale.weightedRegular_ten_constant_mul_coeff Rho1 P3
  have hweight4 :
      (rho1w * P4).1.coeff (10 * S.normal.sextic.scale.p) =
        Rho1 * GCD369CubeHahnRegular.constantCoeff P4 := by
    simpa only [rho1w] using
      S.normal.sextic.scale.weightedRegular_ten_constant_mul_coeff Rho1 P4
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hz := (F.rho1NCoeff Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4).1
    rw [← hscale] at hz
    change (729 * N1).1.coeff
        (((10 : ℕ) : ℚ) * S.normal.sextic.scale.p) = 62208 * Rho1 at hz
    have hPkt :
        (rho1w * P1).1.coeff (10 * S.normal.sextic.scale.p) =
          62208 * Rho1 := by
      rw [hweight1, hload1, mul_comm]
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (10 * F.scale.p)) hexp1
    rw [hlambda, hshift1] at hc
    have hN :
        (729 * N1).1.coeff (10 * F.scale.p) = 62208 * Rho1 := by
      convert hz using 1
      simp only [hpS]; norm_cast
    calc
      (-32 * (729 * R1)).1.coeff lambda - 62208 * Rho1 =
          (729 * N1).1.coeff (10 * F.scale.p) - 62208 * Rho1 := by
        rw [← hc, hlambda]
      _ = (729 * N1).1.coeff (10 * F.scale.p) -
            (rho1w * P1).1.coeff (10 * S.normal.sextic.scale.p) := by
        rw [hPkt]
      _ = 0 := by rw [hN, hPkt, sub_self]
  · have hz := (F.rho1NCoeff Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4).2.1
    rw [← hscale] at hz
    change (2187 * N2).1.coeff
        (((10 : ℕ) : ℚ) * S.normal.sextic.scale.p) = 0 at hz
    have hPkt :
        (rho1w * P2).1.coeff (10 * S.normal.sextic.scale.p) = 0 := by
      rw [hweight2, hload2, mul_zero]
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (10 * F.scale.p)) hexp2
    rw [hlambda, hshift2] at hc
    have hN : (2187 * N2).1.coeff (10 * F.scale.p) = 0 := by
      convert hz using 1
      simp only [hpS]; norm_cast
    calc
      (32 * (-1458 * R2)).1.coeff lambda =
          (2187 * N2).1.coeff (10 * F.scale.p) := by rw [← hc, hlambda]
      _ = (2187 * N2).1.coeff (10 * F.scale.p) -
            (rho1w * P2).1.coeff (10 * S.normal.sextic.scale.p) := by
        rw [hPkt, sub_zero]
      _ = 0 := by rw [hN, hPkt, sub_self]
  · have hz := (F.rho1NCoeff Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4).2.2.1
    rw [← hscale] at hz
    change N3.1.coeff
        (((10 : ℕ) : ℚ) * S.normal.sextic.scale.p) = 0 at hz
    have hPkt :
        (rho1w * P3).1.coeff (10 * S.normal.sextic.scale.p) = 0 := by
      rw [hweight3, hload3, mul_zero]
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (10 * F.scale.p)) hexp3
    change N3.1.coeff (10 * F.scale.p) =
        ((128 * R3) * H ^ 2).1.coeff (10 * F.scale.p) -
          ((64 * A ^ 3) * H ^ 3).1.coeff (10 * F.scale.p) at hc
    rw [hcubic3zero, sub_zero, hlambda, hshift3] at hc
    have hzN : N3.1.coeff (10 * F.scale.p) = 0 := by
      convert hz using 1
      simp only [hpS]; norm_cast
    calc
      (128 * R3).1.coeff lambda =
          N3.1.coeff (lambda + (2 : ℚ) * T.delta) := hc.symm
      _ = N3.1.coeff (10 * F.scale.p) := by rw [hlambda]
      _ = N3.1.coeff (10 * F.scale.p) -
            (rho1w * P3).1.coeff (10 * S.normal.sextic.scale.p) := by
        rw [hPkt, sub_zero]
      _ = 0 := by rw [hzN, hPkt, sub_self]
  · have hz := (F.rho1NCoeff Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4).2.2.2
    rw [← hscale] at hz
    change (6561 * N4).1.coeff
        (((10 : ℕ) : ℚ) * S.normal.sextic.scale.p) = 0 at hz
    have hPkt :
        (rho1w * P4).1.coeff (10 * S.normal.sextic.scale.p) = 0 := by
      rw [hweight4, hload4, mul_zero]
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (10 * F.scale.p)) hexp4
    change (6561 * N4).1.coeff (10 * F.scale.p) =
        ((32 * R4) * H ^ 2).1.coeff (10 * F.scale.p) -
          ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
            (10 * F.scale.p) at hc
    rw [hcubic4zero, sub_zero, hlambda, hshift4] at hc
    have hN : (6561 * N4).1.coeff (10 * F.scale.p) = 0 := by
      convert hz using 1
      simp only [hpS]; norm_cast
    calc
      (32 * R4).1.coeff lambda =
          (6561 * N4).1.coeff (10 * F.scale.p) := by rw [← hc, hlambda]
      _ = (6561 * N4).1.coeff (10 * F.scale.p) -
            (rho1w * P4).1.coeff (10 * S.normal.sextic.scale.p) := by
        rw [hPkt, sub_zero]
      _ = 0 := by rw [hN, hPkt, sub_self]

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_rho1Load_source_coeff_of_lt
