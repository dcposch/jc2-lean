import FiniteDoubleC2LoadSourceCoeff
import FiniteDoubleC2Load

/-! # The moving double-root coefficient at the balanced `c2` resonance

At the equality `7 * p = 3 * delta`, the quadratic double-root jet and the
intrinsic cubic meet the weight-seven load together.  This file extracts the
four literal `c2` equations at residual exponent `7 * p - 2 * delta`,
retaining the `H ^ 3` cubic constants: row 3 contributes `-64 * A0 ^ 3`
and row 4 contributes `-314928 * r0 * A0 ^ 3` once the half-scale
coordinate `B` has vanishing constant coefficient.

After the quadratic coefficient lemmas, these four equations are exactly
the hypotheses of
`GCD369CubeDoubleBlowup_c2Load_balanced_resonance_Bzero_inconsistent`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- At the balanced active-`c2` resonance `7 * p = 3 * delta`, the four
literal `c2` numerators at exponent `7 * p` are the shifted double-root
rows at residual exponent `7 * p - 2 * delta`, plus the pure weight-seven
load, plus the intrinsic cubic constants at exponent `3 * delta`. -/
theorem TransverseFactor.doubleRoot_c2Load_source_coeff_of_eq
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
    (r : GCD369CubeHahnRegular k) (A0 : k)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hu : S.u = -3 * GCD369CubeHahnRegular.constantCoeff r ^ 2)
    (hv : S.v = 2 * GCD369CubeHahnRegular.constantCoeff r ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn =
      GCD369CubeHahnRegular.constantCoeff r * A0)
    (hEq : 7 * F.scale.p = 3 * T.delta) :
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
    let lambda := 7 * F.scale.p - 2 * T.delta
    let r0 := GCD369CubeHahnRegular.constantCoeff r
    ((-32 * (729 * R1)).1.coeff lambda +
        C2 * (82944 * r0 ^ 3) = 0) ∧
    ((32 * (-1458 * R2)).1.coeff lambda +
        C2 * (-186624 * r0 ^ 4) = 0) ∧
    ((128 * R3).1.coeff lambda - 64 * A0 ^ 3 = 0) ∧
    ((32 * R4).1.coeff lambda - 314928 * r0 * A0 ^ 3 +
        C2 * (1866240 * r0 ^ 6) = 0) := by
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
  let lambda : ℚ := 7 * F.scale.p - 2 * T.delta
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
    20736 * S.normal.sextic.scale.regular3
  let P2 : GCD369CubeHahnRegular k :=
    62208 * S.normal.sextic.scale.regular2 -
      20736 * S.normal.sextic.scale.regular4 ^ 2
  let P3 : GCD369CubeHahnRegular k :=
    82944 * S.normal.sextic.scale.regular1 -
      41472 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4
  let P4 : GCD369CubeHahnRegular k :=
    559872 * S.normal.sextic.scale.regular0 -
      186624 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 -
      93312 * S.normal.sextic.scale.regular3 ^ 2 +
      41472 * S.normal.sextic.scale.regular4 ^ 3
  let c2w : GCD369CubeHahnRegular k :=
    S.normal.sextic.scale.weightedRegular 7
      (GCD369CubeHahnRegular.constant C2)
  have hpS : S.normal.sextic.scale.p = F.scale.p := by rw [hscale]
  have hlambda : 7 * F.scale.p = lambda + (2 : ℚ) * T.delta := by
    dsimp only [lambda]
    ring
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
  have hB0 : GCD369CubeHahnRegular.constantCoeff B = 0 := by
    dsimp only [B, A]
    simp only [map_sub, map_mul, hY, hX]
    ring
  have hcubic3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
    T.delta T.hdelta 3 (64 * A ^ 3)
  have hcubic4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
    T.delta T.hdelta 3 (314928 * (r * A + B) * A ^ 2)
  change ((64 * A ^ 3) * H ^ 3).1.coeff (3 * T.delta) =
      GCD369CubeHahnRegular.constantCoeff (64 * A ^ 3) at hcubic3
  change ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
      (3 * T.delta) =
        GCD369CubeHahnRegular.constantCoeff
          (314928 * (r * A + B) * A ^ 2) at hcubic4
  have hcubic3val :
      ((64 * A ^ 3) * H ^ 3).1.coeff (7 * F.scale.p) = 64 * A0 ^ 3 := by
    rw [hEq, hcubic3]
    simp only [map_mul, map_pow, map_ofNat, A, hX]
  have hcubic4val :
      ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
          (7 * F.scale.p) = 314928 * r0 * A0 ^ 3 := by
    rw [hEq, hcubic4]
    simp only [map_mul, map_add, map_pow, map_ofNat, A, hX, hB0]
    dsimp only [r0]
    ring
  have hload1 :
      GCD369CubeHahnRegular.constantCoeff P1 = 82944 * r0 ^ 3 := by
    have hP := S.c2LoadPoly1_constantCoeff
    simpa only [P1] using
      (hP.trans (by
        rw [hv]
        exact (GCD369Cube_c2LoadRemainders_doubleRoot r0).1))
  have hload2 :
      GCD369CubeHahnRegular.constantCoeff P2 = -186624 * r0 ^ 4 := by
    have hP := S.c2LoadPoly2_constantCoeff
    simpa only [P2] using
      (hP.trans (by
        rw [hu]
        exact (GCD369Cube_c2LoadRemainders_doubleRoot r0).2.1))
  have hload3 : GCD369CubeHahnRegular.constantCoeff P3 = 0 := by
    simpa only [P3] using S.c2LoadPoly3_constantCoeff
  have hload4 :
      GCD369CubeHahnRegular.constantCoeff P4 = 1866240 * r0 ^ 6 := by
    have hP := S.c2LoadPoly4_constantCoeff
    simpa only [P4] using
      (hP.trans (by
        rw [hu, hv]
        exact (GCD369Cube_c2LoadRemainders_doubleRoot r0).2.2.2))
  have hweight1 :
      (c2w * P1).1.coeff (7 * S.normal.sextic.scale.p) =
        C2 * GCD369CubeHahnRegular.constantCoeff P1 := by
    simpa only [c2w] using
      S.normal.sextic.scale.weightedRegular_seven_constant_mul_coeff C2 P1
  have hweight2 :
      (c2w * P2).1.coeff (7 * S.normal.sextic.scale.p) =
        C2 * GCD369CubeHahnRegular.constantCoeff P2 := by
    simpa only [c2w] using
      S.normal.sextic.scale.weightedRegular_seven_constant_mul_coeff C2 P2
  have hweight3 :
      (c2w * P3).1.coeff (7 * S.normal.sextic.scale.p) =
        C2 * GCD369CubeHahnRegular.constantCoeff P3 := by
    simpa only [c2w] using
      S.normal.sextic.scale.weightedRegular_seven_constant_mul_coeff C2 P3
  have hweight4 :
      (c2w * P4).1.coeff (7 * S.normal.sextic.scale.p) =
        C2 * GCD369CubeHahnRegular.constantCoeff P4 := by
    simpa only [c2w] using
      S.normal.sextic.scale.weightedRegular_seven_constant_mul_coeff C2 P4
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hz := (F.c2NCoeff_zero C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc1 hrho1 hrho2 hrho3 hrho4).1
    rw [hc2, ← hscale] at hz
    have hform :
        GCD369CubeFaberC2N1
            S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
            S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
            S.normal.sextic.scale.regular4 c2w =
          729 * N1 + c2w * P1 := rfl
    rw [hform, coeff_add] at hz
    change (729 * N1).1.coeff (7 * S.normal.sextic.scale.p) +
        (c2w * P1).1.coeff (7 * S.normal.sextic.scale.p) = 0 at hz
    rw [hweight1, hload1] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (7 * F.scale.p)) hexp1
    rw [hlambda, hshift1] at hc
    calc
      (-32 * (729 * R1)).1.coeff lambda + C2 * (82944 * r0 ^ 3) =
          (729 * N1).1.coeff (7 * F.scale.p) +
            C2 * (82944 * r0 ^ 3) := by rw [← hc, hlambda]
      _ = 0 := by simpa only [hpS] using hz
  · have hz := (F.c2NCoeff_zero C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc1 hrho1 hrho2 hrho3 hrho4).2.1
    rw [hc2, ← hscale] at hz
    have hform :
        GCD369CubeFaberC2N2
            S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
            S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
            S.normal.sextic.scale.regular4 c2w =
          2187 * N2 + c2w * P2 := rfl
    rw [hform, coeff_add] at hz
    change (2187 * N2).1.coeff (7 * S.normal.sextic.scale.p) +
        (c2w * P2).1.coeff (7 * S.normal.sextic.scale.p) = 0 at hz
    rw [hweight2, hload2] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (7 * F.scale.p)) hexp2
    rw [hlambda, hshift2] at hc
    calc
      (32 * (-1458 * R2)).1.coeff lambda + C2 * (-186624 * r0 ^ 4) =
          (2187 * N2).1.coeff (7 * F.scale.p) +
            C2 * (-186624 * r0 ^ 4) := by rw [← hc, hlambda]
      _ = 0 := by simpa only [hpS] using hz
  · have hz := (F.c2NCoeff_zero C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc1 hrho1 hrho2 hrho3 hrho4).2.2.1
    rw [hc2, ← hscale] at hz
    have hform :
        GCD369CubeFaberC2N3
            S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
            S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
            S.normal.sextic.scale.regular4 c2w =
          243 * N3 + c2w * P3 := rfl
    rw [hform, coeff_add] at hz
    change (243 * N3).1.coeff (7 * S.normal.sextic.scale.p) +
        (c2w * P3).1.coeff (7 * S.normal.sextic.scale.p) = 0 at hz
    rw [hweight3, hload3, mul_zero, add_zero] at hz
    have h243 : (243 * N3).1.coeff (7 * S.normal.sextic.scale.p) =
        (243 : k) * N3.1.coeff (7 * S.normal.sextic.scale.p) :=
      GCD369CubeHahnRegular.coeff_nat_mul
        243 N3 (7 * S.normal.sextic.scale.p)
    have hzN : N3.1.coeff (7 * S.normal.sextic.scale.p) = 0 :=
      (mul_eq_zero.mp (h243.symm.trans hz)).resolve_left (by norm_num)
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (7 * F.scale.p)) hexp3
    change N3.1.coeff (7 * F.scale.p) =
        ((128 * R3) * H ^ 2).1.coeff (7 * F.scale.p) -
          ((64 * A ^ 3) * H ^ 3).1.coeff (7 * F.scale.p) at hc
    rw [hcubic3val, hlambda, hshift3] at hc
    rw [hpS, hlambda] at hzN
    exact hc.symm.trans hzN
  · have hz := (F.c2NCoeff_zero C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc1 hrho1 hrho2 hrho3 hrho4).2.2.2
    rw [hc2, ← hscale] at hz
    have hform :
        GCD369CubeFaberC2N4
            S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
            S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
            S.normal.sextic.scale.regular4 c2w =
          6561 * N4 + c2w * P4 := rfl
    rw [hform, coeff_add] at hz
    change (6561 * N4).1.coeff (7 * S.normal.sextic.scale.p) +
        (c2w * P4).1.coeff (7 * S.normal.sextic.scale.p) = 0 at hz
    rw [hweight4, hload4] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (7 * F.scale.p)) hexp4
    change (6561 * N4).1.coeff (7 * F.scale.p) =
        ((32 * R4) * H ^ 2).1.coeff (7 * F.scale.p) -
          ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
            (7 * F.scale.p) at hc
    rw [hcubic4val, hlambda, hshift4] at hc
    calc
      (32 * R4).1.coeff lambda - 314928 * r0 * A0 ^ 3 +
          C2 * (1866240 * r0 ^ 6) =
        (6561 * N4).1.coeff (7 * F.scale.p) +
          C2 * (1866240 * r0 ^ 6) := by rw [← hc, hlambda]
      _ = 0 := by simpa only [hpS] using hz

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_c2Load_source_coeff_of_eq
