import FiniteRho2Extraction
import FiniteDoubleLoadSourceCoeff

/-! # The moving double-root coefficient at the active `rho2` load -/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- In the strict active-`rho2` window, the primitive numerators at exponent
`11 * p` are the shifted double-root rows at residual exponent
`11 * p - 2 * delta`.  Only the second row carries the sparse load
`186624 * R`; the intrinsic cubic has not yet arrived. -/
theorem TransverseFactor.doubleRoot_rho2Load_source_coeff_of_lt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (R Rho3 Rho4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant 0)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant 0)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant R)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hpLT : T.delta < (11 * F.scale.p) / 2)
    (hpGT : 11 * F.scale.p < 3 * T.delta) :
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
    let lambda := 11 * F.scale.p - 2 * T.delta
    ((-32 * (729 * R1)).1.coeff lambda = 0) ∧
    ((32 * (-1458 * R2)).1.coeff lambda - 186624 * R = 0) ∧
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
  let lambda : ℚ := 11 * F.scale.p - 2 * T.delta
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
  have hpS : S.normal.sextic.scale.p = F.scale.p := by rw [hscale]
  have hlambda : 11 * F.scale.p = lambda + (2 : ℚ) * T.delta := by
    dsimp only [lambda]
    ring
  have hexp := T.doubleRoot_zeroHigh_expansions r hroot
  have hexp1 : 729 * N1 = (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [N1, R1, A, D, B, C, H] using hexp.1
  have hexp2 : 2187 * N2 = (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [N2, R2, A, D, B, C, H] using hexp.2.1
  have hexp3 : N3 = (128 * R3) * H ^ 2 - (64 * A ^ 3) * H ^ 3 := by
    simpa only [N3, R3, A, D, B, C, H] using hexp.2.2.1
  have hexp4 : 6561 * N4 =
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
      (lambda + (2 : ℚ) * T.delta) = (128 * R3).1.coeff lambda at hshift3
  change ((32 * R4) * H ^ 2).1.coeff
      (lambda + (2 : ℚ) * T.delta) = (32 * R4).1.coeff lambda at hshift4
  have hcubic3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (64 * A ^ 3) T.delta (11 * F.scale.p - 3 * T.delta) T.hdelta.le 3
  have hcubic4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (314928 * (r * A + B) * A ^ 2) T.delta
      (11 * F.scale.p - 3 * T.delta) T.hdelta.le 3
  change ((64 * A ^ 3) * H ^ 3).1.coeff
      ((11 * F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta) =
        (64 * A ^ 3).1.coeff (11 * F.scale.p - 3 * T.delta) at hcubic3
  change ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
      ((11 * F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta) =
        (314928 * (r * A + B) * A ^ 2).1.coeff
          (11 * F.scale.p - 3 * T.delta) at hcubic4
  have hneg : 11 * F.scale.p - 3 * T.delta < 0 := by linarith
  have hcubic3zero :
      ((64 * A ^ 3) * H ^ 3).1.coeff (11 * F.scale.p) = 0 := by
    rw [← show (11 * F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta =
      11 * F.scale.p by ring, hcubic3]
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg _ hneg
  have hcubic4zero :
      ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
        (11 * F.scale.p) = 0 := by
    rw [← show (11 * F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta =
      11 * F.scale.p by ring, hcubic4]
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg _ hneg
  have hcoeff := F.rho2NCoeff R Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hz := hcoeff.1
    rw [← hscale] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (11 * F.scale.p)) hexp1
    rw [hlambda, hshift1] at hc
    calc
      (-32 * (729 * R1)).1.coeff lambda =
          (729 * N1).1.coeff (11 * F.scale.p) := by rw [← hc, hlambda]
      _ = 0 := by
        convert hz using 1
        simp only [N1, hpS]
        norm_cast
  · have hz := hcoeff.2.1
    rw [← hscale] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (11 * F.scale.p)) hexp2
    rw [hlambda, hshift2] at hc
    calc
      (32 * (-1458 * R2)).1.coeff lambda - 186624 * R =
          (2187 * N2).1.coeff (11 * F.scale.p) - 186624 * R := by
            rw [← hc, hlambda]
      _ = 0 := by
        have hz' : (2187 * N2).1.coeff (11 * F.scale.p) = 186624 * R := by
          convert hz using 1
          simp only [N2, hpS]
          norm_cast
        rw [hz', sub_self]
  · have hz := hcoeff.2.2.1
    rw [← hscale] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (11 * F.scale.p)) hexp3
    change N3.1.coeff (11 * F.scale.p) =
      ((128 * R3) * H ^ 2).1.coeff (11 * F.scale.p) -
        ((64 * A ^ 3) * H ^ 3).1.coeff (11 * F.scale.p) at hc
    rw [hcubic3zero, sub_zero, hlambda, hshift3] at hc
    calc
      (128 * R3).1.coeff lambda = N3.1.coeff (11 * F.scale.p) := by
        simpa only [← hlambda] using hc.symm
      _ = 0 := by
        convert hz using 1
        simp only [N3, hpS]
        norm_cast
  · have hz := hcoeff.2.2.2
    rw [← hscale] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (11 * F.scale.p)) hexp4
    change (6561 * N4).1.coeff (11 * F.scale.p) =
      ((32 * R4) * H ^ 2).1.coeff (11 * F.scale.p) -
        ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
          (11 * F.scale.p) at hc
    rw [hcubic4zero, sub_zero, hlambda, hshift4] at hc
    calc
      (32 * R4).1.coeff lambda =
          (6561 * N4).1.coeff (11 * F.scale.p) := by
            simpa only [← hlambda] using hc.symm
      _ = 0 := by
        convert hz using 1
        simp only [N4, hpS]
        norm_cast

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_rho2Load_source_coeff_of_lt
