import InfinityCoefficientFactor
import FiniteDoubleLiftQuadratic
import FiniteC7EarlyNormal

/-! # Coefficient-only moving-root rows before the c7 load

These lemmas port the foundational double-root coefficient identities from
the finite common-value packet to the lightweight infinity coefficient
packet.  No recovered source coordinate or scale-identification hypothesis
is used.
-/

noncomputable section

namespace GCD369CubeHahnCommonCoefficientData

theorem TransverseFactor.doubleRoot_zeroHigh_expansions_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0) :
    let A := T.Xn
    let d := D.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (729 * GCD369CubeFaberN1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (-32 * (729 *
        (A ^ 2 * d - 2 * A * B * r - B ^ 2 - 2 * A * C))) * H ^ 2) ∧
    (2187 * GCD369CubeFaberN2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (32 * (-1458 *
        (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
          3 * A * C * r + 3 * A * B * d - 3 * B * C))) * H ^ 2) ∧
    (GCD369CubeFaberN3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (128 *
        (-2 * A ^ 2 * r ^ 2 * d + 6 * B ^ 2 * r ^ 2 +
          2 * A ^ 2 * d ^ 2 - 2 * B ^ 2 * d - 4 * A * C * d +
          3 * C ^ 2)) * H ^ 2 - (64 * A ^ 3) * H ^ 3) ∧
    (6561 * GCD369CubeFaberN4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (32 * (4374 * (-3 * r ^ 2 + d) *
        (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
          3 * A * B * d - 3 * B * C))) * H ^ 2 -
        (314928 * (r * A + B) * A ^ 2) * H ^ 3) := by
  dsimp only
  let A : GCD369CubeHahnRegular k := T.Xn
  let d : GCD369CubeHahnRegular k := D.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let e : GCD369CubeHahnRegular k := D.cubicV - 2 * r ^ 3
  have hA : T.Xn = A := rfl
  have hY : T.Yn = r * A + B := by dsimp only [B]; ring
  have hZ : T.Zn = -2 * r ^ 2 * A + C := by dsimp only [C]; ring
  have hU : D.cubicU = -3 * r ^ 2 + d := by dsimp only [d]; ring
  have hV : D.cubicV = 2 * r ^ 3 + e := by dsimp only [e]; ring
  have hre : 3 * e + 2 * d * r = 0 := by
    dsimp only [e, d]
    linear_combination hroot
  have hrow1 := GCD369CubeDoubleBlowupRow1 A B C r d
  have hrow2 := GCD369CubeDoubleBlowupRow2 A B C r d e hre
  have hrow3 := GCD369CubeDoubleBlowupRow3 A B C r d e hre
  have hrow4 := GCD369CubeDoubleBlowupRow4 A B C r d e hre
  have h1 := T.zeroHighN1Expansion
  have h2 := T.zeroHighN2Expansion
  have h3 := T.zeroHighN3Expansion
  have h4 := T.zeroHighN4Expansion
  rw [monomial_eq_regularMonomial] at h1 h2 h3 h4
  rw [hA, hY, hZ, hU, hrow1] at h1
  rw [hA, hY, hZ, hU, hV, hrow2] at h2
  rw [hA, hY, hZ, hU, hV, hrow3] at h3
  rw [hA, hY, hZ, hU, hV, hrow4] at h4
  exact ⟨by simpa only [A, d, B, C, H] using h1,
    by simpa only [A, d, B, C, H] using h2,
    by simpa only [A, d, B, C, H] using h3,
    by simpa only [A, d, B, C, H] using h4⟩


/-- Below the weight-two load, after the weight-one parameter has vanished,
the first two exact moving-root row coefficients vanish at every
nonnegative residual exponent.  Unlike the three-row version, no upper
bound by `delta` is required. -/
theorem TransverseFactor.doubleRoot_row12Coeffs_zero_before_c7_coeff
    {k : Type*} [Field k] [CharZero k]
    {P : GCD369CubeHahnCommonCoefficientData k} (T : P.TransverseFactor)
    (hd : P.faber.d = 0)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * P.cubicU * r + 3 * P.cubicV = 0)
    (e : ℚ) (he : 0 ≤ e) (hearly : 2 * T.delta + e < 2 * P.faber.scale.p) :
    let A := T.Xn
    let D := P.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    ((A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.coeff e = 0) ∧
    ((2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C).1.coeff e = 0) := by
  dsimp only
  let A : GCD369CubeHahnRegular k := T.Xn
  let D : GCD369CubeHahnRegular k := P.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let R1 : GCD369CubeHahnRegular k :=
    A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
  let R2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * D - 3 * B * C
  let N1 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN1
      P.faber.scale.regular0 P.faber.scale.regular1
      P.faber.scale.regular2 P.faber.scale.regular3
      P.faber.scale.regular4
  let N2 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN2
      P.faber.scale.regular0 P.faber.scale.regular1
      P.faber.scale.regular2 P.faber.scale.regular3
      P.faber.scale.regular4
  have hz := P.faber.zeroHighNCoeff_zero_before_c7 hd
    (2 * T.delta + e) (by nlinarith [T.hdelta]) hearly
  have hexp := T.doubleRoot_zeroHigh_expansions_coeff r hroot
  have hexp1 : 729 * N1 = (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [N1, R1, A, D, B, C, H] using hexp.1
  have hexp2 : 2187 * N2 = (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [N2, R2, A, D, B, C, H] using hexp.2.1
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * (729 * R1)) T.delta e T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * (-1458 * R2)) T.delta e T.hdelta.le 2
  change ((-32 * (729 * R1)) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (-32 * (729 * R1)).1.coeff e at hshift1
  change ((32 * (-1458 * R2)) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (32 * (-1458 * R2)).1.coeff e at hshift2
  have hc1 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp1
  have hc2 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp2
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift1] at hc1
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift2] at hc2
  have hz1scaled : (-32 * (729 * R1)).1.coeff e = 0 := by
    calc
      _ = (729 * N1).1.coeff (e + 2 * T.delta) := hc1.symm
      _ = (729 * N1).1.coeff (2 * T.delta + e) := by
        rw [show e + 2 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := by simpa only [N1] using hz.1
  have hz2scaled : (32 * (-1458 * R2)).1.coeff e = 0 := by
    calc
      _ = (2187 * N2).1.coeff (e + 2 * T.delta) := hc2.symm
      _ = (2187 * N2).1.coeff (2 * T.delta + e) := by
        rw [show e + 2 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := by simpa only [N2] using hz.2.1
  have hscalar1 : -32 * (729 * R1) = (-23328 : ℤ) * R1 := by ring
  have hscalar2 : 32 * (-1458 * R2) = (-46656 : ℤ) * R2 := by ring
  rw [hscalar1, GCD369CubeHahnRegular.coeff_int_mul] at hz1scaled
  rw [hscalar2, GCD369CubeHahnRegular.coeff_int_mul] at hz2scaled
  have hR1zero : R1.1.coeff e = 0 :=
    (mul_eq_zero.mp hz1scaled).resolve_left (by norm_num)
  have hR2zero : R2.1.coeff e = 0 :=
    (mul_eq_zero.mp hz2scaled).resolve_left (by norm_num)
  exact ⟨by simpa only [R1, A, D, B, C] using hR1zero,
    by simpa only [R2, A, D, B, C] using hR2zero⟩

/-- Below the weight-two load, after the weight-one parameter has vanished,
the first three exact moving-root row coefficients vanish at every
nonnegative residual exponent strictly below `delta`. -/
theorem TransverseFactor.doubleRoot_row123Coeffs_zero_before_c7_coeff
    {k : Type*} [Field k] [CharZero k]
    {P : GCD369CubeHahnCommonCoefficientData k} (T : P.TransverseFactor)
    (hd : P.faber.d = 0)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * P.cubicU * r + 3 * P.cubicV = 0)
    (e : ℚ) (he : 0 ≤ e) (heDelta : e < T.delta)
    (hearly : 2 * T.delta + e < 2 * P.faber.scale.p) :
    let A := T.Xn
    let D := P.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    ((A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.coeff e = 0) ∧
    ((2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C).1.coeff e = 0) ∧
    ((-2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
        2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D +
        3 * C ^ 2).1.coeff e = 0) := by
  dsimp only
  let A : GCD369CubeHahnRegular k := T.Xn
  let D : GCD369CubeHahnRegular k := P.cubicU + 3 * r ^ 2
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
  let N1 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN1
      P.faber.scale.regular0 P.faber.scale.regular1
      P.faber.scale.regular2 P.faber.scale.regular3
      P.faber.scale.regular4
  let N2 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN2
      P.faber.scale.regular0 P.faber.scale.regular1
      P.faber.scale.regular2 P.faber.scale.regular3
      P.faber.scale.regular4
  let N3 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN3
      P.faber.scale.regular0 P.faber.scale.regular1
      P.faber.scale.regular2 P.faber.scale.regular3
      P.faber.scale.regular4
  have hz := P.faber.zeroHighNCoeff_zero_before_c7 hd
    (2 * T.delta + e) (by nlinarith [T.hdelta]) hearly
  have hexp := T.doubleRoot_zeroHigh_expansions_coeff r hroot
  have hexp1 : 729 * N1 = (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [N1, R1, A, D, B, C, H] using hexp.1
  have hexp2 : 2187 * N2 = (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [N2, R2, A, D, B, C, H] using hexp.2.1
  have hexp3 : N3 = (128 * R3) * H ^ 2 - (64 * A ^ 3) * H ^ 3 := by
    simpa only [N3, R3, A, D, B, C, H] using hexp.2.2.1
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * (729 * R1)) T.delta e T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * (-1458 * R2)) T.delta e T.hdelta.le 2
  have hshift3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (128 * R3) T.delta e T.hdelta.le 2
  change ((-32 * (729 * R1)) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (-32 * (729 * R1)).1.coeff e at hshift1
  change ((32 * (-1458 * R2)) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (32 * (-1458 * R2)).1.coeff e at hshift2
  change ((128 * R3) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (128 * R3).1.coeff e at hshift3
  have hc1 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp1
  have hc2 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp2
  have hc3 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp3
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift1] at hc1
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift2] at hc2
  have hcubicShift := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (64 * A ^ 3) T.delta (e - T.delta) T.hdelta.le 3
  change ((64 * A ^ 3) * H ^ 3).1.coeff
      ((e - T.delta) + (3 : ℚ) * T.delta) =
        (64 * A ^ 3).1.coeff (e - T.delta) at hcubicShift
  have hcubicZero : (64 * A ^ 3).1.coeff (e - T.delta) = 0 := by
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg (64 * A ^ 3)
      (sub_neg.mpr heDelta)
  change N3.1.coeff (2 * T.delta + e) =
    ((128 * R3) * H ^ 2).1.coeff (2 * T.delta + e) -
      ((64 * A ^ 3) * H ^ 3).1.coeff (2 * T.delta + e) at hc3
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift3] at hc3
  rw [show e + (2 : ℚ) * T.delta =
      (e - T.delta) + (3 : ℚ) * T.delta by ring,
    hcubicShift, hcubicZero, sub_zero] at hc3
  have hz1scaled : (-32 * (729 * R1)).1.coeff e = 0 := by
    calc
      _ = (729 * N1).1.coeff (e + 2 * T.delta) := hc1.symm
      _ = (729 * N1).1.coeff (2 * T.delta + e) := by
        rw [show e + 2 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := by simpa only [N1] using hz.1
  have hz2scaled : (32 * (-1458 * R2)).1.coeff e = 0 := by
    calc
      _ = (2187 * N2).1.coeff (e + 2 * T.delta) := hc2.symm
      _ = (2187 * N2).1.coeff (2 * T.delta + e) := by
        rw [show e + 2 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := by simpa only [N2] using hz.2.1
  have hz3N : N3.1.coeff (2 * T.delta + e) = 0 := by
    have hnat : (243 * N3).1.coeff (2 * T.delta + e) =
        (243 : k) * N3.1.coeff (2 * T.delta + e) :=
      GCD369CubeHahnRegular.coeff_nat_mul 243 N3 (2 * T.delta + e)
    have hscaled : (243 * N3).1.coeff (2 * T.delta + e) = 0 := by
      simpa only [N3] using hz.2.2.1
    rw [hnat] at hscaled
    exact (mul_eq_zero.mp hscaled).resolve_left (by norm_num)
  have hz3scaled : (128 * R3).1.coeff e = 0 := by
    calc
      _ = N3.1.coeff (e - T.delta + 3 * T.delta) := hc3.symm
      _ = N3.1.coeff (2 * T.delta + e) := by
        rw [show e - T.delta + 3 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := hz3N
  have hscalar1 : -32 * (729 * R1) = (-23328 : ℤ) * R1 := by
    ring
  have hscalar2 : 32 * (-1458 * R2) = (-46656 : ℤ) * R2 := by
    ring
  rw [hscalar1, GCD369CubeHahnRegular.coeff_int_mul] at hz1scaled
  rw [hscalar2, GCD369CubeHahnRegular.coeff_int_mul] at hz2scaled
  have hcoeff128 : (128 * R3).1.coeff e = (128 : k) * R3.1.coeff e :=
    GCD369CubeHahnRegular.coeff_nat_mul 128 R3 e
  rw [hcoeff128] at hz3scaled
  have hR1zero : R1.1.coeff e = 0 :=
    (mul_eq_zero.mp hz1scaled).resolve_left (by norm_num)
  have hR2zero : R2.1.coeff e = 0 :=
    (mul_eq_zero.mp hz2scaled).resolve_left (by norm_num)
  have hR3zero : R3.1.coeff e = 0 :=
    (mul_eq_zero.mp hz3scaled).resolve_left (by norm_num)
  exact ⟨by simpa only [R1, A, D, B, C] using hR1zero,
    by simpa only [R2, A, D, B, C] using hR2zero,
    by simpa only [R3, A, D, B, C] using hR3zero⟩

end GCD369CubeHahnCommonCoefficientData

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_zeroHigh_expansions_coeff
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_row12Coeffs_zero_before_c7_coeff
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_row123Coeffs_zero_before_c7_coeff
