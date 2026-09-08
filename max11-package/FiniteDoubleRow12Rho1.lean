import FiniteDoubleLoadSourceCoeff
import FiniteRho1EarlyNormal

/-! # The first two moving-root rows through the residual weight-ten scale

After the weight-one, weight-two, weight-four, weight-five, weight-six,
weight-seven, and weight-eight loads have vanished, the bundled three-row
coefficient theorem still stops before residual exponent `delta`, because
the intrinsic cubic enters the third row there.  The first two rows have
no such term.  This file records their coefficient range below ten times
the Hahn scale, together with the leading zero-load first-row residue.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Below the weight-ten load, after the weight-one, weight-two,
weight-four, weight-five, weight-six, weight-seven, and weight-eight
parameters have vanished, the first universal zero-load normal row
vanishes on the residue jet. -/
theorem TransverseFactor.doubleRoot_zeroLoad_row1Coeff_zero_before_rho1
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
    (hearly : 2 * T.delta < 10 * F.scale.p) :
    GCD369CubeNormalRow1
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u = 0 := by
  exact (T.zeroLoadLeadingRows_before_rho1 F hscale hd hc7 hc5 hc4 hc3 hc2 hc1
    hearly).1

/-- Below the weight-ten load, after the weight-one, weight-two,
weight-four, weight-five, weight-six, weight-seven, and weight-eight
parameters have vanished, the first two exact moving-root row coefficients
vanish at every nonnegative residual exponent.  Unlike the three-row
version, no upper bound by `delta` is required. -/
theorem TransverseFactor.doubleRoot_row12Coeffs_zero_before_rho1
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
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (e : ℚ) (he : 0 ≤ e) (hearly : e + 2 * T.delta < 10 * F.scale.p) :
    let A := T.Xn
    let D := S.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    ((A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.coeff e = 0) ∧
    ((2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C).1.coeff e = 0) := by
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
  have hz := F.zeroHighNCoeff_zero_before_rho1 hd hc7 hc5 hc4 hc3 hc2 hc1
    (e + 2 * T.delta) (by nlinarith [T.hdelta]) hearly
  rw [← hscale] at hz
  have hexp := T.doubleRoot_zeroHigh_expansions r hroot
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
  have hc1' := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (e + 2 * T.delta)) hexp1
  have hcoeff2 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (e + 2 * T.delta)) hexp2
  rw [show e + 2 * T.delta = e + (2 : ℚ) * T.delta by ring,
    hshift1] at hc1'
  rw [show e + 2 * T.delta = e + (2 : ℚ) * T.delta by ring,
    hshift2] at hcoeff2
  have hz1scaled : (-32 * (729 * R1)).1.coeff e = 0 := by
    calc
      _ = (729 * N1).1.coeff (e + 2 * T.delta) := hc1'.symm
      _ = 0 := by simpa only [N1] using hz.1
  have hz2scaled : (32 * (-1458 * R2)).1.coeff e = 0 := by
    calc
      _ = (2187 * N2).1.coeff (e + 2 * T.delta) := hcoeff2.symm
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

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_zeroLoad_row1Coeff_zero_before_rho1
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_row12Coeffs_zero_before_rho1
