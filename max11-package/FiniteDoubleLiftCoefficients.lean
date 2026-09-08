import FiniteDoubleLiftRows
import FiniteEarlyNormal

/-! # Coefficients at the next double-root deviation scale

The exact moving-root rows factor by the common monomial supplied by
`TripleScale`.  These lemmas extract their linear leading coefficients.
-/

noncomputable section

namespace GCD369CubeHahnRegular

/-- Multiplication by a ground-field constant acts coefficientwise. -/
theorem coeff_constant_mul
    {k : Type*} [Field k] (c : k) (x : GCD369CubeHahnRegular k)
    (e : ℚ) :
    (constant c * x).1.coeff e = c * x.1.coeff e := by
  change (HahnSeries.C c * x.1).coeff e = _
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

/-- The first double-blowup row at the first common deviation scale is its
linearization; the quadratic `B^2` term occurs strictly later. -/
theorem doubleBlowupRow1_coeff_at_tripleScale
    {k : Type*} [Field k] [CharZero k]
    (A r D B C : GCD369CubeHahnRegular k)
    (J : TripleScale D B C) :
    (A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.coeff J.mu =
      constantCoeff A ^ 2 * constantCoeff J.Dn -
        2 * constantCoeff A * constantCoeff J.Bn * constantCoeff r -
        2 * constantCoeff A * constantCoeff J.Cn := by
  let mu : ℚ := J.mu
  let hmu : 0 < mu := J.hmu
  let Dn : GCD369CubeHahnRegular k := J.Dn
  let Bn : GCD369CubeHahnRegular k := J.Bn
  let Cn : GCD369CubeHahnRegular k := J.Cn
  let M : GCD369CubeHahnRegular k := monomial mu hmu.le
  let L : GCD369CubeHahnRegular k :=
    A ^ 2 * Dn - 2 * A * Bn * r - 2 * A * Cn
  have hD : D = M * Dn := by exact J.hD
  have hB : B = M * Bn := by exact J.hB
  have hC : C = M * Cn := by exact J.hC
  have hfac :
      A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C =
        M ^ 1 * L - M ^ 2 * Bn ^ 2 := by
    rw [hD, hB, hC]
    dsimp only [M, L]
    ring
  have hcoeff := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff mu) hfac
  change _ = (M ^ 1 * L).1.coeff mu -
    (M ^ 2 * Bn ^ 2).1.coeff mu at hcoeff
  have hlin := coeff_monomial_pow_mul_at mu hmu 1 L
  have hquad := coeff_monomial_pow_mul_of_lt mu hmu 1 2
    (by norm_num) (Bn ^ 2)
  norm_num at hlin hquad
  change (monomial mu hmu.le * L).1.coeff mu = constantCoeff L at hlin
  change ((monomial mu hmu.le) ^ 2 * Bn ^ 2).1.coeff mu = 0 at hquad
  simp only [pow_one] at hcoeff
  dsimp only [M] at hcoeff
  rw [hlin, hquad, sub_zero] at hcoeff
  simpa only [mu, Dn, Bn, Cn, L, map_sub, map_mul, map_pow, map_ofNat]
    using hcoeff

/-- The second double-blowup row has the displayed linear coefficient at the
same common scale; its two mixed deviation terms occur at twice that scale. -/
theorem doubleBlowupRow2_coeff_at_tripleScale
    {k : Type*} [Field k] [CharZero k]
    (A r D B C : GCD369CubeHahnRegular k)
    (J : TripleScale D B C) :
    (2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C).1.coeff J.mu =
      2 * constantCoeff A ^ 2 * constantCoeff r * constantCoeff J.Dn -
        3 * constantCoeff A * constantCoeff J.Bn * constantCoeff r ^ 2 -
        3 * constantCoeff A * constantCoeff J.Cn * constantCoeff r := by
  let mu : ℚ := J.mu
  let hmu : 0 < mu := J.hmu
  let Dn : GCD369CubeHahnRegular k := J.Dn
  let Bn : GCD369CubeHahnRegular k := J.Bn
  let Cn : GCD369CubeHahnRegular k := J.Cn
  let M : GCD369CubeHahnRegular k := monomial mu hmu.le
  let L : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * Dn - 3 * A * Bn * r ^ 2 - 3 * A * Cn * r
  let Q : GCD369CubeHahnRegular k :=
    3 * A * Bn * Dn - 3 * Bn * Cn
  have hD : D = M * Dn := by exact J.hD
  have hB : B = M * Bn := by exact J.hB
  have hC : C = M * Cn := by exact J.hC
  have hfac :
      2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
          3 * A * B * D - 3 * B * C =
        M ^ 1 * L + M ^ 2 * Q := by
    rw [hD, hB, hC]
    dsimp only [M, L, Q]
    ring
  have hcoeff := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff mu) hfac
  change _ = (M ^ 1 * L).1.coeff mu + (M ^ 2 * Q).1.coeff mu at hcoeff
  have hlin := coeff_monomial_pow_mul_at mu hmu 1 L
  have hquad := coeff_monomial_pow_mul_of_lt mu hmu 1 2
    (by norm_num) Q
  norm_num at hlin hquad
  change (monomial mu hmu.le * L).1.coeff mu = constantCoeff L at hlin
  change ((monomial mu hmu.le) ^ 2 * Q).1.coeff mu = 0 at hquad
  simp only [pow_one] at hcoeff
  dsimp only [M] at hcoeff
  rw [hlin, hquad, add_zero] at hcoeff
  simpa only [mu, Dn, Bn, Cn, L, map_sub, map_mul, map_pow, map_ofNat]
    using hcoeff

end GCD369CubeHahnRegular

namespace GCD369CubeHahnCommonValueData

/-- Vanishing of the first two Faber coefficients at the first common
deviation scale forces the linear kernel of the second blowup.  This theorem
is deliberately source-agnostic; a later wrapper supplies the two coefficient
vanishings from the literal source equations below the first load. -/
theorem TransverseFactor.doubleRoot_linearKernel_of_coeff_zero
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r : GCD369CubeHahnRegular k) (r0 A0 : k)
    (D B C : GCD369CubeHahnRegular k)
    (J : GCD369CubeHahnRegular.TripleScale D B C)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hA : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hD : D = S.cubicU + 3 * r ^ 2)
    (hB : B = T.Yn - r * T.Xn)
    (hC : C = T.Zn + 2 * r ^ 2 * T.Xn)
    (hz1 :
      (729 * GCD369CubeFaberN1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (2 * T.delta + J.mu) = 0)
    (hz2 :
      (2187 * GCD369CubeFaberN2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (2 * T.delta + J.mu) = 0) :
    GCD369CubeHahnRegular.constantCoeff J.Dn = 0 ∧
      GCD369CubeHahnRegular.constantCoeff J.Cn =
        -r0 * GCD369CubeHahnRegular.constantCoeff J.Bn := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let R1 : GCD369CubeHahnRegular k :=
    T.Xn ^ 2 * D - 2 * T.Xn * B * r - B ^ 2 - 2 * T.Xn * C
  let R2 : GCD369CubeHahnRegular k :=
    2 * T.Xn ^ 2 * r * D - 3 * T.Xn * B * r ^ 2 -
      3 * T.Xn * C * r + 3 * T.Xn * B * D - 3 * B * C
  have hexp := T.doubleRoot_zeroHigh_expansions r hroot
  have hexp1 :
      729 * GCD369CubeFaberN1
          S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
          S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
          S.normal.sextic.scale.regular4 =
        (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [R1, H, hD, hB, hC] using hexp.1
  have hexp2 :
      2187 * GCD369CubeFaberN2
          S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
          S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
          S.normal.sextic.scale.regular4 =
        (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [R2, H, hD, hB, hC] using hexp.2.1
  have hc1 := congrArg
    (fun z : GCD369CubeHahnRegular k =>
      z.1.coeff (2 * T.delta + J.mu)) hexp1
  have hc2 := congrArg
    (fun z : GCD369CubeHahnRegular k =>
      z.1.coeff (2 * T.delta + J.mu)) hexp2
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * (729 * R1)) T.delta J.mu T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * (-1458 * R2)) T.delta J.mu T.hdelta.le 2
  change ((-32 * (729 * R1)) * H ^ 2).1.coeff
      (J.mu + (2 : ℚ) * T.delta) =
        (-32 * (729 * R1)).1.coeff J.mu at hshift1
  change ((32 * (-1458 * R2)) * H ^ 2).1.coeff
      (J.mu + (2 : ℚ) * T.delta) =
        (32 * (-1458 * R2)).1.coeff J.mu at hshift2
  rw [show 2 * T.delta + J.mu = J.mu + (2 : ℚ) * T.delta by ring,
    hshift1] at hc1
  rw [show 2 * T.delta + J.mu = J.mu + (2 : ℚ) * T.delta by ring,
    hshift2] at hc2
  have hz1' :
      (729 * GCD369CubeFaberN1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (J.mu + (2 : ℚ) * T.delta) = 0 := by
    rw [show J.mu + (2 : ℚ) * T.delta = 2 * T.delta + J.mu by ring]
    exact hz1
  have hz2' :
      (2187 * GCD369CubeFaberN2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (J.mu + (2 : ℚ) * T.delta) = 0 := by
    rw [show J.mu + (2 : ℚ) * T.delta = 2 * T.delta + J.mu by ring]
    exact hz2
  rw [hz1'] at hc1
  rw [hz2'] at hc2
  have hR1 := GCD369CubeHahnRegular.doubleBlowupRow1_coeff_at_tripleScale
    T.Xn r D B C J
  have hR2 := GCD369CubeHahnRegular.doubleBlowupRow2_coeff_at_tripleScale
    T.Xn r D B C J
  have hc1zero := hc1.symm
  have hc2zero := hc2.symm
  change (-32 * (729 * R1)).1.coeff J.mu = 0 at hc1zero
  change (32 * (-1458 * R2)).1.coeff J.mu = 0 at hc2zero
  have h32 : (32 : GCD369CubeHahnRegular k) =
      GCD369CubeHahnRegular.constant (32 : k) := by
    apply Subtype.ext
    exact (map_ofNat (HahnSeries.C : k →+* HahnSeries ℚ k) 32).symm
  have h729 : (729 : GCD369CubeHahnRegular k) =
      GCD369CubeHahnRegular.constant (729 : k) := by
    apply Subtype.ext
    exact (map_ofNat (HahnSeries.C : k →+* HahnSeries ℚ k) 729).symm
  have h1458 : (1458 : GCD369CubeHahnRegular k) =
      GCD369CubeHahnRegular.constant (1458 : k) := by
    apply Subtype.ext
    exact (map_ofNat (HahnSeries.C : k →+* HahnSeries ℚ k) 1458).symm
  have hneg32 : (-32 : GCD369CubeHahnRegular k) =
      GCD369CubeHahnRegular.constant (-32 : k) := by
    rw [show (-32 : GCD369CubeHahnRegular k) =
      -(32 : GCD369CubeHahnRegular k) by rfl, h32, map_neg]
  have hneg1458 : (-1458 : GCD369CubeHahnRegular k) =
      GCD369CubeHahnRegular.constant (-1458 : k) := by
    rw [show (-1458 : GCD369CubeHahnRegular k) =
      -(1458 : GCD369CubeHahnRegular k) by rfl, h1458, map_neg]
  have hcoeff1 :
      (-32 * (729 * R1)).1.coeff J.mu =
        (-32 : k) * 729 * R1.1.coeff J.mu := by
    rw [hneg32, h729,
      GCD369CubeHahnRegular.coeff_constant_mul,
      GCD369CubeHahnRegular.coeff_constant_mul]
    ring
  have hcoeff2 :
      (32 * (-1458 * R2)).1.coeff J.mu =
        (32 : k) * (-1458) * R2.1.coeff J.mu := by
    rw [h32, hneg1458,
      GCD369CubeHahnRegular.coeff_constant_mul,
      GCD369CubeHahnRegular.coeff_constant_mul]
    ring
  rw [hcoeff1] at hc1zero
  rw [hcoeff2] at hc2zero
  let hc1' := hc1zero
  let hc2' := hc2zero
  rw [hR1, hA, hr] at hc1'
  rw [hR2, hA, hr] at hc2'
  have hlin1 :
      A0 ^ 2 * GCD369CubeHahnRegular.constantCoeff J.Dn -
        2 * A0 * GCD369CubeHahnRegular.constantCoeff J.Bn * r0 -
        2 * A0 * GCD369CubeHahnRegular.constantCoeff J.Cn = 0 := by
    have hc : ((-32 : k) * 729) *
        (A0 ^ 2 * GCD369CubeHahnRegular.constantCoeff J.Dn -
          2 * A0 * GCD369CubeHahnRegular.constantCoeff J.Bn * r0 -
          2 * A0 * GCD369CubeHahnRegular.constantCoeff J.Cn) = 0 := by
      simpa only [mul_assoc] using hc1'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num)
  have hlin2 :
      2 * A0 ^ 2 * r0 * GCD369CubeHahnRegular.constantCoeff J.Dn -
        3 * A0 * GCD369CubeHahnRegular.constantCoeff J.Bn * r0 ^ 2 -
        3 * A0 * GCD369CubeHahnRegular.constantCoeff J.Cn * r0 = 0 := by
    have hc : ((32 : k) * (-1458)) *
        (2 * A0 ^ 2 * r0 * GCD369CubeHahnRegular.constantCoeff J.Dn -
          3 * A0 * GCD369CubeHahnRegular.constantCoeff J.Bn * r0 ^ 2 -
          3 * A0 * GCD369CubeHahnRegular.constantCoeff J.Cn * r0) = 0 := by
      simpa only [mul_assoc] using hc2'
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num)
  exact GCD369CubeDoubleBlowup_linearKernel
    A0 (GCD369CubeHahnRegular.constantCoeff J.Bn)
    (GCD369CubeHahnRegular.constantCoeff J.Cn) r0
    (GCD369CubeHahnRegular.constantCoeff J.Dn) hA0 hr0 hlin1 hlin2

/-- Literal source wrapper for the preceding linear-kernel extraction.  If
`2*delta + mu` is still below the weight-one load, the complete first two
Faber equations provide exactly the two required zero coefficients. -/
theorem TransverseFactor.doubleRoot_linearKernel_before_d
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r : GCD369CubeHahnRegular k) (r0 A0 : k)
    (D B C : GCD369CubeHahnRegular k)
    (J : GCD369CubeHahnRegular.TripleScale D B C)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hA : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hD : D = S.cubicU + 3 * r ^ 2)
    (hB : B = T.Yn - r * T.Xn)
    (hC : C = T.Zn + 2 * r ^ 2 * T.Xn)
    (hearly : 2 * T.delta + J.mu < F.scale.p) :
    GCD369CubeHahnRegular.constantCoeff J.Dn = 0 ∧
      GCD369CubeHahnRegular.constantCoeff J.Cn =
        -r0 * GCD369CubeHahnRegular.constantCoeff J.Bn := by
  have he : 0 ≤ 2 * T.delta + J.mu := by
    nlinarith [T.hdelta, J.hmu]
  have hz := F.zeroHighNCoeff_zero_before_d
    D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    (2 * T.delta + J.mu) he hearly
  rw [← hscale] at hz
  exact T.doubleRoot_linearKernel_of_coeff_zero
    r r0 A0 D B C J hr hA hr0 hA0 hroot hD hB hC hz.1 hz.2.1

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnRegular.doubleBlowupRow1_coeff_at_tripleScale
#print axioms GCD369CubeHahnRegular.doubleBlowupRow2_coeff_at_tripleScale
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_linearKernel_of_coeff_zero
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_linearKernel_before_d
