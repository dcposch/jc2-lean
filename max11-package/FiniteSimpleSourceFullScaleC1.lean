import FiniteDoubleRow12C1
import FiniteC1CubicN3

/-! # The full-scale simple-root obstruction before the weight-eight load

When `F.d = F.c7 = F.c5 = F.c4 = F.c3 = F.c2 = 0` and `3 * delta < 8 * p`, the first two primitive moving-root
rows still vanish at residual exponent `delta`.  In full-scale coordinates
their linear parts force the residue of the moving cubic correction to
vanish.  The primitive third row at `3 * delta` then contains only the
intrinsic `-64 * A^3` term.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Full-scale simple-root coordinates are impossible strictly before the
weight-eight load, once the weight-one, weight-two, weight-four, weight-five,
weight-six, and weight-seven parameters have vanished. -/
theorem TransverseFactor.simpleRoot_strictLate_inconsistent_of_fullScale_before_c1
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
    (hp : 3 * T.delta < 8 * F.scale.p)
    (r d b C2 : GCD369CubeHahnRegular k) (r0 A0 : k)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hr0 : r0 ≠ 0)
    (hA : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hA0 : A0 ≠ 0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hD : S.cubicU + 3 * r ^ 2 =
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * d)
    (hB : T.Yn - r * T.Xn =
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * b)
    (hC : T.Zn + 2 * r ^ 2 * T.Xn =
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * (-r * b + C2)) :
    False := by
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
  have hrows := T.doubleRoot_row12Coeffs_zero_before_c1 F hscale
    hd hc7 hc5 hc4 hc3 hc2 r hroot T.delta T.hdelta.le (by nlinarith [hp, T.hdelta])
  have hR1zero : R1.1.coeff T.delta = 0 := by
    simpa only [R1, A, D, B, C] using hrows.1
  have hR2zero : R2.1.coeff T.delta = 0 := by
    simpa only [R2, A, D, B, C] using hrows.2
  let L1 : GCD369CubeHahnRegular k := A ^ 2 * d - 2 * A * C2
  let L2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * d - 3 * A * r * C2
  let Q2 : GCD369CubeHahnRegular k :=
    3 * A * b * d + 3 * r * b ^ 2 - 3 * b * C2
  have hR1fac : R1 = H * L1 - H ^ 2 * b ^ 2 := by
    dsimp only [R1, L1, A, D, B, C, H]
    rw [hD, hB, hC]
    ring
  have hR2fac : R2 = H * L2 + H ^ 2 * Q2 := by
    dsimp only [R2, L2, Q2, A, D, B, C, H]
    rw [hD, hB, hC]
    ring
  have hL1coeff := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
    T.delta T.hdelta 1 L1
  have hL2coeff := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
    T.delta T.hdelta 1 L2
  have hquad1 := GCD369CubeHahnRegular.coeff_monomial_pow_mul_of_lt
    T.delta T.hdelta 1 2 (by norm_num) (b ^ 2)
  have hquad2 := GCD369CubeHahnRegular.coeff_monomial_pow_mul_of_lt
    T.delta T.hdelta 1 2 (by norm_num) Q2
  have heq1 : A0 ^ 2 * GCD369CubeHahnRegular.constantCoeff d -
      2 * A0 * GCD369CubeHahnRegular.constantCoeff C2 = 0 := by
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff T.delta) hR1fac
    change R1.1.coeff T.delta =
      (H * L1).1.coeff T.delta - (H ^ 2 * b ^ 2).1.coeff T.delta at hc
    have hL1coeff' : (H * L1).1.coeff T.delta =
        GCD369CubeHahnRegular.constantCoeff L1 := by
      simpa only [H, pow_one, Nat.cast_one, one_mul] using hL1coeff
    have hquad1' : (H ^ 2 * b ^ 2).1.coeff T.delta = 0 := by
      simpa only [H, Nat.cast_one, one_mul] using hquad1
    rw [hR1zero, hL1coeff', hquad1', sub_zero] at hc
    simpa only [L1, map_sub, map_mul, map_pow, map_ofNat, A, hA] using hc.symm
  have heq2 : 2 * A0 ^ 2 * r0 * GCD369CubeHahnRegular.constantCoeff d -
      3 * A0 * r0 * GCD369CubeHahnRegular.constantCoeff C2 = 0 := by
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff T.delta) hR2fac
    change R2.1.coeff T.delta =
      (H * L2).1.coeff T.delta + (H ^ 2 * Q2).1.coeff T.delta at hc
    have hL2coeff' : (H * L2).1.coeff T.delta =
        GCD369CubeHahnRegular.constantCoeff L2 := by
      simpa only [H, pow_one, Nat.cast_one, one_mul] using hL2coeff
    have hquad2' : (H ^ 2 * Q2).1.coeff T.delta = 0 := by
      simpa only [H, Nat.cast_one, one_mul] using hquad2
    rw [hR2zero, hL2coeff', hquad2', add_zero] at hc
    simpa only [L2, map_sub, map_mul, map_pow, map_ofNat, A, hA, hr]
      using hc.symm
  have hdresProd : A0 ^ 2 * r0 *
      GCD369CubeHahnRegular.constantCoeff d = 0 := by
    linear_combination 2 * heq2 - 3 * r0 * heq1
  have hdres : GCD369CubeHahnRegular.constantCoeff d = 0 := by
    exact (mul_eq_zero.mp hdresProd).resolve_left
      (mul_ne_zero (pow_ne_zero 2 hA0) hr0)
  let R3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D + 3 * C ^ 2
  let P3 : GCD369CubeHahnRegular k :=
    6 * b ^ 2 * r ^ 2 + 2 * A ^ 2 * d ^ 2 - 2 * H * b ^ 2 * d -
      4 * A * (-r * b + C2) * d + 3 * (-r * b + C2) ^ 2
  have hR3fac : R3 = H * (-2 * A ^ 2 * r ^ 2 * d) + H ^ 2 * P3 := by
    dsimp only [R3, P3, A, D, B, C, H]
    rw [hD, hB, hC]
    ring
  have hlin3 := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
    T.delta T.hdelta 1 (-2 * A ^ 2 * r ^ 2 * d)
  have hquad3 := GCD369CubeHahnRegular.coeff_monomial_pow_mul_of_lt
    T.delta T.hdelta 1 2 (by norm_num) P3
  have hR3zero : R3.1.coeff T.delta = 0 := by
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff T.delta) hR3fac
    change R3.1.coeff T.delta =
      (H * (-2 * A ^ 2 * r ^ 2 * d)).1.coeff T.delta +
        (H ^ 2 * P3).1.coeff T.delta at hc
    have hlin3' : (H * (-2 * A ^ 2 * r ^ 2 * d)).1.coeff T.delta =
        GCD369CubeHahnRegular.constantCoeff (-2 * A ^ 2 * r ^ 2 * d) := by
      simpa only [H, pow_one, Nat.cast_one, one_mul] using hlin3
    have hquad3' : (H ^ 2 * P3).1.coeff T.delta = 0 := by
      simpa only [H, Nat.cast_one, one_mul] using hquad3
    rw [hlin3', hquad3'] at hc
    simpa only [add_zero, map_neg, map_mul, map_pow, map_ofNat, A, hA, hr,
      hdres, mul_zero] using hc
  let N3 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  have hexp := T.doubleRoot_zeroHigh_expansions r hroot
  have hrow : N3 = (128 * R3) * H ^ 2 - (64 * A ^ 3) * H ^ 3 := by
    simpa only [N3, R3, A, D, B, C, H] using hexp.2.2.1
  have hc := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (3 * T.delta)) hrow
  have hrem := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (128 * R3) T.delta T.delta T.hdelta.le 2
  have hrem' : ((128 * R3) * H ^ 2).1.coeff (3 * T.delta) =
      (128 * R3).1.coeff T.delta := by
    simpa only [H, Nat.cast_ofNat,
      show T.delta + (2 : ℚ) * T.delta = 3 * T.delta by ring] using hrem
  have h128R3zero : (128 * R3).1.coeff T.delta = 0 := by
    calc
      (128 * R3).1.coeff T.delta = (128 : k) * R3.1.coeff T.delta := by
        simpa using GCD369CubeHahnRegular.coeff_int_mul
          (k := k) (128 : ℤ) R3 T.delta
      _ = 0 := by rw [hR3zero, mul_zero]
  have hcubic := GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
    T.delta T.hdelta 3 (64 * A ^ 3)
  change ((64 * A ^ 3) * H ^ 3).1.coeff (3 * T.delta) =
      GCD369CubeHahnRegular.constantCoeff (64 * A ^ 3) at hcubic
  have hn3 : N3.1.coeff (3 * T.delta) = -64 * A0 ^ 3 := by
    change N3.1.coeff (3 * T.delta) =
      ((128 * R3) * H ^ 2).1.coeff (3 * T.delta) -
        ((64 * A ^ 3) * H ^ 3).1.coeff (3 * T.delta) at hc
    rw [hrem', h128R3zero, hcubic] at hc
    simp only [zero_sub, map_mul, map_pow, map_ofNat, A, hA] at hc
    convert hc using 1 <;> ring
  have hz := T.zeroHighN3Coeff_zero_at_cubic_before_c1 F hscale hd hc7 hc5 hc4 hc3 hc2 hp
  have hz' : N3.1.coeff (3 * T.delta) = 0 := by
    simpa only [N3] using hz
  have hbad : (-64 : k) * A0 ^ 3 = 0 := by
    calc
      (-64 : k) * A0 ^ 3 = N3.1.coeff (3 * T.delta) := hn3.symm
      _ = 0 := hz'
  exact (mul_ne_zero (by norm_num) (pow_ne_zero 3 hA0)) hbad

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_strictLate_inconsistent_of_fullScale_before_c1
