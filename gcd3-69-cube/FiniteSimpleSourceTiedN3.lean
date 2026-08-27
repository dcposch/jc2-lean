import FiniteSimpleSourceTiedChart
import FiniteDoubleHahn

/-! # The tied third-row obstruction after the second lift

At the resonance `p = 3 * delta`, the complete source equations still make
the primitive zero-high third coefficient vanish.  If the moving-root cubic
and corrected transverse remainders have acquired a second copy of the
`delta` monomial, the exact third-row expansion has only its intrinsic
`-64 * A^3` coefficient left.  A nonzero transverse residue therefore gives
an immediate contradiction.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- The tied third row is inconsistent once the second moving-root lift has
promoted `d` and the corrected transverse remainder `C2` by one further
copy of the full-scale monomial. -/
theorem TransverseFactor.simpleRoot_tied_N3_inconsistent_of_secondLift
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hp : F.scale.p = 3 * T.delta)
    (r d b C2 : GCD369CubeHahnRegular k) (A0 : k)
    (hA : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hA0 : A0 ≠ 0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hD : S.cubicU + 3 * r ^ 2 =
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * d)
    (hB : T.Yn - r * T.Xn =
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * b)
    (hC : T.Zn + 2 * r ^ 2 * T.Xn =
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * (-r * b + C2))
    (hd : (↑T.delta : WithTop ℚ) ≤ d.1.orderTop)
    (hC2 : (↑T.delta : WithTop ℚ) ≤ C2.1.orderTop) : False := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let d2 : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift d T.delta hd
  let c3 : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift C2 T.delta hC2
  have hd2 : H * d2 = d := by
    simpa only [H, d2] using
      GCD369CubeHahnRegular.monomial_mul_shift
        d T.delta T.hdelta.le hd
  have hc3 : H * c3 = C2 := by
    simpa only [H, c3] using
      GCD369CubeHahnRegular.monomial_mul_shift
        C2 T.delta T.hdelta.le hC2
  let A : GCD369CubeHahnRegular k := T.Xn
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let R3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D + 3 * C ^ 2
  let P : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * d2 + 6 * b ^ 2 * r ^ 2 +
      2 * A ^ 2 * H ^ 2 * d2 ^ 2 - 2 * H ^ 2 * b ^ 2 * d2 -
      4 * A * H * (-r * b + H * c3) * d2 +
      3 * (-r * b + H * c3) ^ 2
  have hR3fac : R3 = H ^ 2 * P := by
    dsimp only [R3, P, D, B, C, A]
    rw [hD, hB, hC, ← hd2, ← hc3]
    dsimp only [H]
    ring
  have hR3zero : R3.1.coeff T.delta = 0 := by
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff T.delta) hR3fac
    have hlate := GCD369CubeHahnRegular.coeff_monomial_pow_mul_of_lt
      T.delta T.hdelta 1 2 (by norm_num) P
    change R3.1.coeff T.delta = (H ^ 2 * P).1.coeff T.delta at hc
    have hlate' : (H ^ 2 * P).1.coeff T.delta = 0 := by
      simpa only [H, Nat.cast_one, one_mul] using hlate
    exact hc.trans hlate'
  have h128R3zero : (128 * R3).1.coeff T.delta = 0 := by
    calc
      (128 * R3).1.coeff T.delta = (128 : k) * R3.1.coeff T.delta := by
        simpa using GCD369CubeHahnRegular.coeff_int_mul
          (k := k) (128 : ℤ) R3 T.delta
      _ = 0 := by rw [hR3zero, mul_zero]
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
  have hXA : GCD369CubeHahnRegular.constantCoeff T.Xn ≠ 0 := by
    rw [hA]
    exact hA0
  let TS : S.TransverseScale :=
    { delta := T.delta
      hdelta := T.hdelta
      Xn := T.Xn
      Yn := T.Yn
      Zn := T.Zn
      hnormal2 := T.hnormal2
      hnormal1 := T.hnormal1
      hnormal0 := T.hnormal0
      hleading := Or.inl hXA }
  have hearly : 2 * TS.delta < F.scale.p := by
    dsimp only [TS]
    rw [hp]
    linarith [T.hdelta]
  have hz := TS.zeroHighN3Coeff_zero_at_cubic_before_d F hscale hearly
  have hz' : N3.1.coeff (3 * T.delta) = 0 := by
    simpa only [TS, N3] using hz
  have hbad : (-64 : k) * A0 ^ 3 = 0 := by
    calc
      (-64 : k) * A0 ^ 3 = N3.1.coeff (3 * T.delta) := hn3.symm
      _ = 0 := hz'
  exact (mul_ne_zero (by norm_num) (pow_ne_zero 3 hA0)) hbad

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_tied_N3_inconsistent_of_secondLift
