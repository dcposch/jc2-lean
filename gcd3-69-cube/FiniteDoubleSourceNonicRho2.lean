import FiniteDoubleSource
import FiniteLaterSourceElimination

/-! # Source-value boundary at the moving double root before `rho2`

Once the weight-one, weight-two, weight-four, weight-five, weight-six,
weight-seven, and weight-eight loads have vanished and `rho1 = 0`, the
literal nonic source value still excludes the late double-root branch
below the weight-eleven `rho2` load.  The argument is the same
second-order residue as in the weight-one case, now evaluated at
`2 * delta` under the weaker cutoff `3 * delta ≤ 11 * p`.  Ninth-Faber
vanishing is the later-source identity below `9 * p`, which that cubic
cutoff supplies.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- The literal nonic source value excludes the late double-root branch as
soon as the sextic analysis supplies the two displayed order bounds, after
the weight-one, weight-two, weight-four, weight-five, weight-six,
weight-seven, and weight-eight loads have vanished, `rho1 = 0`, and
`3 * delta ≤ 11 * p`. -/
theorem TransverseFactor.doubleRoot_sourceNonic_inconsistent_of_orderBounds_before_rho2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hd : S.normal.d = 0)
    (hc7 : S.normal.c7 = 0)
    (hc5 : S.normal.c5 = 0)
    (hc4 : S.normal.c4 = 0)
    (hc3 : S.normal.c3 = 0)
    (hc2 : S.normal.c2 = 0)
    (hc1 : S.normal.c1 = 0)
    (hp : 3 * T.delta ≤ 11 * S.normal.sextic.scale.p)
    (hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop)
    (hphi : (↑(2 * T.delta) : WithTop ℚ) ≤
      S.transverseValue.1.orderTop) : False := by
  have hearly : 2 * T.delta < 9 * S.normal.sextic.scale.p := by
    have hp_pos : 0 < S.normal.sextic.scale.p := S.normal.sextic.scale.hp
    nlinarith [hp, hp_pos]
  have hz := S.normal.faberNineCoeff_zero_before_later
    hd hc7 hc5 hc4 hc3 hc2 hc1 (2 * T.delta) (by nlinarith [T.hdelta]) hearly
  have hc := T.faberNineCoeff_at_twoDelta_of_orderBounds hK hphi
  rw [hc] at hz
  simp only [map_mul, map_add, map_ofNat,
    GCD369CubeHahnRegular.constantCoeff_ratCast] at hz
  rw [hx, hX, hY] at hz
  have hscalar : algebraMap ℚ k (3 / 8) * A * (A * r + 2 * (r * A)) =
      algebraMap ℚ k (9 / 8) * r * A ^ 2 := by
    norm_num
    ring
  rw [hscalar] at hz
  have hn : algebraMap ℚ k (9 / 8) ≠ 0 := by norm_num
  exact (mul_ne_zero (mul_ne_zero hn hr) (pow_ne_zero 2 hA)) hz

/-- Once the moving cubic has order at least `delta`, the reduced ninth
Faber identity excludes the middle branch below `rho2`.  At exponent
`2 * delta` its explicit `E * H^2` term has nonzero residue, while the
cubic cube and cubic-times-sextic terms start later. -/
theorem TransverseFactor.sourceNinth_inconsistent_of_cubic_order_delta_before_rho2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hd : S.normal.d = 0)
    (hc7 : S.normal.c7 = 0)
    (hc5 : S.normal.c5 = 0)
    (hc4 : S.normal.c4 = 0)
    (hc3 : S.normal.c3 = 0)
    (hc2 : S.normal.c2 = 0)
    (hc1 : S.normal.c1 = 0)
    (hp : 3 * T.delta ≤ 11 * S.normal.sextic.scale.p)
    (hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop) : False := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let E : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
      (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)
  let P : GCD369CubeHahnRegular k :=
    S.normal.sextic.scale.weightedRegular 6 S.normal.sextic.value
  let F9 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
      S.normal.sextic.scale.regular0
      S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2
      S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      S.normal.sextic.regularX
  have hF9 : F9.1.coeff (2 * T.delta) = 0 :=
    S.normal.faberNineCoeff_zero_before_later hd hc7 hc5 hc4 hc3 hc2 hc1
      (2 * T.delta) (by nlinarith [T.hdelta])
      (by nlinarith [hp, T.hdelta, S.normal.sextic.scale.hp])
  have htwoF9 : (2 * F9).1.coeff (2 * T.delta) = 0 := by
    calc
      _ = (2 : k) * F9.1.coeff (2 * T.delta) :=
        GCD369CubeHahnRegular.coeff_nat_mul 2 F9 (2 * T.delta)
      _ = 0 := by rw [hF9, mul_zero]
  have hK2 : (↑(2 * T.delta) : WithTop ℚ) ≤
      (S.cubicValue * S.cubicValue).1.orderTop := by
    simpa only [show T.delta + T.delta = 2 * T.delta by ring] using
      GCD369CubeHahnRegular.mul_orderTop_lower
        S.cubicValue S.cubicValue T.delta T.delta hK hK
  have hK3 : (↑(3 * T.delta) : WithTop ℚ) ≤
      (S.cubicValue ^ 3).1.orderTop := by
    rw [show S.cubicValue ^ 3 =
      (S.cubicValue * S.cubicValue) * S.cubicValue by ring]
    simpa only [show 2 * T.delta + T.delta = 3 * T.delta by ring] using
      GCD369CubeHahnRegular.mul_orderTop_lower
        (S.cubicValue * S.cubicValue) S.cubicValue
        (2 * T.delta) T.delta hK2 hK
  have hK3zero : (S.cubicValue ^ 3).1.coeff (2 * T.delta) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr (by nlinarith [T.hdelta])).trans_le hK3)
  have hP : (↑(6 * S.normal.sextic.scale.p) : WithTop ℚ) ≤
      P.1.orderTop :=
    S.normal.sextic.scale.weightedRegular_orderTop_lower 6
      S.normal.sextic.value
  have hKP :
      (↑(T.delta + 6 * S.normal.sextic.scale.p) : WithTop ℚ) ≤
        (S.cubicValue * P).1.orderTop :=
    GCD369CubeHahnRegular.mul_orderTop_lower
      S.cubicValue P T.delta (6 * S.normal.sextic.scale.p) hK hP
  have hKPzero : (S.cubicValue * P).1.coeff (2 * T.delta) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr
        (by nlinarith [hp, S.normal.sextic.scale.hp])).trans_le hKP)
  have hthreeKP : (3 * S.cubicValue * P).1.coeff (2 * T.delta) = 0 := by
    have hassoc : (3 : GCD369CubeHahnRegular k) * S.cubicValue * P =
        3 * (S.cubicValue * P) := by ring
    rw [hassoc]
    calc
      _ = (3 : k) * (S.cubicValue * P).1.coeff (2 * T.delta) :=
        GCD369CubeHahnRegular.coeff_nat_mul 3 (S.cubicValue * P)
          (2 * T.delta)
      _ = 0 := by rw [hKPzero, mul_zero]
  have hEres : GCD369CubeHahnRegular.constantCoeff E =
      algebraMap ℚ k (9 / 8) * r * A ^ 2 := by
    dsimp only [E]
    simp only [map_mul, map_add, map_ofNat,
      GCD369CubeHahnRegular.constantCoeff_ratCast]
    rw [hx, hX, hY]
    norm_num
    ring
  have hEH2at := GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
    T.delta T.hdelta 2 E
  change (E * H ^ 2).1.coeff ((2 : ℚ) * T.delta) =
      GCD369CubeHahnRegular.constantCoeff E at hEH2at
  have hEH2 : (E * H ^ 2).1.coeff (2 * T.delta) =
      algebraMap ℚ k (9 / 8) * r * A ^ 2 := by
    norm_num at hEH2at
    exact hEH2at.trans hEres
  have htwoEH2 : (2 * E * H ^ 2).1.coeff (2 * T.delta) =
      2 * (algebraMap ℚ k (9 / 8) * r * A ^ 2) := by
    have hassoc : (2 : GCD369CubeHahnRegular k) * E * H ^ 2 =
        2 * (E * H ^ 2) := by ring
    rw [hassoc]
    calc
      _ = (2 : k) * (E * H ^ 2).1.coeff (2 * T.delta) :=
        GCD369CubeHahnRegular.coeff_nat_mul 2 (E * H ^ 2)
          (2 * T.delta)
      _ = _ := by rw [hEH2]
  have hid := T.twice_faberNine_reducedBySextic
  have hc := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta)) hid
  change (2 * F9).1.coeff (2 * T.delta) =
    (-(S.cubicValue ^ 3) + 2 * E * H ^ 2 +
      3 * S.cubicValue * P).1.coeff (2 * T.delta) at hc
  rw [htwoF9] at hc
  change 0 =
    ((-(S.cubicValue ^ 3) + 2 * E * H ^ 2).1 +
      (3 * S.cubicValue * P).1).coeff (2 * T.delta) at hc
  rw [HahnSeries.coeff_add, hthreeKP, add_zero] at hc
  change 0 = -(S.cubicValue ^ 3).1.coeff (2 * T.delta) +
      (2 * E * H ^ 2).1.coeff (2 * T.delta) at hc
  rw [hK3zero, htwoEH2, neg_zero, zero_add] at hc
  have hscalar : algebraMap ℚ k (9 / 8) ≠ 0 := by norm_num
  have hnonzero :
      (2 : k) * (algebraMap ℚ k (9 / 8) * r * A ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num)
      (mul_ne_zero (mul_ne_zero hscalar hr) (pow_ne_zero 2 hA))
  exact hnonzero hc.symm

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceNonic_inconsistent_of_orderBounds_before_rho2
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.sourceNinth_inconsistent_of_cubic_order_delta_before_rho2
