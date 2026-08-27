import FiniteDoubleLiftQuadratic

/-! # Eliminating the literal sextic value from the ninth Faber value

The common-normal sextic equation removes the mixed cubic--normal term in
the exact ninth-Faber expansion.  Clearing the single denominator leaves a
particularly useful source identity: below the first weight-one load, the
reduced cubic term and the explicit second-order Faber term have zero
coefficient without any separate order hypothesis on the transverse value.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Twice the exact ninth-Faber value after eliminating the transverse value
with the literal sextic source equation. -/
theorem TransverseFactor.twice_faberNine_reducedBySextic
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    let E := GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
      (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)
    2 * GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
        S.normal.sextic.scale.regular0
        S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2
        S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        S.normal.sextic.regularX =
      -(S.cubicValue ^ 3) + 2 * E * H ^ 2 +
        3 * S.cubicValue *
          S.normal.sextic.scale.weightedRegular 6 S.normal.sextic.value := by
  dsimp only
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let E : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
      (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)
  have hn := S.commonNormalEquation
  have hf := T.faberNineExactExpansion
  dsimp only [H, E] at hf ⊢
  have hthreeHalf :
      (2 : GCD369CubeHahnRegular k) *
          GCD369CubeHahnRegular.ratCast (3 / 2) = 3 := by
    calc
      _ = GCD369CubeHahnRegular.ratCast 2 *
          GCD369CubeHahnRegular.ratCast (3 / 2) := by rw [map_ofNat]
      _ = GCD369CubeHahnRegular.ratCast (2 * (3 / 2)) :=
        (map_mul _ _ _).symm
      _ = GCD369CubeHahnRegular.ratCast 3 := by norm_num
      _ = 3 := by rw [map_ofNat]
  rw [hf]
  linear_combination
    3 * S.cubicValue * hn +
      (S.cubicValue * S.transverseValue) * hthreeHalf

/-- Strictly below the weight-one load, the reduced ninth-Faber expression
has zero coefficient.  This version needs no exact-order information about
the transverse value. -/
theorem TransverseFactor.reducedFaberNineCoeff_zero_before_d
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (e : ℚ) (he : 0 ≤ e) (hearly : e < S.normal.sextic.scale.p) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    let E := GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
      (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)
    (-(S.cubicValue ^ 3) + 2 * E * H ^ 2).1.coeff e = 0 := by
  dsimp only
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
  have hF9 : F9.1.coeff e = 0 := by
    exact S.normal.faberNineCoeff_zero_before_d e he hearly
  have htwoF9 : (2 * F9).1.coeff e = 0 := by
    calc
      _ = (2 : k) * F9.1.coeff e :=
        GCD369CubeHahnRegular.coeff_nat_mul 2 F9 e
      _ = 0 := by rw [hF9, mul_zero]
  have hP : (↑(6 * S.normal.sextic.scale.p) : WithTop ℚ) ≤
      P.1.orderTop := by
    exact S.normal.sextic.scale.weightedRegular_orderTop_lower 6
      S.normal.sextic.value
  have hKPmem : S.cubicValue * P ∈
      GCD369CubeHahnRegular.higherOrderIdeal e he := by
    exact GCD369CubeHahnRegular.mul_mem_higherOrderIdeal_of_bounds
      S.cubicValue P 0 (6 * S.normal.sextic.scale.p) e he
      S.cubicValue.2 hP (by nlinarith [S.normal.sextic.scale.hp])
  have hthreeKPmem : 3 * S.cubicValue * P ∈
      GCD369CubeHahnRegular.higherOrderIdeal e he := by
    have hm : (3 : GCD369CubeHahnRegular k) *
        (S.cubicValue * P) ∈
        GCD369CubeHahnRegular.higherOrderIdeal e he :=
      (GCD369CubeHahnRegular.higherOrderIdeal e he).mul_mem_left _ hKPmem
    simpa only [mul_assoc] using hm
  have hthreeKP : (3 * S.cubicValue * P).1.coeff e = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hthreeKPmem
  have hid := T.twice_faberNine_reducedBySextic
  have hc := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff e) hid
  change (2 * F9).1.coeff e =
    (-(S.cubicValue ^ 3) + 2 * E * H ^ 2 +
      3 * S.cubicValue * P).1.coeff e at hc
  rw [htwoF9] at hc
  change 0 =
    ((-(S.cubicValue ^ 3) + 2 * E * H ^ 2).1 +
      (3 * S.cubicValue * P).1).coeff e at hc
  rw [HahnSeries.coeff_add, hthreeKP, add_zero] at hc
  exact hc.symm

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.twice_faberNine_reducedBySextic
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.reducedFaberNineCoeff_zero_before_d
