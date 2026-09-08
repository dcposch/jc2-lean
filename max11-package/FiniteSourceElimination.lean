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

/-- A finite exact cubic order is impossible whenever the explicit
second-order ninth-Faber term starts strictly later than the cubic cube.
This is the abstract coefficient contradiction used by the simple-root
chart before its final resonance. -/
theorem TransverseFactor.reducedFaberNine_inconsistent_of_exact_cubic_order
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (alpha beta : ℚ) (a : k)
    (halpha : 0 < alpha) (ha : a ≠ 0)
    (hK : S.cubicValue.1.orderTop = (↑alpha : WithTop ℚ))
    (hlcK : S.cubicValue.1.leadingCoeff = a)
    (hE :
      let E := GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
        (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)
      (↑beta : WithTop ℚ) ≤ E.1.orderTop)
    (hlater : 3 * alpha < 2 * T.delta + beta)
    (hearly : 3 * alpha < S.normal.sextic.scale.p) : False := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let E : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
      (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)
  change (↑beta : WithTop ℚ) ≤ E.1.orderTop at hE
  have hK2 := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    S.cubicValue S.cubicValue alpha alpha hK hK
  have hK2order : (S.cubicValue * S.cubicValue).1.orderTop =
      (↑(2 * alpha) : WithTop ℚ) := by
    simpa only [show alpha + alpha = 2 * alpha by ring] using hK2.1
  have hK3 := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    (S.cubicValue * S.cubicValue) S.cubicValue
    (2 * alpha) alpha hK2order hK
  have hKcubeEq : S.cubicValue ^ 3 =
      (S.cubicValue * S.cubicValue) * S.cubicValue := by ring
  have hKcubeOrder : (S.cubicValue ^ 3).1.orderTop =
      (↑(3 * alpha) : WithTop ℚ) := by
    rw [hKcubeEq]
    simpa only [show 2 * alpha + alpha = 3 * alpha by ring] using hK3.1
  have hKcubeCoeff : (S.cubicValue ^ 3).1.coeff (3 * alpha) = a ^ 3 := by
    rw [GCD369CubeHahnRegular.coeff_eq_leadingCoeff_of_orderTop_eq
      (S.cubicValue ^ 3) (3 * alpha) hKcubeOrder]
    rw [hKcubeEq, hK3.2, hK2.2, hlcK]
    ring
  have hH := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) T.delta T.hdelta.le
  have hH2 := GCD369CubeHahnRegular.mul_orderTop_lower
    H H T.delta T.delta
    (by simpa only [H] using hH.1.ge)
    (by simpa only [H] using hH.1.ge)
  have hH2' : (↑(2 * T.delta) : WithTop ℚ) ≤ (H ^ 2).1.orderTop := by
    rw [pow_two]
    simpa only [show T.delta + T.delta = 2 * T.delta by ring] using hH2
  have hEH2 : (↑(beta + 2 * T.delta) : WithTop ℚ) ≤
      (E * H ^ 2).1.orderTop :=
    GCD369CubeHahnRegular.mul_orderTop_lower
      E (H ^ 2) beta (2 * T.delta) hE hH2'
  have hEH2late : (↑(3 * alpha) : WithTop ℚ) <
      (E * H ^ 2).1.orderTop := by
    exact (WithTop.coe_lt_coe.mpr (by linarith [hlater])).trans_le hEH2
  have hEH2coeff : (E * H ^ 2).1.coeff (3 * alpha) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hEH2late
  have htwoEH2coeff : (2 * E * H ^ 2).1.coeff (3 * alpha) = 0 := by
    have hassoc : (2 : GCD369CubeHahnRegular k) * E * H ^ 2 =
        2 * (E * H ^ 2) := by ring
    rw [hassoc]
    calc
      _ = (2 : k) * (E * H ^ 2).1.coeff (3 * alpha) :=
        GCD369CubeHahnRegular.coeff_nat_mul 2 (E * H ^ 2) (3 * alpha)
      _ = 0 := by rw [hEH2coeff, mul_zero]
  have hz := T.reducedFaberNineCoeff_zero_before_d
    (3 * alpha) (by nlinarith [halpha]) hearly
  change (-(S.cubicValue ^ 3) + 2 * E * H ^ 2).1.coeff
    (3 * alpha) = 0 at hz
  change ((-(S.cubicValue ^ 3)).1 + (2 * E * H ^ 2).1).coeff
    (3 * alpha) = 0 at hz
  rw [HahnSeries.coeff_add, htwoEH2coeff, add_zero] at hz
  change -(S.cubicValue ^ 3).1.coeff (3 * alpha) = 0 at hz
  rw [hKcubeCoeff] at hz
  exact (pow_ne_zero 3 ha) (neg_eq_zero.mp hz)

/-- If the square of the moving cubic is the unique lowest term in the
literal sextic equation, its finite order cannot lie below the source
boundary. -/
theorem TransverseFactor.sourceSextic_inconsistent_of_cubic_dominant
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (_T : S.TransverseFactor)
    (alpha beta : ℚ)
    (hK : S.cubicValue.1.orderTop = (↑alpha : WithTop ℚ))
    (hphi : (↑beta : WithTop ℚ) ≤
      S.transverseValue.1.orderTop)
    (hdominant : 2 * alpha < beta)
    (hbelow : 2 * alpha < 6 * S.normal.sextic.scale.p) : False := by
  have hK2 := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    S.cubicValue S.cubicValue alpha alpha hK hK
  have hKsq : (S.cubicValue ^ 2).1.orderTop =
      (↑(2 * alpha) : WithTop ℚ) := by
    rw [pow_two]
    simpa only [show alpha + alpha = 2 * alpha by ring] using hK2.1
  have hord : (S.cubicValue ^ 2).1.orderTop <
      S.transverseValue.1.orderTop := by
    rw [hKsq]
    exact (WithTop.coe_lt_coe.mpr hdominant).trans_le hphi
  have hsum : (S.cubicValue ^ 2 + S.transverseValue).1.orderTop =
      (↑(2 * alpha) : WithTop ℚ) := by
    change (S.cubicValue.1 ^ 2 + S.transverseValue.1).orderTop = _
    have hord' : (S.cubicValue.1 ^ 2).orderTop <
        S.transverseValue.1.orderTop := by simpa using hord
    rw [HahnSeries.orderTop_add_eq_left hord']
    simpa using hKsq
  have hs := S.commonNormalEquation_orderTop_lower
  rw [hsum, WithTop.coe_le_coe] at hs
  linarith

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.twice_faberNine_reducedBySextic
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.reducedFaberNineCoeff_zero_before_d
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.reducedFaberNine_inconsistent_of_exact_cubic_order
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.sourceSextic_inconsistent_of_cubic_dominant
