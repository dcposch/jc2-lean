import FiniteC5SourceElimination

/-! # Ninth-Faber vanishing below the first weight-five load

Once the weight-one, weight-two, and weight-four loads are identically
zero, the same higher-order quotient argument that killed every
positive-weight term below the first load applies up to the next first
load: below five times the Hahn scale, the ninth Faber value has zero
coefficient.  The intermediate weight-three `c6` term is multiplied by
the regular sextic, which already lives at weight six, so it vanishes in
the same quotient.  Clearing the sextic source equation then gives the
reduced cubic identity used to exclude an exact cubic order before that
load.
-/

noncomputable section

namespace GCD369CubeHahnNormalValueData

/-- Strictly below the weight-five load scale, and after the weight-one,
weight-two, and weight-four loads have already been killed, every remaining
positive-weight term in the complete normal form vanishes in the
higher-order quotient.  Hence the ninth Faber value has zero coefficient
at the selected exponent. -/
theorem faberNineCoeff_zero_before_c4
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnNormalValueData k)
    (hd : S.d = 0) (hc7 : S.c7 = 0) (hc5 : S.c5 = 0)
    (e : ℚ) (he : 0 ≤ e) (hearly : e < 5 * S.sextic.scale.p) :
    (GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
      S.sextic.scale.regular0 S.sextic.scale.regular1
      S.sextic.scale.regular2 S.sextic.scale.regular3
      S.sextic.scale.regular4 S.sextic.regularX).1.coeff e = 0 := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 5 ≤ w) :
      e < (w : ℚ) * S.sextic.scale.p := by
    calc
      e < (5 : ℚ) * S.sextic.scale.p := by simpa using hearly
      _ ≤ (w : ℚ) * S.sextic.scale.p := by
        exact mul_le_mul_of_nonneg_right
          (show (5 : ℚ) ≤ (w : ℚ) by exact_mod_cast hw)
          S.sextic.scale.hp.le
  have hkill (w : ℕ) (hw : 5 ≤ w)
      (x : GCD369CubeHahnRegular k) :
      q (S.sextic.scale.weightedRegular w x) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (↑e : WithTop ℚ) <
      (S.sextic.scale.weightedRegular w x).1.orderTop
    exact (WithTop.coe_lt_coe.mpr (hweight w hw)).trans_le
      (S.sextic.scale.weightedRegular_orderTop_lower w x)
  have hdq : q (S.sextic.scale.weightedRegular 1 S.d) = 0 := by
    have hzw : S.sextic.scale.weightedRegular 1 S.d = 0 := by
      apply Subtype.ext
      change S.sextic.scale.t ^ 1 * S.d.1 = 0
      rw [hd]
      simp
    rw [hzw, map_zero]
  have hc7q : q (S.sextic.scale.weightedRegular 2 S.c7) = 0 := by
    have hzw : S.sextic.scale.weightedRegular 2 S.c7 = 0 := by
      apply Subtype.ext
      change S.sextic.scale.t ^ 2 * S.c7.1 = 0
      rw [hc7]
      simp
    rw [hzw, map_zero]
  have hc5q : q (S.sextic.scale.weightedRegular 4 S.c5) = 0 := by
    have hzw : S.sextic.scale.weightedRegular 4 S.c5 = 0 := by
      apply Subtype.ext
      change S.sextic.scale.t ^ 4 * S.c5.1 = 0
      rw [hc5]
      simp
    rw [hzw, map_zero]
  have hc4 := hkill 5 (by norm_num) S.c4
  have hc3 := hkill 6 (by norm_num) S.c3
  have hc2 := hkill 7 (by norm_num) S.c2
  have hc1 := hkill 8 (by norm_num) S.c1
  have hc0 := hkill 9 (by norm_num) S.c0
  have hvalue := hkill 9 (by norm_num) S.value
  have hF6id :
      GCD369CubeFaberSixValueQ GCD369CubeHahnRegular.ratCast
        S.sextic.scale.regular0 S.sextic.scale.regular1
        S.sextic.scale.regular2 S.sextic.scale.regular3
        S.sextic.scale.regular4 S.sextic.regularX =
      S.sextic.scale.weightedRegular 6 S.sextic.value := by
    have hsub :
        S.sextic.regularX ^ 6 +
          (S.sextic.scale.regular4 * S.sextic.regularX ^ 4 +
            (S.sextic.scale.regular3 * S.sextic.regularX ^ 3 +
              (S.sextic.scale.regular2 * S.sextic.regularX ^ 2 +
                (S.sextic.scale.regular1 * S.sextic.regularX +
                  S.sextic.scale.regular0)))) =
        S.sextic.scale.weightedRegular 6 S.sextic.value := by
      apply Subtype.ext
      exact S.sextic.scaledEquation
    simp only [GCD369CubeFaberSixValueQ]
    convert hsub using 1
    ring
  have hF6map :
      GCD369CubeFaberSixValueQ
        (q.comp GCD369CubeHahnRegular.ratCast)
        (q S.sextic.scale.regular0) (q S.sextic.scale.regular1)
        (q S.sextic.scale.regular2) (q S.sextic.scale.regular3)
        (q S.sextic.scale.regular4) (q S.sextic.regularX) =
      q (GCD369CubeFaberSixValueQ GCD369CubeHahnRegular.ratCast
        S.sextic.scale.regular0 S.sextic.scale.regular1
        S.sextic.scale.regular2 S.sextic.scale.regular3
        S.sextic.scale.regular4 S.sextic.regularX) := by
    simp only [GCD369CubeFaberSixValueQ, map_add, map_mul, map_pow]
  have hF6q :
      GCD369CubeFaberSixValueQ
        (q.comp GCD369CubeHahnRegular.ratCast)
        (q S.sextic.scale.regular0) (q S.sextic.scale.regular1)
        (q S.sextic.scale.regular2) (q S.sextic.scale.regular3)
        (q S.sextic.scale.regular4) (q S.sextic.regularX) = 0 := by
    rw [hF6map, hF6id]
    exact hkill 6 (by norm_num) S.sextic.value
  have hmap := congrArg q S.heval
  rw [GCD369CubeFaberNormalValueQ_map] at hmap
  rw [hdq, hc7q, hc5q, hc4, hc3, hc2, hc1, hc0, hvalue] at hmap
  simp only [GCD369CubeFaberNormalValueQ, zero_mul, add_zero] at hmap
  rw [hF6q, mul_zero, add_zero] at hmap
  have hFaberMap : q
      (GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
        S.sextic.scale.regular0 S.sextic.scale.regular1
        S.sextic.scale.regular2 S.sextic.scale.regular3
        S.sextic.scale.regular4 S.sextic.regularX) =
      GCD369CubeFaberNineValueQ
        (q.comp GCD369CubeHahnRegular.ratCast)
        (q S.sextic.scale.regular0) (q S.sextic.scale.regular1)
        (q S.sextic.scale.regular2) (q S.sextic.scale.regular3)
        (q S.sextic.scale.regular4) (q S.sextic.regularX) := by
    simp only [GCD369CubeFaberNineValueQ, RingHom.comp_apply,
      map_add, map_sub, map_mul, map_pow]
  have hzero : q
      (GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
        S.sextic.scale.regular0 S.sextic.scale.regular1
        S.sextic.scale.regular2 S.sextic.scale.regular3
        S.sextic.scale.regular4 S.sextic.regularX) = 0 := by
    exact hFaberMap.trans hmap
  have hmem :
      GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
        S.sextic.scale.regular0 S.sextic.scale.regular1
        S.sextic.scale.regular2 S.sextic.scale.regular3
        S.sextic.scale.regular4 S.sextic.regularX ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop hmem

end GCD369CubeHahnNormalValueData

namespace GCD369CubeHahnCommonValueData

/-- Strictly below the weight-five load, after the weight-one, weight-two,
and weight-four loads have already been killed, the reduced ninth-Faber
expression has zero coefficient.  This version needs no exact-order
information about the transverse value. -/
theorem TransverseFactor.reducedFaberNineCoeff_zero_before_c4
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0) (hc7 : S.normal.c7 = 0)
    (hc5 : S.normal.c5 = 0)
    (e : ℚ) (he : 0 ≤ e) (hearly : e < 5 * S.normal.sextic.scale.p) :
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
    exact S.normal.faberNineCoeff_zero_before_c4 hd hc7 hc5 e he hearly
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
second-order ninth-Faber term starts strictly later than the cubic cube,
and that cube itself still lies below the weight-five load. -/
theorem TransverseFactor.reducedFaberNine_inconsistent_of_exact_cubic_order_before_c4
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0) (hc7 : S.normal.c7 = 0)
    (hc5 : S.normal.c5 = 0)
    (alpha beta : ℚ) (a : k)
    (halpha : 0 < alpha) (ha : a ≠ 0)
    (hK : S.cubicValue.1.orderTop = (↑alpha : WithTop ℚ))
    (hlcK : S.cubicValue.1.leadingCoeff = a)
    (hE :
      let E := GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
        (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)
      (↑beta : WithTop ℚ) ≤ E.1.orderTop)
    (hlater : 3 * alpha < 2 * T.delta + beta)
    (hearly : 3 * alpha < 5 * S.normal.sextic.scale.p) : False := by
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
  have hz := T.reducedFaberNineCoeff_zero_before_c4
    hd hc7 hc5 (3 * alpha) (by nlinarith [halpha]) hearly
  change (-(S.cubicValue ^ 3) + 2 * E * H ^ 2).1.coeff
    (3 * alpha) = 0 at hz
  change ((-(S.cubicValue ^ 3)).1 + (2 * E * H ^ 2).1).coeff
    (3 * alpha) = 0 at hz
  rw [HahnSeries.coeff_add, htwoEH2coeff, add_zero] at hz
  change -(S.cubicValue ^ 3).1.coeff (3 * alpha) = 0 at hz
  rw [hKcubeCoeff] at hz
  exact (pow_ne_zero 3 ha) (neg_eq_zero.mp hz)

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnNormalValueData.faberNineCoeff_zero_before_c4
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.reducedFaberNineCoeff_zero_before_c4
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.reducedFaberNine_inconsistent_of_exact_cubic_order_before_c4
