import FiniteC2SourceElimination

/-! # Ninth-Faber vanishing below the first weight-eight load

Once the weight-one, weight-two, weight-four, weight-five, weight-six, and
weight-seven loads are identically zero, the same higher-order quotient
argument that killed every remaining positive-weight term applies up to
the next first load: below eight times the Hahn scale, the ninth Faber
value has zero coefficient.  The intermediate weight-three `c6` term
multiplied by the regular sextic is itself a weight-nine term, so it
vanishes in the same quotient.  An exact cubic order below that load is
then excluded from the reduced ninth-Faber identity, using the exact
cubic order rather than a generic vanishing of the reduced expression
below `8 p`.  The resulting threshold covers the `c1` tied resonance
`3 * alpha = 6 * p`.
-/

noncomputable section

namespace GCD369CubeHahnNormalValueData

/-- Strictly below the weight-eight load scale, and after the weight-one,
weight-two, weight-four, weight-five, weight-six, and weight-seven loads
have already been killed, every remaining positive-weight term in the
complete normal form vanishes in the higher-order quotient.  Hence the
ninth Faber value has zero coefficient at the selected exponent. -/
theorem faberNineCoeff_zero_before_c1
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnNormalValueData k)
    (hd : S.d = 0) (hc7 : S.c7 = 0) (hc5 : S.c5 = 0) (hc4 : S.c4 = 0)
    (hc3 : S.c3 = 0) (hc2 : S.c2 = 0)
    (e : ℚ) (he : 0 ≤ e) (hearly : e < 8 * S.sextic.scale.p) :
    (GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
      S.sextic.scale.regular0 S.sextic.scale.regular1
      S.sextic.scale.regular2 S.sextic.scale.regular3
      S.sextic.scale.regular4 S.sextic.regularX).1.coeff e = 0 := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 8 ≤ w) :
      e < (w : ℚ) * S.sextic.scale.p := by
    calc
      e < (8 : ℚ) * S.sextic.scale.p := by simpa using hearly
      _ ≤ (w : ℚ) * S.sextic.scale.p := by
        exact mul_le_mul_of_nonneg_right
          (show (8 : ℚ) ≤ (w : ℚ) by exact_mod_cast hw)
          S.sextic.scale.hp.le
  have hkill (w : ℕ) (hw : 8 ≤ w)
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
  have hc4q : q (S.sextic.scale.weightedRegular 5 S.c4) = 0 := by
    have hzw : S.sextic.scale.weightedRegular 5 S.c4 = 0 := by
      apply Subtype.ext
      change S.sextic.scale.t ^ 5 * S.c4.1 = 0
      rw [hc4]
      simp
    rw [hzw, map_zero]
  have hc3q : q (S.sextic.scale.weightedRegular 6 S.c3) = 0 := by
    have hzw : S.sextic.scale.weightedRegular 6 S.c3 = 0 := by
      apply Subtype.ext
      change S.sextic.scale.t ^ 6 * S.c3.1 = 0
      rw [hc3]
      simp
    rw [hzw, map_zero]
  have hc2q : q (S.sextic.scale.weightedRegular 7 S.c2) = 0 := by
    have hzw : S.sextic.scale.weightedRegular 7 S.c2 = 0 := by
      apply Subtype.ext
      change S.sextic.scale.t ^ 7 * S.c2.1 = 0
      rw [hc2]
      simp
    rw [hzw, map_zero]
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
  have hc6F6 :
      S.sextic.scale.weightedRegular 3 S.c6 *
        GCD369CubeFaberSixValueQ GCD369CubeHahnRegular.ratCast
          S.sextic.scale.regular0 S.sextic.scale.regular1
          S.sextic.scale.regular2 S.sextic.scale.regular3
          S.sextic.scale.regular4 S.sextic.regularX =
      S.sextic.scale.weightedRegular 9 (S.c6 * S.sextic.value) := by
    rw [hF6id]
    apply Subtype.ext
    change (S.sextic.scale.t ^ 3 * S.c6.1) *
        (S.sextic.scale.t ^ 6 * S.sextic.value.1) =
      S.sextic.scale.t ^ 9 * (S.c6.1 * S.sextic.value.1)
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
  have hc6F6q :
      q (S.sextic.scale.weightedRegular 3 S.c6) *
        GCD369CubeFaberSixValueQ
          (q.comp GCD369CubeHahnRegular.ratCast)
          (q S.sextic.scale.regular0) (q S.sextic.scale.regular1)
          (q S.sextic.scale.regular2) (q S.sextic.scale.regular3)
          (q S.sextic.scale.regular4) (q S.sextic.regularX) = 0 := by
    rw [hF6map, ← map_mul, hc6F6]
    exact hkill 9 (by norm_num) (S.c6 * S.sextic.value)
  have hmap := congrArg q S.heval
  rw [GCD369CubeFaberNormalValueQ_map] at hmap
  rw [hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1, hc0, hvalue] at hmap
  simp only [GCD369CubeFaberNormalValueQ, zero_mul, add_zero] at hmap
  rw [hc6F6q, add_zero] at hmap
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

/-- A finite exact cubic order is impossible whenever the explicit
second-order ninth-Faber term starts strictly later than the cubic cube,
the mixed cubic--sextic remainder starts strictly later than that cube,
and the cube itself still lies below the weight-eight load. -/
theorem TransverseFactor.reducedFaberNine_inconsistent_of_exact_cubic_order_before_c1
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0) (hc7 : S.normal.c7 = 0)
    (hc5 : S.normal.c5 = 0) (hc4 : S.normal.c4 = 0)
    (hc3 : S.normal.c3 = 0) (hc2 : S.normal.c2 = 0)
    (alpha beta : ℚ) (a : k)
    (halpha : 0 < alpha) (ha : a ≠ 0)
    (hK : S.cubicValue.1.orderTop = (↑alpha : WithTop ℚ))
    (hlcK : S.cubicValue.1.leadingCoeff = a)
    (hE :
      let E := GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
        (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)
      (↑beta : WithTop ℚ) ≤ E.1.orderTop)
    (hlater : 3 * alpha < 2 * T.delta + beta)
    (hsexticLater : 3 * alpha < alpha + 6 * S.normal.sextic.scale.p)
    (hearly : 3 * alpha < 8 * S.normal.sextic.scale.p) : False := by
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
  have hF9 : F9.1.coeff (3 * alpha) = 0 :=
    S.normal.faberNineCoeff_zero_before_c1 hd hc7 hc5 hc4 hc3 hc2
      (3 * alpha) (by nlinarith [halpha]) hearly
  have htwoF9 : (2 * F9).1.coeff (3 * alpha) = 0 := by
    calc
      _ = (2 : k) * F9.1.coeff (3 * alpha) :=
        GCD369CubeHahnRegular.coeff_nat_mul 2 F9 (3 * alpha)
      _ = 0 := by rw [hF9, mul_zero]
  have hP : (↑(6 * S.normal.sextic.scale.p) : WithTop ℚ) ≤
      P.1.orderTop :=
    S.normal.sextic.scale.weightedRegular_orderTop_lower 6
      S.normal.sextic.value
  have hKP : (↑(alpha + 6 * S.normal.sextic.scale.p) : WithTop ℚ) ≤
      (S.cubicValue * P).1.orderTop :=
    GCD369CubeHahnRegular.mul_orderTop_lower
      S.cubicValue P alpha (6 * S.normal.sextic.scale.p)
      hK.ge hP
  have hKPlate : (↑(3 * alpha) : WithTop ℚ) <
      (S.cubicValue * P).1.orderTop :=
    (WithTop.coe_lt_coe.mpr hsexticLater).trans_le hKP
  have hKPcoeff : (S.cubicValue * P).1.coeff (3 * alpha) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hKPlate
  have hthreeKP : (3 * S.cubicValue * P).1.coeff (3 * alpha) = 0 := by
    have hassoc : (3 : GCD369CubeHahnRegular k) * S.cubicValue * P =
        3 * (S.cubicValue * P) := by ring
    rw [hassoc]
    calc
      _ = (3 : k) * (S.cubicValue * P).1.coeff (3 * alpha) :=
        GCD369CubeHahnRegular.coeff_nat_mul 3 (S.cubicValue * P)
          (3 * alpha)
      _ = 0 := by rw [hKPcoeff, mul_zero]
  have hid := T.twice_faberNine_reducedBySextic
  have hc := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (3 * alpha)) hid
  change (2 * F9).1.coeff (3 * alpha) =
    (-(S.cubicValue ^ 3) + 2 * E * H ^ 2 +
      3 * S.cubicValue * P).1.coeff (3 * alpha) at hc
  rw [htwoF9] at hc
  change 0 =
    ((-(S.cubicValue ^ 3) + 2 * E * H ^ 2).1 +
      (3 * S.cubicValue * P).1).coeff (3 * alpha) at hc
  rw [HahnSeries.coeff_add, hthreeKP, add_zero] at hc
  have hz : (-(S.cubicValue ^ 3) + 2 * E * H ^ 2).1.coeff
      (3 * alpha) = 0 := hc.symm
  change ((-(S.cubicValue ^ 3)).1 + (2 * E * H ^ 2).1).coeff
    (3 * alpha) = 0 at hz
  rw [HahnSeries.coeff_add, htwoEH2coeff, add_zero] at hz
  change -(S.cubicValue ^ 3).1.coeff (3 * alpha) = 0 at hz
  rw [hKcubeCoeff] at hz
  exact (pow_ne_zero 3 ha) (neg_eq_zero.mp hz)

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnNormalValueData.faberNineCoeff_zero_before_c1
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.reducedFaberNine_inconsistent_of_exact_cubic_order_before_c1
