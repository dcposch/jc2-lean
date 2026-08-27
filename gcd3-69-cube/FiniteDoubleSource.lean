import FiniteDoubleLoad

/-! # Source-value boundary at the moving double root

The four invariant rows leave one balanced second-blowup resonance.  The
literal source equations contain more information: below the weight-one
load scale, the complete nonic equation forces the ninth Faber value itself
to have zero coefficient.  This file first isolates that source-level fact;
the double-root expansion used to contradict it is developed below.
-/

noncomputable section

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Exact second-order common-normal expansion of the ninth Faber value.
The earlier source API retained the last term as an existential multiple of
`h^2`; its coefficient is in fact the simple expression
`(3/8) * X * (X*x + 2*Y)`, and there are no higher powers of `h`. -/
theorem GCD369CubeFaberNineCommonNormalExactQ
    {R : Type*} [CommRing R] (q : ℚ →+* R)
    (X Y Z u v h x : R) :
    GCD369CubeFaberNineValueQ q
        (v ^ 2 + h * Z) (2 * u * v + h * Y) (u ^ 2 + h * X)
        (2 * v) (2 * u) x =
      (x ^ 3 + u * x + v) ^ 3 +
        q (3 / 2) * (x ^ 3 + u * x + v) *
          (X * x ^ 2 + Y * x + Z) * h +
        q (3 / 8) * X * (X * x + 2 * Y) * h ^ 2 := by
  have qscale (a : ℚ) : q a = q (128 * a) * q (1 / 128) := by
    rw [← q.map_mul]
    congr 1
    ring
  have hunit : (128 : R) * q (1 / 128) = 1 := by
    rw [show (128 : R) = q 128 by exact (map_ofNat q 128).symm,
      ← q.map_mul]
    norm_num
  simp only [GCD369CubeFaberNineValueQ]
  rw [qscale (3 / 2), qscale (3 / 8), qscale (3 / 4),
    qscale (1 / 16), qscale (3 / 16), qscale (3 / 128),
    qscale (3 / 32)]
  norm_num
  rw [map_ofNat q 192, map_ofNat q 48, map_ofNat q 96,
    map_ofNat q 8, map_ofNat q 24, map_ofNat q 3, map_ofNat q 12]
  linear_combination
    ((u * x + v) *
      (u ^ 2 * x ^ 2 + 2 * u * v * x + 3 * u * x ^ 4 + v ^ 2 +
        3 * v * x ^ 3 + 3 * x ^ 6)) * hunit

namespace GCD369CubeHahnNormalValueData

/-- Strictly below the weight-one load scale, every positive-weight term in
the complete normal form vanishes in the higher-order quotient.  Hence the
ninth Faber value has zero coefficient at the selected exponent.  Unlike the
earlier row-extraction lemmas, this needs no assumption that the regular load
parameters are constant. -/
theorem faberNineCoeff_zero_before_d
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnNormalValueData k)
    (e : ℚ) (he : 0 ≤ e) (hearly : e < S.sextic.scale.p) :
    (GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
      S.sextic.scale.regular0 S.sextic.scale.regular1
      S.sextic.scale.regular2 S.sextic.scale.regular3
      S.sextic.scale.regular4 S.sextic.regularX).1.coeff e = 0 := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 1 ≤ w) :
      e < (w : ℚ) * S.sextic.scale.p := by
    calc
      e < (1 : ℚ) * S.sextic.scale.p := by simpa using hearly
      _ ≤ (w : ℚ) * S.sextic.scale.p := by
        exact mul_le_mul_of_nonneg_right
          (show (1 : ℚ) ≤ (w : ℚ) by exact_mod_cast hw)
          S.sextic.scale.hp.le
  have hkill (w : ℕ) (hw : 1 ≤ w)
      (x : GCD369CubeHahnRegular k) :
      q (S.sextic.scale.weightedRegular w x) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (↑e : WithTop ℚ) <
      (S.sextic.scale.weightedRegular w x).1.orderTop
    exact (WithTop.coe_lt_coe.mpr (hweight w hw)).trans_le
      (S.sextic.scale.weightedRegular_orderTop_lower w x)
  have hd := hkill 1 (by norm_num) S.d
  have hc7 := hkill 2 (by norm_num) S.c7
  have hc6 := hkill 3 (by norm_num) S.c6
  have hc5 := hkill 4 (by norm_num) S.c5
  have hc4 := hkill 5 (by norm_num) S.c4
  have hc3 := hkill 6 (by norm_num) S.c3
  have hc2 := hkill 7 (by norm_num) S.c2
  have hc1 := hkill 8 (by norm_num) S.c1
  have hc0 := hkill 9 (by norm_num) S.c0
  have hvalue := hkill 9 (by norm_num) S.value
  have hmap := congrArg q S.heval
  rw [GCD369CubeFaberNormalValueQ_map] at hmap
  rw [hd, hc7, hc6, hc5, hc4, hc3, hc2, hc1, hc0, hvalue] at hmap
  simp only [GCD369CubeFaberNormalValueQ, zero_mul, add_zero] at hmap
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

/-- Exact Hahn-local form of the second-order ninth-Faber expansion.  This
strengthens `TransverseFactor.faberNineExpansion` by identifying its
`H^2` coefficient and proving that there is no further polynomial term. -/
theorem TransverseFactor.faberNineExactExpansion
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
        S.normal.sextic.scale.regular0
        S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2
        S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        S.normal.sextic.regularX =
      S.cubicValue ^ 3 +
        GCD369CubeHahnRegular.ratCast (3 / 2) *
          S.cubicValue * S.transverseValue +
        GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
          (T.Xn * S.normal.sextic.regularX + 2 * T.Yn) * H ^ 2 := by
  dsimp only
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  have hexact := GCD369CubeFaberNineCommonNormalExactQ
    (R := GCD369CubeHahnRegular k)
    GCD369CubeHahnRegular.ratCast T.Xn T.Yn T.Zn
      S.cubicU S.cubicV H S.normal.sextic.regularX
  have ha0 : S.normal.sextic.scale.regular0 =
      S.cubicV ^ 2 + H * T.Zn := by
    rw [T.regular0_eq]
    ring
  have ha1 : S.normal.sextic.scale.regular1 =
      2 * S.cubicU * S.cubicV + H * T.Yn := by
    rw [T.regular1_eq]
    ring
  have ha2 : S.normal.sextic.scale.regular2 =
      S.cubicU ^ 2 + H * T.Xn := by
    rw [T.regular2_eq]
    ring
  rw [ha0, ha1, ha2, S.regular3_eq_two_cubicV,
    S.regular4_eq_two_cubicU]
  rw [T.transverseValue_eq]
  dsimp only [cubicValue, H] at hexact ⊢
  linear_combination hexact

/-- Once the moving cubic has order at least `delta` and the transverse
value has order at least `2*delta`, the coefficient at `2*delta` of the
ninth Faber value is exactly the residue of the universal second-order
term. -/
theorem TransverseFactor.faberNineCoeff_at_twoDelta_of_orderBounds
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop)
    (hphi : (↑(2 * T.delta) : WithTop ℚ) ≤
      S.transverseValue.1.orderTop) :
    (GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
      S.normal.sextic.scale.regular0
      S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2
      S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      S.normal.sextic.regularX).1.coeff (2 * T.delta) =
      GCD369CubeHahnRegular.constantCoeff
        (GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
          (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)) := by
  let e : ℚ := 2 * T.delta
  have he : 0 ≤ e := by
    dsimp only [e]
    nlinarith [T.hdelta]
  have hKsq : (↑(2 * T.delta) : WithTop ℚ) ≤
      (S.cubicValue * S.cubicValue).1.orderTop := by
    by_cases hz : S.cubicValue.1 = 0
    · simp [hz]
    change (↑(2 * T.delta) : WithTop ℚ) ≤
      (S.cubicValue.1 * S.cubicValue.1).orderTop
    rw [HahnSeries.orderTop_mul]
    have hadd := add_le_add hK hK
    rw [show 2 * T.delta = T.delta + T.delta by ring,
      WithTop.coe_add]
    exact hadd
  have hKcube_mem : S.cubicValue ^ 3 ∈
      GCD369CubeHahnRegular.higherOrderIdeal e he := by
    have hm := GCD369CubeHahnRegular.mul_mem_higherOrderIdeal_of_bounds
      S.cubicValue (S.cubicValue * S.cubicValue)
      T.delta (2 * T.delta) e he hK hKsq (by
        dsimp only [e]
        nlinarith [T.hdelta])
    simpa [pow_succ, mul_assoc] using hm
  have hKphi_mem : S.cubicValue * S.transverseValue ∈
      GCD369CubeHahnRegular.higherOrderIdeal e he :=
    GCD369CubeHahnRegular.mul_mem_higherOrderIdeal_of_bounds
      S.cubicValue S.transverseValue T.delta (2 * T.delta) e he
      hK hphi (by
        dsimp only [e]
        nlinarith [T.hdelta])
  have hKcube_coeff : (S.cubicValue ^ 3).1.coeff e = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hKcube_mem
  have hKphi_coeff :
      (GCD369CubeHahnRegular.ratCast (3 / 2) *
        S.cubicValue * S.transverseValue).1.coeff e = 0 := by
    have hscalar : GCD369CubeHahnRegular.ratCast (3 / 2) *
        (S.cubicValue * S.transverseValue) ∈
        GCD369CubeHahnRegular.higherOrderIdeal e he :=
      (GCD369CubeHahnRegular.higherOrderIdeal e he).mul_mem_left
        _ hKphi_mem
    simpa only [mul_assoc] using
      (HahnSeries.coeff_eq_zero_of_lt_orderTop hscalar)
  have hexp := T.faberNineExactExpansion
  have hcoeff := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff e) hexp
  change _ =
    (S.cubicValue ^ 3).1.coeff e +
      (GCD369CubeHahnRegular.ratCast (3 / 2) *
        S.cubicValue * S.transverseValue).1.coeff e +
      ((GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
        (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)) *
        (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2).1.coeff e
      at hcoeff
  have hlast := GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
    T.delta T.hdelta 2
      (GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
        (T.Xn * S.normal.sextic.regularX + 2 * T.Yn))
  change
    ((GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn *
      (T.Xn * S.normal.sextic.regularX + 2 * T.Yn)) *
      (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2).1.coeff
        (2 * T.delta) = _ at hlast
  rw [hKcube_coeff, hKphi_coeff, zero_add] at hcoeff
  dsimp only [e] at hcoeff
  rw [hlast] at hcoeff
  simpa only [zero_add] using hcoeff

/-- The literal nonic source value excludes the late double-root branch as
soon as the sextic analysis supplies the two displayed order bounds. -/
theorem TransverseFactor.doubleRoot_sourceNonic_inconsistent_of_orderBounds
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hearly : 2 * T.delta < S.normal.sextic.scale.p)
    (hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop)
    (hphi : (↑(2 * T.delta) : WithTop ℚ) ≤
      S.transverseValue.1.orderTop) : False := by
  have hz := S.normal.faberNineCoeff_zero_before_d
    (2 * T.delta) (by nlinarith [T.hdelta]) hearly
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

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeFaberNineCommonNormalExactQ
#print axioms GCD369CubeHahnNormalValueData.faberNineCoeff_zero_before_d
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.faberNineExactExpansion
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.faberNineCoeff_at_twoDelta_of_orderBounds
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_sourceNonic_inconsistent_of_orderBounds
