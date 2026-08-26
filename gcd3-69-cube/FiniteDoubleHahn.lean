import FiniteDoubleNormal
import FiniteValueOrders

/-! # The third Faber row before the first active load

The third full Faber row has a useful extra vanishing property near the
common-cubic sheet: every high-parameter term contains at least one exact
normal coordinate.  Thus, if the first transverse scale is `delta` and
`2 * delta < p`, all high-parameter terms vanish through exponent
`3 * delta`, even when the weight-one parameter itself enters before that
exponent.  This is the source-level separation needed by the double-root
cubic obstruction.
-/

noncomputable section

namespace GCD369CubeHahnRegular

/-- Multiplying a regular Hahn series by the monomial of exponent `delta`
raises its order to at least `delta`. -/
theorem monomial_mul_orderTop_lower
    {k : Type*} [Field k]
    (delta : ℚ) (hdelta : 0 ≤ delta) (x : GCD369CubeHahnRegular k) :
    (↑delta : WithTop ℚ) ≤ (monomial delta hdelta * x).1.orderTop := by
  change (↑delta : WithTop ℚ) ≤
    (HahnSeries.single delta (1 : k) * x.1).orderTop
  by_cases hx : x.1 = 0
  · simp [hx]
  have hm : HahnSeries.single delta (1 : k) ≠ 0 := by simp
  rw [HahnSeries.orderTop_mul,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hm,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hx]
  change (↑delta : WithTop ℚ) ≤
    (↑((HahnSeries.single delta (1 : k)).order + x.1.order) : WithTop ℚ)
  rw [WithTop.coe_le_coe]
  have hmorder : (HahnSeries.single delta (1 : k)).order = delta := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hm,
      HahnSeries.orderTop_single one_ne_zero]
  have hx0 : (0 : ℚ) ≤ x.1.order :=
    HahnSeries.zero_le_orderTop_iff.mp x.2
  rw [hmorder]
  linarith

/-- Two lower order bounds whose sum is beyond `e` put the product in the
strict higher-order ideal at `e`. -/
theorem mul_mem_higherOrderIdeal_of_bounds
    {k : Type*} [Field k]
    (x y : GCD369CubeHahnRegular k) (a b e : ℚ) (he : 0 ≤ e)
    (ha : (↑a : WithTop ℚ) ≤ x.1.orderTop)
    (hb : (↑b : WithTop ℚ) ≤ y.1.orderTop)
    (hab : e < a + b) :
    x * y ∈ higherOrderIdeal e he := by
  change (↑e : WithTop ℚ) < (x.1 * y.1).orderTop
  by_cases hx : x.1 = 0
  · simp [hx]
  by_cases hy : y.1 = 0
  · simp [hy]
  rw [HahnSeries.orderTop_mul,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hx,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hy]
  change (↑e : WithTop ℚ) < ↑(x.1.order + y.1.order)
  rw [WithTop.coe_lt_coe]
  have hax : a ≤ x.1.order := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hx,
      WithTop.coe_le_coe] at ha
    exact ha
  have hby : b ≤ y.1.order := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hy,
      WithTop.coe_le_coe] at hb
    exact hb
  linarith

end GCD369CubeHahnRegular

set_option maxRecDepth 10000 in
/-- In any quotient where every high parameter annihilates all three
normal coordinates, the full third Faber numerator is its zero-high part.
This exact identity is the algebraic reason that high loads cannot alter the
first double-normal cubic obstruction. -/
theorem GCD369CubeFaberFullN3_eq_zeroHigh_of_load_annihilates_normals
    {R : Type*} [CommRing R]
    (X Y Z U V d c7 c5 c4 c3 c2 c1 : R)
    (hd : d * X = 0 ∧ d * Y = 0 ∧ d * Z = 0)
    (h7 : c7 * X = 0 ∧ c7 * Y = 0 ∧ c7 * Z = 0)
    (h5 : c5 * X = 0 ∧ c5 * Y = 0 ∧ c5 * Z = 0)
    (h4 : c4 * X = 0 ∧ c4 * Y = 0 ∧ c4 * Z = 0)
    (h3 : c3 * X = 0 ∧ c3 * Y = 0 ∧ c3 * Z = 0)
    (h2 : c2 * X = 0 ∧ c2 * Y = 0 ∧ c2 * Z = 0)
    (h1 : c1 * X = 0 ∧ c1 * Y = 0 ∧ c1 * Z = 0) :
    GCD369CubeFaberFullN3
        (V ^ 2 + Z) (2 * U * V + Y) (U ^ 2 + X) (2 * V) (2 * U)
        d c7 c5 c4 c3 c2 c1 =
      243 * GCD369CubeFaberN3
        (V ^ 2 + Z) (2 * U * V + Y) (U ^ 2 + X) (2 * V) (2 * U) := by
  rcases hd with ⟨hdX, hdY, _hdZ⟩
  rcases h7 with ⟨h7X, h7Y, _h7Z⟩
  rcases h5 with ⟨h5X, h5Y, _h5Z⟩
  rcases h4 with ⟨h4X, h4Y, _h4Z⟩
  rcases h3 with ⟨h3X, _h3Y, h3Z⟩
  rcases h2 with ⟨_h2X, h2Y, _h2Z⟩
  rcases h1 with ⟨h1X, _h1Y, _h1Z⟩
  simp only [GCD369CubeFaberN3]
  linear_combination
    (24576 * U ^ 2 * V - 73728 * X * V - 110592 * Y * U) * hdX +
    (-36864 * V ^ 2 + 4096 * U ^ 3 + 110592 * Z) * hdY +
    (-32256 * V ^ 2 - 32256 * U * X + 7168 * U ^ 3 + 48384 * Z) * h7X +
    (-32256 * U * V + 24192 * Y) * h7Y +
    (23040 * U ^ 2 - 17280 * X) * h5X - 69120 * V * h5Y -
    110592 * V * h4X - 55296 * U * h4Y - 82944 * U * h3X +
    124416 * h3Z + 82944 * h2Y + 41472 * h1X

/-- The primitive third zero-high numerator commutes with ring maps. -/
theorem GCD369CubeFaberN3_map
    {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (a0 a1 a2 a3 a4 : R) :
    f (GCD369CubeFaberN3 a0 a1 a2 a3 a4) =
      GCD369CubeFaberN3 (f a0) (f a1) (f a2) (f a3) (f a4) := by
  simp only [GCD369CubeFaberN3, map_add, map_sub, map_mul, map_pow,
    map_ofNat]

namespace GCD369CubeHahnCommonValueData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Before the half-`d` scale, the coefficient of the primitive zero-high
third row at the cubic transverse exponent is zero.  Unlike the earlier
quadratic extraction, this remains true even when `3 * delta ≥ p`: every
high-parameter term gains one additional normal factor. -/
theorem TransverseScale.zeroHighN3Coeff_zero_at_cubic_before_d
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hearly : 2 * T.delta < F.scale.p) :
    (GCD369CubeFaberN3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff (3 * T.delta) = 0 := by
  let e : ℚ := 3 * T.delta
  have he : 0 ≤ e := by
    dsimp only [e]
    nlinarith [T.hdelta]
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hn2 : (↑T.delta : WithTop ℚ) ≤ S.normal2.1.orderTop := by
    rw [T.hnormal2]
    exact GCD369CubeHahnRegular.monomial_mul_orderTop_lower
      T.delta T.hdelta.le T.Xn
  have hn1 : (↑T.delta : WithTop ℚ) ≤ S.normal1.1.orderTop := by
    rw [T.hnormal1]
    exact GCD369CubeHahnRegular.monomial_mul_orderTop_lower
      T.delta T.hdelta.le T.Yn
  have hn0 : (↑T.delta : WithTop ℚ) ≤ S.normal0.1.orderTop := by
    rw [T.hnormal0]
    exact GCD369CubeHahnRegular.monomial_mul_orderTop_lower
      T.delta T.hdelta.le T.Zn
  have hpw (w : ℕ) (hw : 1 ≤ w) :
      F.scale.p ≤ (w : ℚ) * F.scale.p := by
    have hwq : (1 : ℚ) ≤ (w : ℚ) := by exact_mod_cast hw
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hwq F.scale.hp.le
  have hann (w : ℕ) (hw : 1 ≤ w) (x : GCD369CubeHahnRegular k) :
      q (F.scale.weightedRegular w x) * q S.normal2 = 0 ∧
      q (F.scale.weightedRegular w x) * q S.normal1 = 0 ∧
      q (F.scale.weightedRegular w x) * q S.normal0 = 0 := by
    have hcut : e < (w : ℚ) * F.scale.p + T.delta := by
      dsimp only [e]
      have := hpw w hw
      linarith
    constructor
    · rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact GCD369CubeHahnRegular.mul_mem_higherOrderIdeal_of_bounds
        (F.scale.weightedRegular w x) S.normal2
        ((w : ℚ) * F.scale.p) T.delta e he
        (F.scale.weightedRegular_orderTop_lower w x) hn2 hcut
    constructor
    · rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact GCD369CubeHahnRegular.mul_mem_higherOrderIdeal_of_bounds
        (F.scale.weightedRegular w x) S.normal1
        ((w : ℚ) * F.scale.p) T.delta e he
        (F.scale.weightedRegular_orderTop_lower w x) hn1 hcut
    · rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact GCD369CubeHahnRegular.mul_mem_higherOrderIdeal_of_bounds
        (F.scale.weightedRegular w x) S.normal0
        ((w : ℚ) * F.scale.p) T.delta e he
        (F.scale.weightedRegular_orderTop_lower w x) hn0 hcut
  have hd := hann 1 (by norm_num) F.d
  have h7 := hann 2 (by norm_num) F.c7
  have h5 := hann 4 (by norm_num) F.c5
  have h4 := hann 5 (by norm_num) F.c4
  have h3 := hann 6 (by norm_num) F.c3
  have h2 := hann 7 (by norm_num) F.c2
  have h1 := hann 8 (by norm_num) F.c1
  have ha2 : S.normal.sextic.scale.regular2 = S.cubicU ^ 2 + S.normal2 := by
    dsimp only [normal2]
    ring
  have ha1 : S.normal.sextic.scale.regular1 =
      2 * S.cubicU * S.cubicV + S.normal1 := by
    dsimp only [normal1]
    ring
  have ha0 : S.normal.sextic.scale.regular0 = S.cubicV ^ 2 + S.normal0 := by
    dsimp only [normal0]
    ring
  let full := GCD369CubeFaberFullN3
    S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
    S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
    S.normal.sextic.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let zeroThird := 243 * GCD369CubeFaberN3
    S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
    S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
    S.normal.sextic.scale.regular4
  have hmapZeroThird : q zeroThird =
      243 * GCD369CubeFaberN3
        (q S.normal.sextic.scale.regular0)
        (q S.normal.sextic.scale.regular1)
        (q S.normal.sextic.scale.regular2)
        (q S.normal.sextic.scale.regular3)
        (q S.normal.sextic.scale.regular4) := by
    dsimp only [zeroThird]
    rw [map_mul, map_ofNat, GCD369CubeFaberN3_map]
  have hqfull_zeroThird : q full = q zeroThird := by
    dsimp only [full]
    rw [ha0, ha1, ha2, S.regular3_eq_two_cubicV,
      S.regular4_eq_two_cubicU,
      (GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.2.1]
    rw [hmapZeroThird, ha0, ha1, ha2, S.regular3_eq_two_cubicV,
      S.regular4_eq_two_cubicU]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    exact GCD369CubeFaberFullN3_eq_zeroHigh_of_load_annihilates_normals
      (q S.normal2) (q S.normal1) (q S.normal0)
      (q S.cubicU) (q S.cubicV)
      (q (F.scale.weightedRegular 1 F.d))
      (q (F.scale.weightedRegular 2 F.c7))
      (q (F.scale.weightedRegular 4 F.c5))
      (q (F.scale.weightedRegular 5 F.c4))
      (q (F.scale.weightedRegular 6 F.c3))
      (q (F.scale.weightedRegular 7 F.c2))
      (q (F.scale.weightedRegular 8 F.c1))
      hd h7 h5 h4 h3 h2 h1
  have hrho3q : q (F.scale.weightedRegular 12 F.rho3) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (↑e : WithTop ℚ) <
      (F.scale.weightedRegular 12 F.rho3).1.orderTop
    apply (WithTop.coe_lt_coe.mpr (show e < (12 : ℚ) * F.scale.p by
      dsimp only [e]
      nlinarith [F.scale.hp])).trans_le
    exact F.scale.weightedRegular_orderTop_lower 12 F.rho3
  have hqfull_zero : q full = 0 := by
    have hscaled : full = 248832 * F.scale.weightedRegular 12 F.rho3 := by
      dsimp only [full]
      rw [hscale]
      apply Subtype.ext
      exact F.scaledFullN3
    rw [hscaled, map_mul, hrho3q, mul_zero]
  have hqzeroThird_zero : q zeroThird = 0 :=
    hqfull_zeroThird.symm.trans hqfull_zero
  have hzeroThird_mem : zeroThird ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp hqzeroThird_zero
  have hzscaled : zeroThird.1.coeff e = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hzeroThird_mem
  dsimp only [zeroThird, e] at hzscaled
  let N := GCD369CubeFaberN3
    S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
    S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
    S.normal.sextic.scale.regular4
  have hnum : (243 : GCD369CubeHahnRegular k) =
      GCD369CubeHahnRegular.constant (243 : k) := by
    apply Subtype.ext
    exact (map_ofNat (HahnSeries.C : k →+* HahnSeries ℚ k) 243).symm
  change (243 * N).1.coeff (3 * T.delta) = 0 at hzscaled
  rw [hnum] at hzscaled
  change (HahnSeries.C (243 : k) * N.1).coeff (3 * T.delta) = 0 at hzscaled
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul] at hzscaled
  exact (mul_eq_zero.mp hzscaled).resolve_left (by norm_num)

/-- If the full normalized Hahn jet follows a moving double-root radical,
the third zero-high row is exactly its cubic remainder.  Here `r` and `A`
are themselves arbitrary regular Hahn series, so this statement already
allows all tangent corrections absorbed by the moving double root. -/
theorem TransverseFactor.zeroHighN3Expansion_of_doubleRadical
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r A : GCD369CubeHahnRegular k)
    (hX : T.Xn = A)
    (hY : T.Yn = r * A)
    (hZ : T.Zn = -2 * r ^ 2 * A)
    (hu : S.cubicU = -3 * r ^ 2)
    (hv : S.cubicV = 2 * r ^ 3) :
    GCD369CubeFaberN3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4 =
      (-64 * A ^ 3) *
        (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 3 := by
  rw [T.zeroHighN3Expansion, hX, hY, hZ, hu, hv]
  have hrow : GCD369CubeNormalRow3 A (r * A) (-2 * r ^ 2 * A)
      (-3 * r ^ 2) (2 * r ^ 3) = 0 := by
    dsimp only [GCD369CubeNormalRow3]
    ring
  rw [hrow]
  ring

/-- Coefficient form of the exact moving-double-radical identity. -/
theorem TransverseFactor.zeroHighN3Coeff_of_doubleRadical
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r A : GCD369CubeHahnRegular k)
    (hX : T.Xn = A)
    (hY : T.Yn = r * A)
    (hZ : T.Zn = -2 * r ^ 2 * A)
    (hu : S.cubicU = -3 * r ^ 2)
    (hv : S.cubicV = 2 * r ^ 3) :
    (GCD369CubeFaberN3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff (3 * T.delta) =
      -64 * GCD369CubeHahnRegular.constantCoeff A ^ 3 := by
  have h := congrArg
    (fun x : GCD369CubeHahnRegular k => x.1.coeff (3 * T.delta))
    (T.zeroHighN3Expansion_of_doubleRadical r A hX hY hZ hu hv)
  change _ =
    ((-64 * A ^ 3) *
      (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 3).1.coeff
        (((3 : ℕ) : ℚ) * T.delta) at h
  change _ = -64 * GCD369CubeHahnRegular.constantCoeff A ^ 3
  rw [GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
    T.delta T.hdelta 3] at h
  simpa only [map_neg, map_mul, map_pow, map_ofNat] using h

/-- The moving-double-radical cubic coefficient is nonzero whenever its
amplitude has nonzero residue. -/
theorem TransverseFactor.zeroHighN3Coeff_of_doubleRadical_ne_zero
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r A : GCD369CubeHahnRegular k)
    (hX : T.Xn = A)
    (hY : T.Yn = r * A)
    (hZ : T.Zn = -2 * r ^ 2 * A)
    (hu : S.cubicU = -3 * r ^ 2)
    (hv : S.cubicV = 2 * r ^ 3)
    (hA : GCD369CubeHahnRegular.constantCoeff A ≠ 0) :
    (GCD369CubeFaberN3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff (3 * T.delta) ≠ 0 := by
  rw [T.zeroHighN3Coeff_of_doubleRadical r A hX hY hZ hu hv]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hA)

/-- An exact moving double-root radical cannot occur as a nonzero
transverse branch strictly before the half-`d` scale.  The remaining lifting
problem is therefore precisely to promote the successive zero-load jets to
this exact Hahn-series factorization. -/
theorem TransverseScale.exact_doubleRadical_not_before_d
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hearly : 2 * T.delta < F.scale.p)
    (r A : GCD369CubeHahnRegular k)
    (hX : T.factor.Xn = A)
    (hY : T.factor.Yn = r * A)
    (hZ : T.factor.Zn = -2 * r ^ 2 * A)
    (hu : S.cubicU = -3 * r ^ 2)
    (hv : S.cubicV = 2 * r ^ 3)
    (hA : GCD369CubeHahnRegular.constantCoeff A ≠ 0) : False := by
  have hz := T.zeroHighN3Coeff_zero_at_cubic_before_d F hscale hearly
  have hn := T.factor.zeroHighN3Coeff_of_doubleRadical_ne_zero
    r A hX hY hZ hu hv hA
  exact hn hz

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnRegular.monomial_mul_orderTop_lower
#print axioms GCD369CubeHahnRegular.mul_mem_higherOrderIdeal_of_bounds
#print axioms GCD369CubeFaberFullN3_eq_zeroHigh_of_load_annihilates_normals
#print axioms GCD369CubeFaberN3_map
#print axioms GCD369CubeHahnCommonValueData.TransverseScale.zeroHighN3Coeff_zero_at_cubic_before_d
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.zeroHighN3Expansion_of_doubleRadical
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.zeroHighN3Coeff_of_doubleRadical
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.zeroHighN3Coeff_of_doubleRadical_ne_zero
#print axioms GCD369CubeHahnCommonValueData.TransverseScale.exact_doubleRadical_not_before_d
