import FiniteCommonSource

/-! # First active Faber loads at a finite common-cubic pole

The normal coordinates have already been factored at a prescribed positive
Hahn scale.  This file begins the source-facing active-load bridge by proving
that a weight-one `d` constant, scaled to the square of that monomial, gives
exactly the four arbitrary-`d` Kuranishi rows used by the audited algebraic
exclusion.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnRegular

theorem coeff_monomial_sq_constant_mul
    {k : Type*} [Field k] (delta : ℚ) (hdelta : 0 < delta)
    (D : k) (P : GCD369CubeHahnRegular k) :
    ((monomial delta hdelta.le) ^ 2 * constant D * P).1.coeff
        (((2 : ℕ) : ℚ) * delta) =
      D * constantCoeff P := by
  rw [mul_assoc, coeff_monomial_pow_mul_at delta hdelta 2]
  simp

/-- Coefficients commute with multiplication by a natural scalar in the
regular Hahn local ring. -/
theorem coeff_nat_mul
    {k : Type*} [Field k] (n : ℕ) (x : GCD369CubeHahnRegular k)
    (e : ℚ) :
    (n * x).1.coeff e = (n : k) * x.1.coeff e := by
  change (HahnSeries.single 0 (n : k) * x.1).coeff e = _
  rw [HahnSeries.coeff_single_zero_mul]

/-- Regular Hahn series vanishing strictly beyond a fixed nonnegative
exponent form an ideal. -/
def higherOrderIdeal
    {k : Type*} [Field k] (e : ℚ) (_he : 0 ≤ e) :
    Ideal (GCD369CubeHahnRegular k) where
  carrier := {x | (↑e : WithTop ℚ) < x.1.orderTop}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact (lt_min hx hy).trans_le
      (HahnSeries.min_orderTop_le_orderTop_add (x := x.1) (y := y.1))
  smul_mem' := by
    intro c x hx
    change (↑e : WithTop ℚ) < x.1.orderTop at hx
    change (↑e : WithTop ℚ) < (c.1 * x.1).orderTop
    by_cases hc : c.1 = 0
    · simp [hc]
    by_cases hx0 : x.1 = 0
    · simp [hx0]
    rw [HahnSeries.orderTop_mul]
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hc,
      ← HahnSeries.order_eq_orderTop_of_ne_zero hx0]
    change (↑e : WithTop ℚ) < ↑(c.1.order + x.1.order)
    rw [WithTop.coe_lt_coe]
    have hc0 : (0 : ℚ) ≤ c.1.order :=
      HahnSeries.zero_le_orderTop_iff.mp c.2
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hx0,
      WithTop.coe_lt_coe] at hx
    linarith

/-- A scaled constant whose weighted order exceeds the cutoff belongs to
the higher-order ideal. -/
theorem weightedRegular_constant_mem_higherOrderIdeal
    {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k)
    (w : ℕ) (c : k) {e : ℚ} (he : 0 ≤ e)
    (hlt : e < (w : ℚ) * S.p) :
    S.weightedRegular w (GCD369CubeHahnRegular.constant c) ∈
      higherOrderIdeal e he := by
  change (↑e : WithTop ℚ) <
    (S.t ^ w * (GCD369CubeHahnRegular.constant c).1).orderTop
  by_cases hc : c = 0
  · simp [hc]
  rw [GCD369CubeHahnPoleScale.t, HahnSeries.single_pow]
  change (↑e : WithTop ℚ) <
    (HahnSeries.single (w • S.p) (1 ^ w) * HahnSeries.C c).orderTop
  rw [HahnSeries.C_apply, HahnSeries.single_mul_single,
    HahnSeries.orderTop_single]
  · exact_mod_cast (by simpa [nsmul_eq_mul] using hlt)
  · simp [hc]

end GCD369CubeHahnRegular

/-- Setting all parameters after `d` to zero specializes the four complete
numerators to the integral `d` rows over any commutative ring. -/
theorem GCD369CubeFaberFullN_d_specialize
    {R : Type*} [CommRing R] (a0 a1 a2 a3 a4 d : R) :
    GCD369CubeFaberFullN1 a0 a1 a2 a3 a4 d 0 0 0 0 0 0 =
        GCD369CubeFaberD1 a0 a1 a2 a3 a4 d ∧
    GCD369CubeFaberFullN2 a0 a1 a2 a3 a4 d 0 0 0 0 0 0 =
        GCD369CubeFaberD2 a0 a1 a2 a3 a4 d ∧
    GCD369CubeFaberFullN3 a0 a1 a2 a3 a4 d 0 0 0 0 0 0 =
        GCD369CubeFaberD3 a0 a1 a2 a3 a4 d ∧
    GCD369CubeFaberFullN4 a0 a1 a2 a3 a4 d 0 0 0 0 0 0 =
        GCD369CubeFaberD4 a0 a1 a2 a3 a4 d := by
  constructor
  · simp only [GCD369CubeFaberD1, GCD369CubeFaberN1]
    ring
  constructor
  · simp only [GCD369CubeFaberD2, GCD369CubeFaberN2]
    ring
  constructor
  · simp only [GCD369CubeFaberD3, GCD369CubeFaberN3]
    ring
  · simp only [GCD369CubeFaberD4, GCD369CubeFaberN4]
    ring

/-- The complete numerator rows commute with arbitrary commutative-ring
homomorphisms. -/
theorem GCD369CubeFaberFullN_map
    {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1 : R) :
    f (GCD369CubeFaberFullN1 a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1) =
        GCD369CubeFaberFullN1 (f a0) (f a1) (f a2) (f a3) (f a4)
          (f d) (f c7) (f c5) (f c4) (f c3) (f c2) (f c1) ∧
    f (GCD369CubeFaberFullN2 a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1) =
        GCD369CubeFaberFullN2 (f a0) (f a1) (f a2) (f a3) (f a4)
          (f d) (f c7) (f c5) (f c4) (f c3) (f c2) (f c1) ∧
    f (GCD369CubeFaberFullN3 a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1) =
        GCD369CubeFaberFullN3 (f a0) (f a1) (f a2) (f a3) (f a4)
          (f d) (f c7) (f c5) (f c4) (f c3) (f c2) (f c1) ∧
    f (GCD369CubeFaberFullN4 a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1) =
        GCD369CubeFaberFullN4 (f a0) (f a1) (f a2) (f a3) (f a4)
          (f d) (f c7) (f c5) (f c4) (f c3) (f c2) (f c1) := by
  constructor
  · simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  constructor
  · simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  constructor
  · simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  · simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]

/-- The four integral `d` rows commute with arbitrary commutative-ring
homomorphisms. -/
theorem GCD369CubeFaberD_map
    {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (a0 a1 a2 a3 a4 d : R) :
    f (GCD369CubeFaberD1 a0 a1 a2 a3 a4 d) =
        GCD369CubeFaberD1 (f a0) (f a1) (f a2) (f a3) (f a4) (f d) ∧
    f (GCD369CubeFaberD2 a0 a1 a2 a3 a4 d) =
        GCD369CubeFaberD2 (f a0) (f a1) (f a2) (f a3) (f a4) (f d) ∧
    f (GCD369CubeFaberD3 a0 a1 a2 a3 a4 d) =
        GCD369CubeFaberD3 (f a0) (f a1) (f a2) (f a3) (f a4) (f d) ∧
    f (GCD369CubeFaberD4 a0 a1 a2 a3 a4 d) =
        GCD369CubeFaberD4 (f a0) (f a1) (f a2) (f a3) (f a4) (f d) := by
  constructor
  · simp only [GCD369CubeFaberD1, GCD369CubeFaberN1,
      map_add, map_sub, map_mul, map_pow, map_ofNat]
  constructor
  · simp only [GCD369CubeFaberD2, GCD369CubeFaberN2,
      map_add, map_sub, map_mul, map_pow, map_ofNat]
  constructor
  · simp only [GCD369CubeFaberD3, GCD369CubeFaberN3,
      map_add, map_sub, map_mul, map_pow, map_ofNat]
  · simp only [GCD369CubeFaberD4, GCD369CubeFaberN4,
      map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]

namespace GCD369CubeHahnCommonValueData

theorem TransverseFactor.dN1Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (D : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberD1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant D)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -32 * (GCD369CubeNormalRow1
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u +
        320 * D * S.u ^ 3 * S.v - 960 * D * S.v ^ 3) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    27648 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular3 +
      27648 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular2 -
      9216 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular4 ^ 2 -
      18432 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
      3072 * S.normal.sextic.scale.regular3 ^ 3 +
      5120 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4 ^ 3
  change
    (729 * GCD369CubeFaberN1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant D * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff]
  have hload :
      ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant D * P).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        D * GCD369CubeHahnRegular.constantCoeff P := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta D P
  rw [hload]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + D *
    (27648 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading3 +
      27648 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading2 -
      9216 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading4 ^ 2 -
      18432 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading3 * S.normal.sextic.scale.leading4 -
      3072 * S.normal.sextic.scale.leading3 ^ 3 +
      5120 * S.normal.sextic.scale.leading3 *
          S.normal.sextic.scale.leading4 ^ 3) = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

theorem TransverseFactor.dN2Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (D : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberD2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant D)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      32 * (GCD369CubeNormalRow2
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v +
        64 * D * S.u ^ 5 - 1440 * D * S.u ^ 2 * S.v ^ 2) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    82944 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular2 -
      27648 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular4 ^ 2 +
      41472 * S.normal.sextic.scale.regular1 ^ 2 -
      55296 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
      27648 * S.normal.sextic.scale.regular2 ^ 2 *
        S.normal.sextic.scale.regular4 -
      27648 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 ^ 2 +
      15360 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 ^ 3 +
      23040 * S.normal.sextic.scale.regular3 ^ 2 *
        S.normal.sextic.scale.regular4 ^ 2 -
      2048 * S.normal.sextic.scale.regular4 ^ 5
  change
    (2187 * GCD369CubeFaberN2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant D * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta D P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + D *
    (82944 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading2 -
      27648 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading4 ^ 2 +
      41472 * S.normal.sextic.scale.leading1 ^ 2 -
      55296 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading3 *
            S.normal.sextic.scale.leading4 -
      27648 * S.normal.sextic.scale.leading2 ^ 2 *
          S.normal.sextic.scale.leading4 -
      27648 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading3 ^ 2 +
      15360 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading4 ^ 3 +
      23040 * S.normal.sextic.scale.leading3 ^ 2 *
          S.normal.sextic.scale.leading4 ^ 2 -
      2048 * S.normal.sextic.scale.leading4 ^ 5) = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

theorem TransverseFactor.dN3Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (D : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberD3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant D)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    110592 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular1 -
      55296 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
      55296 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular2 * S.normal.sextic.scale.regular4 -
      36864 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular3 ^ 2 +
      14336 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular4 ^ 3 -
      36864 * S.normal.sextic.scale.regular2 ^ 2 *
        S.normal.sextic.scale.regular3 +
      49152 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 2 +
      18432 * S.normal.sextic.scale.regular3 ^ 3 *
        S.normal.sextic.scale.regular4 -
      10240 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4 ^ 4
  have hzero :
      (243 * GCD369CubeFaberN3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        31104 * GCD369CubeNormalRow3
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v := by
    calc
      _ = (243 : k) *
          (GCD369CubeFaberN3
            S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
            S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
            S.normal.sextic.scale.regular4).1.coeff
              (((2 : ℕ) : ℚ) * T.delta) :=
        GCD369CubeHahnRegular.coeff_nat_mul 243 _ _
      _ = _ := by rw [T.zeroHighN3Coeff]; ring
  change
    (243 * GCD369CubeFaberN3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant D * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta D P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + D *
    (110592 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading1 -
      55296 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading3 *
            S.normal.sextic.scale.leading4 -
      55296 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading2 *
            S.normal.sextic.scale.leading4 -
      36864 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading3 ^ 2 +
      14336 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading4 ^ 3 -
      36864 * S.normal.sextic.scale.leading2 ^ 2 *
          S.normal.sextic.scale.leading3 +
      49152 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading3 *
            S.normal.sextic.scale.leading4 ^ 2 +
      18432 * S.normal.sextic.scale.leading3 ^ 3 *
          S.normal.sextic.scale.leading4 -
      10240 * S.normal.sextic.scale.leading3 *
          S.normal.sextic.scale.leading4 ^ 4) = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

theorem TransverseFactor.dN4Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (D : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberD4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant D)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      32 * (GCD369CubeNormalRow4
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v +
        160 * D * S.u ^ 6 - 5760 * D * S.u ^ 3 * S.v ^ 2 +
        6480 * D * S.v ^ 4) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    373248 * S.normal.sextic.scale.regular0 ^ 2 -
      248832 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular2 * S.normal.sextic.scale.regular4 -
      124416 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular3 ^ 2 +
      55296 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular4 ^ 3 -
      124416 * S.normal.sextic.scale.regular1 ^ 2 *
        S.normal.sextic.scale.regular4 -
      373248 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular2 * S.normal.sextic.scale.regular3 +
      207360 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 2 -
      82944 * S.normal.sextic.scale.regular2 ^ 3 +
      124416 * S.normal.sextic.scale.regular2 ^ 2 *
        S.normal.sextic.scale.regular4 ^ 2 +
      248832 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 ^ 2 *
          S.normal.sextic.scale.regular4 -
      46080 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 ^ 4 +
      20736 * S.normal.sextic.scale.regular3 ^ 4 -
      92160 * S.normal.sextic.scale.regular3 ^ 2 *
        S.normal.sextic.scale.regular4 ^ 3 +
      5120 * S.normal.sextic.scale.regular4 ^ 6
  change
    (6561 * GCD369CubeFaberN4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant D * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta D P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + D *
    (373248 * S.normal.sextic.scale.leading0 ^ 2 -
      248832 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading2 *
            S.normal.sextic.scale.leading4 -
      124416 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading3 ^ 2 +
      55296 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading4 ^ 3 -
      124416 * S.normal.sextic.scale.leading1 ^ 2 *
          S.normal.sextic.scale.leading4 -
      373248 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading2 *
            S.normal.sextic.scale.leading3 +
      207360 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading3 *
            S.normal.sextic.scale.leading4 ^ 2 -
      82944 * S.normal.sextic.scale.leading2 ^ 3 +
      124416 * S.normal.sextic.scale.leading2 ^ 2 *
          S.normal.sextic.scale.leading4 ^ 2 +
      248832 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading3 ^ 2 *
            S.normal.sextic.scale.leading4 -
      46080 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading4 ^ 4 +
      20736 * S.normal.sextic.scale.leading3 ^ 4 -
      92160 * S.normal.sextic.scale.leading3 ^ 2 *
          S.normal.sextic.scale.leading4 ^ 3 +
      5120 * S.normal.sextic.scale.leading4 ^ 6) = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

/-- Vanishing of the four literal quadratic Hahn coefficients is exactly
the source-facing arbitrary-`d` Faber row packet. -/
theorem TransverseFactor.dLeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (D : k)
    (h1 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberD1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant D)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberD2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant D)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberD3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant D)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberD4
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant D)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeDLeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v D := by
  dsimp [GCD369CubeDLeadingFaberRowsAt]
  have hc := GCD369CubeFaberDNormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v D
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.dN1Coeff D]
    exact h1
  · rw [hc2, ← T.dN2Coeff D]
    exact h2
  · rw [hc3, ← T.dN3Coeff D]
    exact h3
  · rw [hc4, ← T.dN4Coeff D]
    exact h4

end GCD369CubeHahnCommonValueData

namespace GCD369CubeHahnFaberPoleData

/-- When the later source parameters and first invariant are literal
ground-field constants, the first complete scaled equation reduces through
order `p` to the specialized `d` numerator. -/
theorem dN1Coeff_zero
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C7 C5 C4 C3 C2 C1 R1 : k)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1) :
    (GCD369CubeFaberD1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)).1.coeff F.scale.p = 0 := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal F.scale.p F.scale.hp.le
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 1 < w) :
      F.scale.p < (w : ℚ) * F.scale.p := by
    simpa only [one_mul] using
      (mul_lt_mul_of_pos_right
        (show (1 : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp)
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by
    rw [hc7, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 2 C7 F.scale.hp.le (hweight 2 (by norm_num))
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by
    rw [hc5, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 4 C5 F.scale.hp.le (hweight 4 (by norm_num))
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by
    rw [hc4, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 5 C4 F.scale.hp.le (hweight 5 (by norm_num))
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by
    rw [hc3, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 6 C3 F.scale.hp.le (hweight 6 (by norm_num))
  have hc2q : q (F.scale.weightedRegular 7 F.c2) = 0 := by
    rw [hc2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 7 C2 F.scale.hp.le (hweight 7 (by norm_num))
  have hc1q : q (F.scale.weightedRegular 8 F.c1) = 0 := by
    rw [hc1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 8 C1 F.scale.hp.le (hweight 8 (by norm_num))
  have hr1q : q (F.scale.weightedRegular 10 F.rho1) = 0 := by
    rw [hr1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 10 R1 F.scale.hp.le (hweight 10 (by norm_num))
  let full := GCD369CubeFaberFullN1
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let drow := GCD369CubeFaberD1
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
  have hqfull_drow : q full = q drow := by
    dsimp only [full, drow]
    rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).1,
      (GCD369CubeFaberD_map q _ _ _ _ _ _).1,
      hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
    exact (GCD369CubeFaberFullN_d_specialize _ _ _ _ _ _).1
  have hscaled : full = 62208 * F.scale.weightedRegular 10 F.rho1 := by
    apply Subtype.ext
    exact F.scaledFullN1
  have hqfull_zero : q full = 0 := by
    rw [hscaled, map_mul, hr1q, mul_zero]
  have hqdrow_zero : q drow = 0 := hqfull_drow ▸ hqfull_zero
  have hdrow_mem : drow ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp hqdrow_zero
  have hdrow_order :
      (↑F.scale.p : WithTop ℚ) < drow.1.orderTop := hdrow_mem
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop hdrow_order

/-- When the later source parameters and second invariant are literal
ground-field constants, the second complete scaled equation reduces through
order `p` to the specialized `d` numerator. -/
theorem dN2Coeff_zero
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C7 C5 C4 C3 C2 C1 R2 : k)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2) :
    (GCD369CubeFaberD2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)).1.coeff F.scale.p = 0 := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal F.scale.p F.scale.hp.le
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 1 < w) :
      F.scale.p < (w : ℚ) * F.scale.p := by
    simpa only [one_mul] using
      (mul_lt_mul_of_pos_right
        (show (1 : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp)
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by
    rw [hc7, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 2 C7 F.scale.hp.le (hweight 2 (by norm_num))
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by
    rw [hc5, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 4 C5 F.scale.hp.le (hweight 4 (by norm_num))
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by
    rw [hc4, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 5 C4 F.scale.hp.le (hweight 5 (by norm_num))
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by
    rw [hc3, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 6 C3 F.scale.hp.le (hweight 6 (by norm_num))
  have hc2q : q (F.scale.weightedRegular 7 F.c2) = 0 := by
    rw [hc2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 7 C2 F.scale.hp.le (hweight 7 (by norm_num))
  have hc1q : q (F.scale.weightedRegular 8 F.c1) = 0 := by
    rw [hc1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 8 C1 F.scale.hp.le (hweight 8 (by norm_num))
  have hr2q : q (F.scale.weightedRegular 11 F.rho2) = 0 := by
    rw [hr2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 11 R2 F.scale.hp.le (hweight 11 (by norm_num))
  let full := GCD369CubeFaberFullN2
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let drow := GCD369CubeFaberD2
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
  have hqfull_drow : q full = q drow := by
    dsimp only [full, drow]
    rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.1,
      (GCD369CubeFaberD_map q _ _ _ _ _ _).2.1,
      hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
    exact (GCD369CubeFaberFullN_d_specialize _ _ _ _ _ _).2.1
  have hscaled : full = 186624 * F.scale.weightedRegular 11 F.rho2 := by
    apply Subtype.ext
    exact F.scaledFullN2
  have hqfull_zero : q full = 0 := by
    rw [hscaled, map_mul, hr2q, mul_zero]
  have hqdrow_zero : q drow = 0 := hqfull_drow ▸ hqfull_zero
  have hdrow_mem : drow ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp hqdrow_zero
  have hdrow_order :
      (↑F.scale.p : WithTop ℚ) < drow.1.orderTop := hdrow_mem
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop hdrow_order

set_option maxRecDepth 10000 in
/-- When the later source parameters and third invariant are literal
ground-field constants, the third complete scaled equation reduces through
order `p` to the specialized `d` numerator. -/
theorem dN3Coeff_zero
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C7 C5 C4 C3 C2 C1 R3 : k)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3) :
    (GCD369CubeFaberD3
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)).1.coeff F.scale.p = 0 := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal F.scale.p F.scale.hp.le
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 1 < w) :
      F.scale.p < (w : ℚ) * F.scale.p := by
    simpa only [one_mul] using
      (mul_lt_mul_of_pos_right
        (show (1 : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp)
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by
    rw [hc7, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 2 C7 F.scale.hp.le (hweight 2 (by norm_num))
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by
    rw [hc5, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 4 C5 F.scale.hp.le (hweight 4 (by norm_num))
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by
    rw [hc4, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 5 C4 F.scale.hp.le (hweight 5 (by norm_num))
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by
    rw [hc3, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 6 C3 F.scale.hp.le (hweight 6 (by norm_num))
  have hc2q : q (F.scale.weightedRegular 7 F.c2) = 0 := by
    rw [hc2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 7 C2 F.scale.hp.le (hweight 7 (by norm_num))
  have hc1q : q (F.scale.weightedRegular 8 F.c1) = 0 := by
    rw [hc1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 8 C1 F.scale.hp.le (hweight 8 (by norm_num))
  have hr3q : q (F.scale.weightedRegular 12 F.rho3) = 0 := by
    rw [hr3, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 12 R3 F.scale.hp.le (hweight 12 (by norm_num))
  let full := GCD369CubeFaberFullN3
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let drow := GCD369CubeFaberD3
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
  have hqfull_drow : q full = q drow := by
    dsimp only [full, drow]
    rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.2.1,
      (GCD369CubeFaberD_map q _ _ _ _ _ _).2.2.1,
      hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
    exact (GCD369CubeFaberFullN_d_specialize _ _ _ _ _ _).2.2.1
  have hscaled : full = 248832 * F.scale.weightedRegular 12 F.rho3 := by
    apply Subtype.ext
    exact F.scaledFullN3
  have hqfull_zero : q full = 0 := by
    rw [hscaled, map_mul, hr3q, mul_zero]
  have hqdrow_zero : q drow = 0 := hqfull_drow ▸ hqfull_zero
  have hdrow_mem : drow ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp hqdrow_zero
  have hdrow_order :
      (↑F.scale.p : WithTop ℚ) < drow.1.orderTop := hdrow_mem
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop hdrow_order

set_option maxRecDepth 10000 in
/-- When the later source parameters and fourth invariant are literal
ground-field constants, the fourth complete scaled equation reduces through
order `p` to the specialized `d` numerator. -/
theorem dN4Coeff_zero
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C7 C5 C4 C3 C2 C1 R4 : k)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4) :
    (GCD369CubeFaberD4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)).1.coeff F.scale.p = 0 := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal F.scale.p F.scale.hp.le
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 1 < w) :
      F.scale.p < (w : ℚ) * F.scale.p := by
    simpa only [one_mul] using
      (mul_lt_mul_of_pos_right
        (show (1 : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp)
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by
    rw [hc7, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 2 C7 F.scale.hp.le (hweight 2 (by norm_num))
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by
    rw [hc5, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 4 C5 F.scale.hp.le (hweight 4 (by norm_num))
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by
    rw [hc4, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 5 C4 F.scale.hp.le (hweight 5 (by norm_num))
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by
    rw [hc3, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 6 C3 F.scale.hp.le (hweight 6 (by norm_num))
  have hc2q : q (F.scale.weightedRegular 7 F.c2) = 0 := by
    rw [hc2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 7 C2 F.scale.hp.le (hweight 7 (by norm_num))
  have hc1q : q (F.scale.weightedRegular 8 F.c1) = 0 := by
    rw [hc1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 8 C1 F.scale.hp.le (hweight 8 (by norm_num))
  have hr4q : q (F.scale.weightedRegular 13 F.rho4) = 0 := by
    rw [hr4, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 13 R4 F.scale.hp.le (hweight 13 (by norm_num))
  let full := GCD369CubeFaberFullN4
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let drow := GCD369CubeFaberD4
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
  have hqfull_drow : q full = q drow := by
    dsimp only [full, drow]
    rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.2.2,
      (GCD369CubeFaberD_map q _ _ _ _ _ _).2.2.2,
      hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
    exact (GCD369CubeFaberFullN_d_specialize _ _ _ _ _ _).2.2.2
  have hscaled : full = 1679616 * F.scale.weightedRegular 13 F.rho4 := by
    apply Subtype.ext
    exact F.scaledFullN4
  have hqfull_zero : q full = 0 := by
    rw [hscaled, map_mul, hr4q, mul_zero]
  have hqdrow_zero : q drow = 0 := hqfull_drow ▸ hqfull_zero
  have hdrow_mem : drow ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp hqdrow_zero
  have hdrow_order :
      (↑F.scale.p : WithTop ℚ) < drow.1.orderTop := hdrow_mem
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop hdrow_order

end GCD369CubeHahnFaberPoleData

#print axioms GCD369CubeHahnRegular.higherOrderIdeal
#print axioms GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
#print axioms GCD369CubeFaberFullN_d_specialize
#print axioms GCD369CubeFaberFullN_map
#print axioms GCD369CubeFaberD_map
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.dN1Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.dN2Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.dN3Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.dN4Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.dLeadingFaberRowsAt
#print axioms GCD369CubeHahnFaberPoleData.dN1Coeff_zero
#print axioms GCD369CubeHahnFaberPoleData.dN2Coeff_zero
#print axioms GCD369CubeHahnFaberPoleData.dN3Coeff_zero
#print axioms GCD369CubeHahnFaberPoleData.dN4Coeff_zero
