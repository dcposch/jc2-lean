import FinitePoleSource

noncomputable section
open Polynomial

/-! # The recovered source coordinate at a finite weighted pole

Original polynomiality says that the normalized sextic evaluated at the
recovered translation is locally regular.  A monic nonarchimedean estimate
then forces the translation itself to have at most the selected weighted
pole.  Its residue is consequently a root of the leading normalized sextic.
-/

private theorem GCD369CubeHahn_orderTop_pow_six_lt_mul
    {k : Type*} [Field k] (x a : HahnSeries ℚ k) (n : ℕ)
    (hx : x.order < 0) (hn : n < 6)
    (ha : (↑(0 : ℚ) : WithTop ℚ) ≤ a.orderTop) :
    (x ^ 6).orderTop < (a * x ^ n).orderTop := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, HahnSeries.order_zero] at hx
    exact (lt_irrefl _ hx)
  have hpow (j : ℕ) :
      (x ^ j).orderTop = (↑((j : ℚ) * x.order) : WithTop ℚ) := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero (pow_ne_zero j hx0),
      HahnSeries.order_pow]
    simp [nsmul_eq_mul]
  rw [HahnSeries.orderTop_mul, hpow 6, hpow n]
  calc
    (↑((6 : ℚ) * x.order) : WithTop ℚ) <
        ↑((n : ℚ) * x.order) := by
      rw [WithTop.coe_lt_coe]
      have hnq : (n : ℚ) < 6 := by exact_mod_cast hn
      nlinarith
    _ = 0 + ↑((n : ℚ) * x.order) := by simp
    _ ≤ a.orderTop + ↑((n : ℚ) * x.order) := by
      simpa [add_comm] using
        (add_le_add_right ha (↑((n : ℚ) * x.order) : WithTop ℚ))

private theorem GCD369CubeHahn_orderTop_lt_add
    {k : Type*} [AddMonoid k] (o : WithTop ℚ)
    (x y : HahnSeries ℚ k)
    (hx : o < x.orderTop) (hy : o < y.orderTop) :
    o < (x + y).orderTop :=
  (lt_min hx hy).trans_le HahnSeries.min_orderTop_le_orderTop_add

set_option maxRecDepth 10000 in
/-- A root up to a regular error of a monic depressed sextic with regular
coefficients is itself regular. -/
theorem GCD369CubeHahn_monicSextic_root_regular
    {k : Type*} [Field k]
    (x a0 a1 a2 a3 a4 y : HahnSeries ℚ k)
    (ha0 : (↑(0 : ℚ) : WithTop ℚ) ≤ a0.orderTop)
    (ha1 : (↑(0 : ℚ) : WithTop ℚ) ≤ a1.orderTop)
    (ha2 : (↑(0 : ℚ) : WithTop ℚ) ≤ a2.orderTop)
    (ha3 : (↑(0 : ℚ) : WithTop ℚ) ≤ a3.orderTop)
    (ha4 : (↑(0 : ℚ) : WithTop ℚ) ≤ a4.orderTop)
    (hy : (↑(0 : ℚ) : WithTop ℚ) ≤ y.orderTop)
    (heq : x ^ 6 +
      (a4 * x ^ 4 + (a3 * x ^ 3 +
        (a2 * x ^ 2 + (a1 * x + a0)))) = y) :
    (0 : ℚ) ≤ x.order := by
  by_contra hxnonneg
  have hx : x.order < 0 := lt_of_not_ge hxnonneg
  have h4 := GCD369CubeHahn_orderTop_pow_six_lt_mul
    x a4 4 hx (by omega) ha4
  have h3 := GCD369CubeHahn_orderTop_pow_six_lt_mul
    x a3 3 hx (by omega) ha3
  have h2 := GCD369CubeHahn_orderTop_pow_six_lt_mul
    x a2 2 hx (by omega) ha2
  have h1raw := GCD369CubeHahn_orderTop_pow_six_lt_mul
    x a1 1 hx (by omega) ha1
  have h1 : (x ^ 6).orderTop < (a1 * x).orderTop := by
    simpa using h1raw
  have h0raw := GCD369CubeHahn_orderTop_pow_six_lt_mul
    x a0 0 hx (by omega) ha0
  have h0 : (x ^ 6).orderTop < a0.orderTop := by
    simpa using h0raw
  have hrest : (x ^ 6).orderTop <
      (a4 * x ^ 4 + (a3 * x ^ 3 +
        (a2 * x ^ 2 + (a1 * x + a0)))).orderTop :=
    GCD369CubeHahn_orderTop_lt_add _ _ _ h4
      (GCD369CubeHahn_orderTop_lt_add _ _ _ h3
        (GCD369CubeHahn_orderTop_lt_add _ _ _ h2
          (GCD369CubeHahn_orderTop_lt_add _ _ _ h1 h0)))
  have hsum := HahnSeries.orderTop_add_eq_left hrest
  have heqorder := congrArg HahnSeries.orderTop heq
  rw [hsum] at heqorder
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, HahnSeries.order_zero] at hx
    exact (lt_irrefl _ hx)
  have hx6order : (x ^ 6).orderTop =
      (↑((6 : ℚ) * x.order) : WithTop ℚ) := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero (pow_ne_zero 6 hx0),
      HahnSeries.order_pow]
    simp [nsmul_eq_mul]
  have hx6neg : (x ^ 6).orderTop < (↑(0 : ℚ) : WithTop ℚ) := by
    rw [hx6order, WithTop.coe_lt_coe]
    linarith
  rw [← heqorder] at hy
  exact (not_le_of_gt hx6neg) hy

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The complete Faber normal polynomial is homogeneous of total weight nine
when the source coordinate has weight one and its parameters have their
canonical weights. -/
theorem GCD369CubeFaberNormalPolynomial_eval_weight
    {K : Type*} [Field K] [CharZero K]
    (t x a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0 : K) :
    (GCD369CubeFaberNormalPolynomial
      (t ^ 6 * a0) (t ^ 5 * a1) (t ^ 4 * a2)
      (t ^ 3 * a3) (t ^ 2 * a4)
      (t * d) (t ^ 2 * c7) (t ^ 3 * c6) (t ^ 4 * c5)
      (t ^ 5 * c4) (t ^ 6 * c3) (t ^ 7 * c2)
      (t ^ 8 * c1) (t ^ 9 * c0)).eval (t * x) =
    t ^ 9 *
      (GCD369CubeFaberNormalPolynomial
        a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0).eval x := by
  simp only [GCD369CubeFaberNormalPolynomial, GCD369CubeFaberNine,
    GCD369CubeFaberEight, GCD369CubeFaberSeven,
    GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree,
    GCD369CubeFaberTwo, GCD369CubeFaberOne,
    GCD369CubeDepressedSextic,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_monomial]
  ring

set_option maxRecDepth 10000 in
/-- Evaluating the complete Faber normal polynomial commutes with every
field homomorphism. -/
theorem GCD369CubeFaberNormalPolynomial_eval_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (x a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0 : K) :
    f ((GCD369CubeFaberNormalPolynomial
      a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0).eval x) =
    (GCD369CubeFaberNormalPolynomial
      (f a0) (f a1) (f a2) (f a3) (f a4)
      (f d) (f c7) (f c6) (f c5) (f c4) (f c3) (f c2)
      (f c1) (f c0)).eval (f x) := by
  simp only [GCD369CubeFaberNormalPolynomial, GCD369CubeFaberNine,
    GCD369CubeFaberEight, GCD369CubeFaberSeven,
    GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree,
    GCD369CubeFaberTwo, GCD369CubeFaberOne,
    GCD369CubeDepressedSextic,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C,
    Polynomial.eval_monomial, _root_.map_div₀, map_add, map_sub,
    map_mul, map_pow, map_ofNat, map_one]

/-! ## Rational-coefficient Faber values in the regular local ring -/

def GCD369CubeFaberOneValueQ
    {R : Type*} [CommRing R] (_q : ℚ →+* R)
    (_a0 _a1 _a2 _a3 _a4 x : R) : R := x

def GCD369CubeFaberTwoValueQ
    {R : Type*} [CommRing R] (q : ℚ →+* R)
    (_a0 _a1 _a2 _a3 a4 x : R) : R :=
  x ^ 2 + q (1 / 3) * a4

def GCD369CubeFaberThreeValueQ
    {R : Type*} [CommRing R] (q : ℚ →+* R)
    (_a0 _a1 _a2 a3 a4 x : R) : R :=
  x ^ 3 + q (1 / 2) * a4 * x + q (1 / 2) * a3

def GCD369CubeFaberFourValueQ
    {R : Type*} [CommRing R] (q : ℚ →+* R)
    (_a0 _a1 a2 a3 a4 x : R) : R :=
  x ^ 4 + q (2 / 3) * a4 * x ^ 2 + q (2 / 3) * a3 * x +
    (q (2 / 3) * a2 - q (1 / 9) * a4 ^ 2)

def GCD369CubeFaberFiveValueQ
    {R : Type*} [CommRing R] (q : ℚ →+* R)
    (_a0 a1 a2 a3 a4 x : R) : R :=
  x ^ 5 + q (5 / 6) * a4 * x ^ 3 + q (5 / 6) * a3 * x ^ 2 +
    (q (5 / 6) * a2 - q (5 / 72) * a4 ^ 2) * x +
    (q (5 / 6) * a1 - q (5 / 36) * a3 * a4)

def GCD369CubeFaberSixValueQ
    {R : Type*} [CommRing R] (_q : ℚ →+* R)
    (a0 a1 a2 a3 a4 x : R) : R :=
  x ^ 6 + a4 * x ^ 4 + a3 * x ^ 3 + a2 * x ^ 2 + a1 * x + a0

def GCD369CubeFaberSevenValueQ
    {R : Type*} [CommRing R] (q : ℚ →+* R)
    (a0 a1 a2 a3 a4 x : R) : R :=
  x ^ 7 + q (7 / 6) * a4 * x ^ 5 + q (7 / 6) * a3 * x ^ 4 +
    (q (7 / 6) * a2 + q (7 / 72) * a4 ^ 2) * x ^ 3 +
    (q (7 / 6) * a1 + q (7 / 36) * a3 * a4) * x ^ 2 +
    (q (7 / 6) * a0 + q (7 / 36) * a2 * a4 +
      q (7 / 72) * a3 ^ 2 - q (35 / 1296) * a4 ^ 3) * x +
    (q (7 / 36) * a1 * a4 + q (7 / 36) * a2 * a3 -
      q (35 / 432) * a3 * a4 ^ 2)

def GCD369CubeFaberEightValueQ
    {R : Type*} [CommRing R] (q : ℚ →+* R)
    (a0 a1 a2 a3 a4 x : R) : R :=
  x ^ 8 + q (4 / 3) * a4 * x ^ 6 + q (4 / 3) * a3 * x ^ 5 +
    (q (4 / 3) * a2 + q (2 / 9) * a4 ^ 2) * x ^ 4 +
    (q (4 / 3) * a1 + q (4 / 9) * a3 * a4) * x ^ 3 +
    (q (4 / 3) * a0 + q (4 / 9) * a2 * a4 +
      q (2 / 9) * a3 ^ 2 - q (4 / 81) * a4 ^ 3) * x ^ 2 +
    (q (4 / 9) * a1 * a4 + q (4 / 9) * a2 * a3 -
      q (4 / 27) * a3 * a4 ^ 2) * x +
    (q (4 / 9) * a0 * a4 + q (4 / 9) * a1 * a3 +
      q (2 / 9) * a2 ^ 2 - q (4 / 27) * a2 * a4 ^ 2 -
      q (4 / 27) * a3 ^ 2 * a4 + q (5 / 243) * a4 ^ 4)

/-- The value of the ninth Faber polynomial, written over an arbitrary
commutative ring equipped with an explicit copy of the rationals.  This form
can be evaluated in the regular Hahn subring, where field division is not
available but all rational constants remain available. -/
def GCD369CubeFaberNineValueQ
    {R : Type*} [CommRing R] (q : ℚ →+* R)
    (a0 a1 a2 a3 a4 x : R) : R :=
  x ^ 9 + q (3 / 2) * a4 * x ^ 7 + q (3 / 2) * a3 * x ^ 6 +
    (q (3 / 2) * a2 + q (3 / 8) * a4 ^ 2) * x ^ 5 +
    (q (3 / 2) * a1 + q (3 / 4) * a3 * a4) * x ^ 4 +
    (q (3 / 2) * a0 + q (3 / 4) * a2 * a4 +
      q (3 / 8) * a3 ^ 2 - q (1 / 16) * a4 ^ 3) * x ^ 3 +
    (q (3 / 4) * a1 * a4 + q (3 / 4) * a2 * a3 -
      q (3 / 16) * a3 * a4 ^ 2) * x ^ 2 +
    (q (3 / 4) * a0 * a4 + q (3 / 4) * a1 * a3 +
      q (3 / 8) * a2 ^ 2 - q (3 / 16) * a2 * a4 ^ 2 -
      q (3 / 16) * a3 ^ 2 * a4 + q (3 / 128) * a4 ^ 4) * x +
    (q (3 / 4) * a0 * a3 + q (3 / 4) * a1 * a2 -
      q (3 / 16) * a1 * a4 ^ 2 - q (3 / 8) * a2 * a3 * a4 -
      q (1 / 16) * a3 ^ 3 + q (3 / 32) * a3 * a4 ^ 3)

/-- The complete Faber normal value over a commutative ring with rational
constants. -/
def GCD369CubeFaberNormalValueQ
    {R : Type*} [CommRing R] (q : ℚ →+* R)
    (a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0 x : R) : R :=
  GCD369CubeFaberNineValueQ q a0 a1 a2 a3 a4 x +
    d * GCD369CubeFaberEightValueQ q a0 a1 a2 a3 a4 x +
    c7 * GCD369CubeFaberSevenValueQ q a0 a1 a2 a3 a4 x +
    c6 * GCD369CubeFaberSixValueQ q a0 a1 a2 a3 a4 x +
    c5 * GCD369CubeFaberFiveValueQ q a0 a1 a2 a3 a4 x +
    c4 * GCD369CubeFaberFourValueQ q a0 a1 a2 a3 a4 x +
    c3 * GCD369CubeFaberThreeValueQ q a0 a1 a2 a3 a4 x +
    c2 * GCD369CubeFaberTwoValueQ q a0 a1 a2 a3 a4 x +
    c1 * GCD369CubeFaberOneValueQ q a0 a1 a2 a3 a4 x + c0

/-- Over a characteristic-zero field, the rational-coefficient value is the
ordinary evaluation of the existing ninth Faber polynomial. -/
theorem GCD369CubeFaberNineValueQ_eq_eval
    {K : Type*} [Field K] [CharZero K]
    (a0 a1 a2 a3 a4 x : K) :
    GCD369CubeFaberNineValueQ (algebraMap ℚ K)
      a0 a1 a2 a3 a4 x =
      (GCD369CubeFaberNine a0 a1 a2 a3 a4).eval x := by
  simp only [GCD369CubeFaberNineValueQ, GCD369CubeFaberNine,
    Polynomial.eval_add, Polynomial.eval_monomial]
  norm_num
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Over a characteristic-zero field, the rational-coefficient normal value
is evaluation of the complete existing Faber normal polynomial. -/
theorem GCD369CubeFaberNormalValueQ_eq_eval
    {K : Type*} [Field K] [CharZero K]
    (a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0 x : K) :
    GCD369CubeFaberNormalValueQ (algebraMap ℚ K)
      a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0 x =
      (GCD369CubeFaberNormalPolynomial
        a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0).eval x := by
  simp only [GCD369CubeFaberNormalValueQ,
    GCD369CubeFaberNineValueQ, GCD369CubeFaberEightValueQ,
    GCD369CubeFaberSevenValueQ, GCD369CubeFaberSixValueQ,
    GCD369CubeFaberFiveValueQ, GCD369CubeFaberFourValueQ,
    GCD369CubeFaberThreeValueQ, GCD369CubeFaberTwoValueQ,
    GCD369CubeFaberOneValueQ,
    GCD369CubeFaberNormalPolynomial, GCD369CubeFaberNine,
    GCD369CubeFaberEight, GCD369CubeFaberSeven,
    GCD369CubeFaberSix, GCD369CubeFaberFive,
    GCD369CubeFaberFour, GCD369CubeFaberThree,
    GCD369CubeFaberTwo, GCD369CubeFaberOne,
    GCD369CubeDepressedSextic,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_monomial]
  norm_num
  ring

/-- Rational-coefficient Faber evaluation commutes with ring homomorphisms. -/
theorem GCD369CubeFaberNormalValueQ_map
    {R L : Type*} [CommRing R] [CommRing L]
    (f : R →+* L) (q : ℚ →+* R)
    (a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0 x : R) :
    f (GCD369CubeFaberNormalValueQ q
      a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0 x) =
    GCD369CubeFaberNormalValueQ (f.comp q)
      (f a0) (f a1) (f a2) (f a3) (f a4)
      (f d) (f c7) (f c6) (f c5) (f c4) (f c3) (f c2)
      (f c1) (f c0) (f x) := by
  simp only [GCD369CubeFaberNormalValueQ,
    GCD369CubeFaberNineValueQ, GCD369CubeFaberEightValueQ,
    GCD369CubeFaberSevenValueQ, GCD369CubeFaberSixValueQ,
    GCD369CubeFaberFiveValueQ, GCD369CubeFaberFourValueQ,
    GCD369CubeFaberThreeValueQ, GCD369CubeFaberTwoValueQ,
    GCD369CubeFaberOneValueQ, RingHom.comp_apply,
    map_add, map_sub, map_mul, map_pow]

/-- Constant Hahn series, regarded as elements of the regular local ring. -/
def GCD369CubeHahnRegular.constant
    {k : Type*} [Field k] : k →+* GCD369CubeHahnRegular k where
  toFun c := ⟨HahnSeries.C c, by
    change (↑(0 : ℚ) : WithTop ℚ) ≤ (HahnSeries.C c).orderTop
    by_cases hc : c = 0
    · simp [hc]
    · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hc]⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The canonical rational constants in the regular Hahn local ring. -/
noncomputable def GCD369CubeHahnRegular.ratCast
    {k : Type*} [Field k] [CharZero k] :
    ℚ →+* GCD369CubeHahnRegular k :=
  GCD369CubeHahnRegular.constant.comp (algebraMap ℚ k)

@[simp] theorem GCD369CubeHahnRegular.coe_ratCast
    {k : Type*} [Field k] [CharZero k] (q : ℚ) :
    ((GCD369CubeHahnRegular.ratCast q : GCD369CubeHahnRegular k) :
      HahnSeries ℚ k) = algebraMap ℚ (HahnSeries ℚ k) q := by
  have h :
      (GCD369CubeHahnRegular k).subtype.comp
          GCD369CubeHahnRegular.ratCast =
        algebraMap ℚ (HahnSeries ℚ k) := Subsingleton.elim _ _
  exact DFunLike.congr_fun h q

@[simp] theorem GCD369CubeHahnRegular.constantCoeff_constant
    {k : Type*} [Field k] (c : k) :
    GCD369CubeHahnRegular.constantCoeff
      (GCD369CubeHahnRegular.constant c) = c := by
  simp [GCD369CubeHahnRegular.constant,
    GCD369CubeHahnRegular.constantCoeff]

@[simp] theorem GCD369CubeHahnRegular.constantCoeff_ratCast
    {k : Type*} [Field k] [CharZero k] (q : ℚ) :
    GCD369CubeHahnRegular.constantCoeff
      (GCD369CubeHahnRegular.ratCast q) = algebraMap ℚ k q := by
  simp [GCD369CubeHahnRegular.ratCast]

/-- The Davenport--Stothers sextic and ninth Faber value have no common root
at any nonzero scale.  This is the homogeneous form of the normalized
boundary Bézout certificate. -/
theorem GCD369CubeDSBoundaryExclusion_scaled
    {K : Type*} [Field K] [CharZero K] (lambda r : K)
    (hlambda : lambda ≠ 0)
    (hf : r ^ 6 + 4 * lambda * r ^ 4 + 10 * lambda ^ 2 * r ^ 2 +
      6 * lambda ^ 3 = 0)
    (hg : r ^ 9 + 6 * lambda * r ^ 7 + 21 * lambda ^ 2 * r ^ 5 +
      35 * lambda ^ 3 * r ^ 3 + (63 / 2) * lambda ^ 4 * r = 0) :
    False := by
  have hbez :
      (6 * r ^ 8 + 28 * lambda * r ^ 6 + 70 * lambda ^ 2 * r ^ 4 +
          70 * lambda ^ 3 * r ^ 2 + 21 * lambda ^ 4) *
          (r ^ 6 + 4 * lambda * r ^ 4 + 10 * lambda ^ 2 * r ^ 2 +
            6 * lambda ^ 3) -
        (6 * r ^ 5 + 16 * lambda * r ^ 3 + 20 * lambda ^ 2 * r) *
          (r ^ 9 + 6 * lambda * r ^ 7 + 21 * lambda ^ 2 * r ^ 5 +
            35 * lambda ^ 3 * r ^ 3 + (63 / 2) * lambda ^ 4 * r) =
        126 * lambda ^ 7 := by
    ring
  rw [hf, hg] at hbez
  simp only [mul_zero, sub_zero] at hbez
  have hne : (126 : K) * lambda ^ 7 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 7 hlambda)
  exact hne hbez.symm

/-- A weighted coefficient pole scale, a recovered source coordinate, and
the regular original sextic value at that coordinate. -/
structure GCD369CubeHahnSexticValueData
    (k : Type*) [Field k] where
  scale : GCD369CubeHahnPoleScale k
  x : HahnSeries ℚ k
  value : GCD369CubeHahnRegular k
  heval : x ^ 6 +
    (scale.a4 * x ^ 4 + (scale.a3 * x ^ 3 +
      (scale.a2 * x ^ 2 + (scale.a1 * x + scale.a0)))) = value.1

namespace GCD369CubeHahnSexticValueData

/-- The recovered coordinate after applying the selected weight-one pole
scale. -/
def scaledX {k : Type*} [Field k]
    (S : GCD369CubeHahnSexticValueData k) : HahnSeries ℚ k :=
  S.scale.t * S.x

/-- Scaling the literal sextic value equation by weight six gives a monic
equation whose five coefficients are the regular weighted coefficients. -/
theorem scaledEquation {k : Type*} [Field k]
    (S : GCD369CubeHahnSexticValueData k) :
    S.scaledX ^ 6 +
      (S.scale.scaled4 * S.scaledX ^ 4 +
        (S.scale.scaled3 * S.scaledX ^ 3 +
          (S.scale.scaled2 * S.scaledX ^ 2 +
            (S.scale.scaled1 * S.scaledX + S.scale.scaled0)))) =
      S.scale.t ^ 6 * S.value.1 := by
  dsimp only [scaledX, GCD369CubeHahnPoleScale.scaled0,
    GCD369CubeHahnPoleScale.scaled1,
    GCD369CubeHahnPoleScale.scaled2,
    GCD369CubeHahnPoleScale.scaled3,
    GCD369CubeHahnPoleScale.scaled4]
  rw [← S.heval]
  ring

/-- The scaled recovered coordinate is regular. -/
theorem scaledX_order_nonneg {k : Type*} [Field k]
    (S : GCD369CubeHahnSexticValueData k) :
    (0 : ℚ) ≤ S.scaledX.order := by
  apply GCD369CubeHahn_monicSextic_root_regular
    S.scaledX S.scale.scaled0 S.scale.scaled1 S.scale.scaled2
      S.scale.scaled3 S.scale.scaled4 (S.scale.t ^ 6 * S.value.1)
    S.scale.scaled0_regular S.scale.scaled1_regular
      S.scale.scaled2_regular S.scale.scaled3_regular
      S.scale.scaled4_regular
  · exact (S.scale.weightedRegular 6 S.value).property
  · exact S.scaledEquation

/-- The scaled coordinate as an element of the regular Hahn local ring. -/
def regularX {k : Type*} [Field k]
    (S : GCD369CubeHahnSexticValueData k) : GCD369CubeHahnRegular k :=
  ⟨S.scaledX, HahnSeries.zero_le_orderTop_iff.mpr S.scaledX_order_nonneg⟩

/-- The residue of the recovered coordinate is a root of the leading
depressed sextic. -/
theorem leadingSexticRoot {k : Type*} [Field k]
    (S : GCD369CubeHahnSexticValueData k) :
    let r := S.scaledX.coeff 0
    r ^ 6 +
      (S.scale.leading4 * r ^ 4 +
        (S.scale.leading3 * r ^ 3 +
          (S.scale.leading2 * r ^ 2 +
            (S.scale.leading1 * r + S.scale.leading0)))) = 0 := by
  dsimp only
  have hsub :
      S.regularX ^ 6 +
        (S.scale.regular4 * S.regularX ^ 4 +
          (S.scale.regular3 * S.regularX ^ 3 +
            (S.scale.regular2 * S.regularX ^ 2 +
              (S.scale.regular1 * S.regularX + S.scale.regular0)))) =
        S.scale.weightedRegular 6 S.value := by
    apply Subtype.ext
    exact S.scaledEquation
  have hres := congrArg GCD369CubeHahnRegular.constantCoeff hsub
  simp only [map_add, map_mul, map_pow] at hres
  rw [S.scale.weightedRegular_constantCoeff_zero 6 (by norm_num)] at hres
  exact hres

end GCD369CubeHahnSexticValueData

/-- A sextic boundary packet together with all regular Faber parameters and
the regular original nonic value.  The displayed equation is the exact
weight-nine scaling of the complete Faber normal form. -/
structure GCD369CubeHahnNormalValueData
    (k : Type*) [Field k] [CharZero k] where
  sextic : GCD369CubeHahnSexticValueData k
  d : GCD369CubeHahnRegular k
  c7 : GCD369CubeHahnRegular k
  c6 : GCD369CubeHahnRegular k
  c5 : GCD369CubeHahnRegular k
  c4 : GCD369CubeHahnRegular k
  c3 : GCD369CubeHahnRegular k
  c2 : GCD369CubeHahnRegular k
  c1 : GCD369CubeHahnRegular k
  c0 : GCD369CubeHahnRegular k
  value : GCD369CubeHahnRegular k
  heval : GCD369CubeFaberNormalValueQ GCD369CubeHahnRegular.ratCast
      sextic.scale.regular0 sextic.scale.regular1
      sextic.scale.regular2 sextic.scale.regular3 sextic.scale.regular4
      (sextic.scale.weightedRegular 1 d)
      (sextic.scale.weightedRegular 2 c7)
      (sextic.scale.weightedRegular 3 c6)
      (sextic.scale.weightedRegular 4 c5)
      (sextic.scale.weightedRegular 5 c4)
      (sextic.scale.weightedRegular 6 c3)
      (sextic.scale.weightedRegular 7 c2)
      (sextic.scale.weightedRegular 8 c1)
      (sextic.scale.weightedRegular 9 c0)
      sextic.regularX = sextic.scale.weightedRegular 9 value

namespace GCD369CubeHahnNormalValueData

/-- Taking residues in the scaled normal-form equation kills every positive
weight target parameter and leaves the ninth Faber polynomial. -/
theorem leadingNonicRoot
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnNormalValueData k) :
    let r := S.sextic.scaledX.coeff 0
    (GCD369CubeFaberNine
      S.sextic.scale.leading0 S.sextic.scale.leading1
      S.sextic.scale.leading2 S.sextic.scale.leading3
      S.sextic.scale.leading4).eval r = 0 := by
  dsimp only
  have hres := congrArg GCD369CubeHahnRegular.constantCoeff S.heval
  rw [GCD369CubeFaberNormalValueQ_map] at hres
  have hqmap :
      GCD369CubeHahnRegular.constantCoeff.comp
          GCD369CubeHahnRegular.ratCast = algebraMap ℚ k :=
    Subsingleton.elim _ _
  rw [hqmap] at hres
  have hd := S.sextic.scale.weightedRegular_constantCoeff_zero
    1 (by norm_num) S.d
  have hc7 := S.sextic.scale.weightedRegular_constantCoeff_zero
    2 (by norm_num) S.c7
  have hc6 := S.sextic.scale.weightedRegular_constantCoeff_zero
    3 (by norm_num) S.c6
  have hc5 := S.sextic.scale.weightedRegular_constantCoeff_zero
    4 (by norm_num) S.c5
  have hc4 := S.sextic.scale.weightedRegular_constantCoeff_zero
    5 (by norm_num) S.c4
  have hc3 := S.sextic.scale.weightedRegular_constantCoeff_zero
    6 (by norm_num) S.c3
  have hc2 := S.sextic.scale.weightedRegular_constantCoeff_zero
    7 (by norm_num) S.c2
  have hc1 := S.sextic.scale.weightedRegular_constantCoeff_zero
    8 (by norm_num) S.c1
  have hc0 := S.sextic.scale.weightedRegular_constantCoeff_zero
    9 (by norm_num) S.c0
  have hvalue := S.sextic.scale.weightedRegular_constantCoeff_zero
    9 (by norm_num) S.value
  rw [hd, hc7, hc6, hc5, hc4, hc3, hc2, hc1, hc0, hvalue] at hres
  simp only [GCD369CubeFaberNormalValueQ, zero_mul, add_zero] at hres
  change GCD369CubeFaberNineValueQ (algebraMap ℚ k)
      S.sextic.scale.leading0 S.sextic.scale.leading1
      S.sextic.scale.leading2 S.sextic.scale.leading3
      S.sextic.scale.leading4 (S.sextic.scaledX.coeff 0) = 0 at hres
  rw [GCD369CubeFaberNineValueQ_eq_eval] at hres
  exact hres

end GCD369CubeHahnNormalValueData

namespace GCD369CubePolynomialSource

/-- The exact recovered translation and original regular sextic value extend
the canonical finite Faber pole packet to sextic boundary data. -/
noncomputable def finiteSexticValueData
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    GCD369CubeHahnSexticValueData k := by
  let H := GCD369CubeRatFuncHahnAt a
  let F := S.finiteFaberPoleData a hpole
  refine {
    scale := F.scale
    x := H S.translation
    value := ⟨H (S.normalizedP.eval S.translation),
      S.hahnAt_normalizedP_eval_translation_orderTop_nonneg a⟩
    heval := ?_
  }
  have hevalRat :
      S.translation ^ 6 +
        (S.normalizedP.coeff 4 * S.translation ^ 4 +
          (S.normalizedP.coeff 3 * S.translation ^ 3 +
            (S.normalizedP.coeff 2 * S.translation ^ 2 +
              (S.normalizedP.coeff 1 * S.translation +
                S.normalizedP.coeff 0)))) =
        S.normalizedP.eval S.translation := by
    calc
      _ = (GCD369CubeDepressedSextic
          (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
          (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
          (S.normalizedP.coeff 4)).eval S.translation := by
        simp [GCD369CubeDepressedSextic, Polynomial.eval_add,
          Polynomial.eval_monomial]
        ring
      _ = S.normalizedP.eval S.translation :=
        congrArg (fun p : (RatFunc k)[X] => p.eval S.translation)
          S.normalizedP_eq_depressed.symm
  change (H S.translation) ^ 6 +
      (H (S.normalizedP.coeff 4) * (H S.translation) ^ 4 +
        (H (S.normalizedP.coeff 3) * (H S.translation) ^ 3 +
          (H (S.normalizedP.coeff 2) * (H S.translation) ^ 2 +
            (H (S.normalizedP.coeff 1) * H S.translation +
              H (S.normalizedP.coeff 0))))) =
    H (S.normalizedP.eval S.translation)
  simpa only [map_add, map_mul, map_pow] using congrArg H hevalRat

/-- The sextic-value packet uses exactly the canonical scale selected by the
finite Faber pole construction. -/
theorem finiteSexticValueData_scale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    (S.finiteSexticValueData a hpole).scale =
      (S.finiteFaberPoleData a hpole).scale := rfl

/-- The scale coefficients and recovered coordinate are literally the local
Hahn expansions selected from the polynomial source. -/
theorem finiteSexticValueData_source_fields
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    let B := S.finiteSexticValueData a hpole
    B.scale.a0 = GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0) ∧
    B.scale.a1 = GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1) ∧
    B.scale.a2 = GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2) ∧
    B.scale.a3 = GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3) ∧
    B.scale.a4 = GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4) ∧
    B.x = GCD369CubeRatFuncHahnAt a S.translation := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The literal normalized nonic, evaluated at the recovered translation,
supplies the exact weight-nine normal-form equation over the regular Hahn
local ring. -/
noncomputable def finiteNormalValueData
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    GCD369CubeHahnNormalValueData k := by
  letI : CharZero (HahnSeries ℚ k) :=
    charZero_of_injective_algebraMap (R := k)
      (RingHom.injective (algebraMap k (HahnSeries ℚ k)))
  let H := GCD369CubeRatFuncHahnAt a
  let B := S.finiteSexticValueData a hpole
  let N := S.faberNormalForm
  let P := S.faberConstantParameters
  let dr := GCD369CubeHahnRegular.ofRatFuncConstant a P.d
  let c7r := GCD369CubeHahnRegular.ofRatFuncConstant a P.c7
  let c6r := GCD369CubeHahnRegular.ofRatFuncConstant a P.c6
  let c5r := GCD369CubeHahnRegular.ofRatFuncConstant a P.c5
  let c4r := GCD369CubeHahnRegular.ofRatFuncConstant a P.c4
  let c3r := GCD369CubeHahnRegular.ofRatFuncConstant a P.c3
  let c2r := GCD369CubeHahnRegular.ofRatFuncConstant a P.c2
  let c1r := GCD369CubeHahnRegular.ofRatFuncConstant a P.c1
  let c0r := GCD369CubeHahnRegular.ofRatFuncConstant a P.c0
  let qvalue : GCD369CubeHahnRegular k :=
    ⟨H (S.normalizedQ.eval S.translation),
      S.hahnAt_normalizedQ_eval_translation_orderTop_nonneg a⟩
  refine {
    sextic := B
    d := dr
    c7 := c7r
    c6 := c6r
    c5 := c5r
    c4 := c4r
    c3 := c3r
    c2 := c2r
    c1 := c1r
    c0 := c0r
    value := qvalue
    heval := ?_
  }
  rcases S.finiteSexticValueData_source_fields a hpole with
    ⟨ha0, ha1, ha2, ha3, ha4, hx⟩
  change B.scale.a0 = H (S.normalizedP.coeff 0) at ha0
  change B.scale.a1 = H (S.normalizedP.coeff 1) at ha1
  change B.scale.a2 = H (S.normalizedP.coeff 2) at ha2
  change B.scale.a3 = H (S.normalizedP.coeff 3) at ha3
  change B.scale.a4 = H (S.normalizedP.coeff 4) at ha4
  change B.x = H S.translation at hx
  have hqRat :
      S.normalizedQ = GCD369CubeFaberNormalPolynomial
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        (algebraMap k (RatFunc k) P.d)
        (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c6)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1)
        (algebraMap k (RatFunc k) P.c0) := by
    calc
      S.normalizedQ = GCD369CubeFaberNormalPolynomial
          (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
          (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
          (S.normalizedP.coeff 4)
          N.d N.c7 N.c6 N.c5 N.c4 N.c3 N.c2 N.c1 N.c0 := by
        simpa only [GCD369CubeFaberNormalPolynomial] using N.hq
      _ = _ := by rw [P.hd, P.hc7, P.hc6, P.hc5, P.hc4,
        P.hc3, P.hc2, P.hc1, P.hc0]
  have hnormalRat :
      (GCD369CubeFaberNormalPolynomial
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        (algebraMap k (RatFunc k) P.d)
        (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c6)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1)
        (algebraMap k (RatFunc k) P.c0)).eval S.translation =
      S.normalizedQ.eval S.translation := by
    exact congrArg (fun q : (RatFunc k)[X] => q.eval S.translation)
      hqRat.symm
  have hnormalH := congrArg H hnormalRat
  rw [GCD369CubeFaberNormalPolynomial_eval_map] at hnormalH
  have hweight := GCD369CubeFaberNormalPolynomial_eval_weight
    B.scale.t (H S.translation)
    (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
    (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
    (H (S.normalizedP.coeff 4))
    (H (algebraMap k (RatFunc k) P.d))
    (H (algebraMap k (RatFunc k) P.c7))
    (H (algebraMap k (RatFunc k) P.c6))
    (H (algebraMap k (RatFunc k) P.c5))
    (H (algebraMap k (RatFunc k) P.c4))
    (H (algebraMap k (RatFunc k) P.c3))
    (H (algebraMap k (RatFunc k) P.c2))
    (H (algebraMap k (RatFunc k) P.c1))
    (H (algebraMap k (RatFunc k) P.c0))
  apply Subtype.ext
  let inclusion := (GCD369CubeHahnRegular k).subtype
  have hmapRegular := GCD369CubeFaberNormalValueQ_map
    inclusion GCD369CubeHahnRegular.ratCast
    B.scale.regular0 B.scale.regular1 B.scale.regular2
    B.scale.regular3 B.scale.regular4
    (B.scale.weightedRegular 1 dr)
    (B.scale.weightedRegular 2 c7r)
    (B.scale.weightedRegular 3 c6r)
    (B.scale.weightedRegular 4 c5r)
    (B.scale.weightedRegular 5 c4r)
    (B.scale.weightedRegular 6 c3r)
    (B.scale.weightedRegular 7 c2r)
    (B.scale.weightedRegular 8 c1r)
    (B.scale.weightedRegular 9 c0r) B.regularX
  have hqmap : inclusion.comp GCD369CubeHahnRegular.ratCast =
      algebraMap ℚ (HahnSeries ℚ k) := Subsingleton.elim _ _
  rw [hqmap] at hmapRegular
  calc
    _ = GCD369CubeFaberNormalValueQ
        (algebraMap ℚ (HahnSeries ℚ k))
        B.scale.regular0.1 B.scale.regular1.1 B.scale.regular2.1
        B.scale.regular3.1 B.scale.regular4.1
        (B.scale.weightedRegular 1 dr).1
        (B.scale.weightedRegular 2 c7r).1
        (B.scale.weightedRegular 3 c6r).1
        (B.scale.weightedRegular 4 c5r).1
        (B.scale.weightedRegular 5 c4r).1
        (B.scale.weightedRegular 6 c3r).1
        (B.scale.weightedRegular 7 c2r).1
        (B.scale.weightedRegular 8 c1r).1
        (B.scale.weightedRegular 9 c0r).1 B.regularX.1 := hmapRegular
    _ = (GCD369CubeFaberNormalPolynomial
        B.scale.regular0.1 B.scale.regular1.1 B.scale.regular2.1
        B.scale.regular3.1 B.scale.regular4.1
        (B.scale.weightedRegular 1 dr).1
        (B.scale.weightedRegular 2 c7r).1
        (B.scale.weightedRegular 3 c6r).1
        (B.scale.weightedRegular 4 c5r).1
        (B.scale.weightedRegular 5 c4r).1
        (B.scale.weightedRegular 6 c3r).1
        (B.scale.weightedRegular 7 c2r).1
        (B.scale.weightedRegular 8 c1r).1
        (B.scale.weightedRegular 9 c0r).1).eval B.regularX.1 :=
      GCD369CubeFaberNormalValueQ_eq_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ = B.scale.t ^ 9 * H (S.normalizedQ.eval S.translation) := by
      rw [← hnormalH]
      simpa only [GCD369CubeHahnPoleScale.regular0,
        GCD369CubeHahnPoleScale.regular1,
        GCD369CubeHahnPoleScale.regular2,
        GCD369CubeHahnPoleScale.regular3,
        GCD369CubeHahnPoleScale.regular4,
        GCD369CubeHahnPoleScale.scaled0,
        GCD369CubeHahnPoleScale.scaled1,
        GCD369CubeHahnPoleScale.scaled2,
        GCD369CubeHahnPoleScale.scaled3,
        GCD369CubeHahnPoleScale.scaled4,
        GCD369CubeHahnPoleScale.weightedRegular,
        GCD369CubeHahnSexticValueData.regularX,
        GCD369CubeHahnSexticValueData.scaledX,
        dr, c7r, c6r, c5r, c4r, c3r, c2r, c1r, c0r,
        GCD369CubeHahnRegular.ofRatFuncConstant,
        pow_one, ha0, ha1, ha2, ha3, ha4, hx] using hweight
    _ = (B.scale.weightedRegular 9 qvalue).1 := rfl

/-- The same residue that roots the leading sextic also roots the leading
ninth Faber polynomial. -/
theorem finiteLeadingNonicRoot
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    let B := S.finiteSexticValueData a hpole
    let r := B.scaledX.coeff 0
    (GCD369CubeFaberNine B.scale.leading0 B.scale.leading1
      B.scale.leading2 B.scale.leading3 B.scale.leading4).eval r = 0 :=
  (S.finiteNormalValueData a hpole).leadingNonicRoot

/-- The original sextic and nonic boundary values eliminate the
Davenport--Stothers component, so the leading Faber point is necessarily a
nonzero common-cubic square. -/
theorem finiteLeadingComponent_common
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    let B := S.finiteSexticValueData a hpole
    ∃ u v : k, (u ≠ 0 ∨ v ≠ 0) ∧
      B.scale.leading4 = 2 * u ∧
      B.scale.leading3 = 2 * v ∧
      B.scale.leading2 = u ^ 2 ∧
      B.scale.leading1 = 2 * u * v ∧
      B.scale.leading0 = v ^ 2 := by
  let B := S.finiteSexticValueData a hpole
  have hcomponent := (S.finiteLeadingFaberSource a hpole).toComponent
  change GCD369CubeLeadingComponent
    B.scale.leading0 B.scale.leading1 B.scale.leading2
      B.scale.leading3 B.scale.leading4 at hcomponent
  rcases hcomponent with
    ⟨u, v, hprojective, ha4, ha3, ha2, ha1, ha0⟩ |
    ⟨lambda, hlambda, ha4, ha3, ha2, ha1, ha0⟩
  · exact ⟨u, v, hprojective, ha4, ha3, ha2, ha1, ha0⟩
  · let r := B.scaledX.coeff 0
    exfalso
    have hf := B.leadingSexticRoot
    have hg := S.finiteLeadingNonicRoot a hpole
    change r ^ 6 +
      (B.scale.leading4 * r ^ 4 +
        (B.scale.leading3 * r ^ 3 +
          (B.scale.leading2 * r ^ 2 +
            (B.scale.leading1 * r + B.scale.leading0)))) = 0 at hf
    change (GCD369CubeFaberNine
      B.scale.leading0 B.scale.leading1 B.scale.leading2
      B.scale.leading3 B.scale.leading4).eval r = 0 at hg
    have hfDS :
        r ^ 6 + 4 * lambda * r ^ 4 + 10 * lambda ^ 2 * r ^ 2 +
          6 * lambda ^ 3 = 0 := by
      rw [ha4, ha3, ha2, ha1, ha0] at hf
      linear_combination hf
    have hgDS :
        r ^ 9 + 6 * lambda * r ^ 7 + 21 * lambda ^ 2 * r ^ 5 +
          35 * lambda ^ 3 * r ^ 3 + (63 / 2) * lambda ^ 4 * r = 0 := by
      rw [ha4, ha3, ha2, ha1, ha0] at hg
      simp only [GCD369CubeFaberNine, Polynomial.eval_add,
        Polynomial.eval_monomial] at hg
      linear_combination hg
    exact GCD369CubeDSBoundaryExclusion_scaled lambda r hlambda hfDS hgDS

/-- The residue of the recovered translation is therefore an actual root of
the leading normalized sextic attached to the same Faber pole packet. -/
theorem finiteLeadingSexticRoot
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    let B := S.finiteSexticValueData a hpole
    let r := B.scaledX.coeff 0
    r ^ 6 +
      (B.scale.leading4 * r ^ 4 +
        (B.scale.leading3 * r ^ 3 +
          (B.scale.leading2 * r ^ 2 +
            (B.scale.leading1 * r + B.scale.leading0)))) = 0 :=
  (S.finiteSexticValueData a hpole).leadingSexticRoot

end GCD369CubePolynomialSource

#print axioms GCD369CubeHahn_monicSextic_root_regular
#print axioms GCD369CubeDSBoundaryExclusion_scaled
#print axioms GCD369CubeHahnSexticValueData.scaledX_order_nonneg
#print axioms GCD369CubeHahnSexticValueData.leadingSexticRoot
#print axioms GCD369CubeHahnNormalValueData.leadingNonicRoot
#print axioms GCD369CubePolynomialSource.finiteSexticValueData
#print axioms GCD369CubePolynomialSource.finiteSexticValueData_scale
#print axioms GCD369CubePolynomialSource.finiteNormalValueData
#print axioms GCD369CubePolynomialSource.finiteLeadingSexticRoot
#print axioms GCD369CubePolynomialSource.finiteLeadingNonicRoot
#print axioms GCD369CubePolynomialSource.finiteLeadingComponent_common
