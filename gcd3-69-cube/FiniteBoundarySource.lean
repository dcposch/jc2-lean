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
#print axioms GCD369CubeHahnSexticValueData.scaledX_order_nonneg
#print axioms GCD369CubeHahnSexticValueData.leadingSexticRoot
#print axioms GCD369CubePolynomialSource.finiteSexticValueData
#print axioms GCD369CubePolynomialSource.finiteSexticValueData_scale
#print axioms GCD369CubePolynomialSource.finiteLeadingSexticRoot
