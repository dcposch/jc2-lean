import RationalSource

noncomputable section

open Polynomial

universe u

/-! # Literal polynomial cube source

This module begins the remaining map from a normalized bivariate Keller
source to the exhaustive rational pole source closed in `RationalSource`.
The input is the original pair in `k[x][y]`; no Faber or pole landing is an
assumption.
-/

/-- Coefficientwise differentiation in the inner source variable `x`. -/
noncomputable def GCD369CubeSourceXDeriv
    {k : Type*} [CommRing k] (p : k[X][X]) : k[X][X] :=
  PolynomialModule.equivPolynomialSelf (Polynomial.derivative'.mapCoeffs p)

@[simp] theorem GCD369CubeSourceXDeriv_coeff
    {k : Type*} [CommRing k] (p : k[X][X]) (n : ℕ) :
    (GCD369CubeSourceXDeriv p).coeff n = (p.coeff n).derivative := by
  rfl

/-- The coefficient-polynomial Jacobian of a bivariate pair. -/
noncomputable def GCD369CubeBivariateJacobian
    {k : Type*} [CommRing k] (p q : k[X][X]) : k[X][X] :=
  GCD369CubeSourceXDeriv p * derivative q -
    derivative p * GCD369CubeSourceXDeriv q

/-- The first row below the leading weighted-Wronskian row for outer
degrees `(6,9)`. -/
theorem GCD369CubeNextJacobianRow
    {k : Type*} [Field k] [CharZero k]
    {p q : k[X][X]} {j : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 9)
    (hjac : GCD369CubeBivariateJacobian p q = C (C j)) :
    (p.coeff 6).derivative * (q.coeff 8 * C (8 : k)) +
        (p.coeff 5).derivative * (q.coeff 9 * C (9 : k)) -
      ((p.coeff 6 * C (6 : k)) * (q.coeff 8).derivative +
        (p.coeff 5 * C (5 : k)) * (q.coeff 9).derivative) = 0 := by
  have hcoeff := congrArg (fun r : k[X][X] => r.coeff 13) hjac
  simp only [GCD369CubeBivariateJacobian, coeff_sub, coeff_mul,
    GCD369CubeSourceXDeriv_coeff, coeff_derivative, coeff_C,
    show (13 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 13 :
      Finset (ℕ × ℕ)) =
      ({(0, 13), (1, 12), (2, 11), (3, 10), (4, 9), (5, 8), (6, 7),
        (7, 6), (8, 5), (9, 4), (10, 3), (11, 2), (12, 1), (13, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC8 : C (8 : k) = (8 : k[X]) := C_eq_natCast 8
  have hC9 : C (9 : k) = (9 : k[X]) := C_eq_natCast 9
  have hC6 : C (6 : k) = (6 : k[X]) := C_eq_natCast 6
  have hC5 : C (5 : k) = (5 : k[X]) := C_eq_natCast 5
  rw [hC8, hC9, hC6, hC5]
  linear_combination hcoeff

/-- For a sextic, the fifth Hasse derivative consists of exactly its top
two coefficients. -/
theorem GCD369CubeHasseFiveOfDegreeSix
    {K : Type*} [Field K] [CharZero K]
    (p : K[X]) (hp : p.natDegree = 6) :
    hasseDeriv 5 p = C (p.coeff 5) + C (6 * p.coeff 6) * X := by
  ext n
  rw [hasseDeriv_coeff]
  by_cases hn0 : n = 0
  · subst n
    norm_num
  by_cases hn1 : n = 1
  · subst n
    norm_num
  have hn2 : 2 ≤ n := by omega
  have hcoeff : p.coeff (n + 5) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  rw [hcoeff, mul_zero]
  rw [coeff_add, coeff_C_mul]
  simp [coeff_C, coeff_X, hn0]
  intro h
  exact (hn1 h.symm).elim

/-- For a nonic, the eighth Hasse derivative consists of exactly its top
two coefficients. -/
theorem GCD369CubeHasseEightOfDegreeNine
    {K : Type*} [Field K] [CharZero K]
    (q : K[X]) (hq : q.natDegree = 9) :
    hasseDeriv 8 q = C (q.coeff 8) + C (9 * q.coeff 9) * X := by
  ext n
  rw [hasseDeriv_coeff]
  by_cases hn0 : n = 0
  · subst n
    norm_num
  by_cases hn1 : n = 1
  · subst n
    norm_num
  have hn2 : 2 ≤ n := by omega
  have hcoeff : q.coeff (n + 8) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  rw [hcoeff, mul_zero]
  rw [coeff_add, coeff_C_mul]
  simp [coeff_C, coeff_X, hn0]
  intro h
  exact (hn1 h.symm).elim

/-- The Jacobian bracket for two polynomials over `k(x)`, using the
quotient-rule derivative on coefficients and the ordinary derivative in the
outer variable. -/
noncomputable def GCD369CubeRatFuncJacobian
    {k : Type*} [Field k] (p q : (RatFunc k)[X]) : (RatFunc k)[X] :=
  GCD369CubeRatFuncCoefficientDerivative p * derivative q -
    derivative p * GCD369CubeRatFuncCoefficientDerivative q

/-- A common substitution in the outer variable scales this bracket by the
ordinary derivative of the substituted coordinate. -/
theorem GCD369CubeRatFuncJacobian_comp
    {k : Type*} [Field k]
    (p q L : (RatFunc k)[X]) :
    GCD369CubeRatFuncJacobian (p.comp L) (q.comp L) =
      derivative L * (GCD369CubeRatFuncJacobian p q).comp L := by
  simp only [GCD369CubeRatFuncJacobian,
    GCD369CubeRatFuncCoefficientDerivative_comp, derivative_comp,
    sub_comp, mul_comp]
  ring

/-- Coefficient convolution for the rational-function Jacobian bracket. -/
theorem GCD369CubeRatFuncJacobian_coeff
    {k : Type*} [Field k] (p q : (RatFunc k)[X]) (n : ℕ) :
    (GCD369CubeRatFuncJacobian p q).coeff n =
      (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        GCD369CubeRatFuncDerivative (p.coeff ij.1) *
          (q.coeff (ij.2 + 1) * ((ij.2 : RatFunc k) + 1))) -
      (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (p.coeff (ij.1 + 1) * ((ij.1 : RatFunc k) + 1)) *
          GCD369CubeRatFuncDerivative (q.coeff ij.2)) := by
  unfold GCD369CubeRatFuncJacobian
  simp only [coeff_sub, coeff_mul,
    GCD369CubeRatFuncCoefficientDerivative_coeff, coeff_derivative]

/-- The zeroth Faber polynomial. -/
noncomputable def GCD369CubeFaberZero {K : Type*} [Field K]
    (_a0 _a1 _a2 _a3 _a4 : K) : K[X] :=
  monomial 0 1

/-- The first Faber polynomial. -/
noncomputable def GCD369CubeFaberOne {K : Type*} [Field K]
    (_a0 _a1 _a2 _a3 _a4 : K) : K[X] :=
  monomial 1 1

/-- The second Faber polynomial, the polynomial part of `f^(1/3)`. -/
noncomputable def GCD369CubeFaberTwo {K : Type*} [Field K]
    (_a0 _a1 _a2 _a3 a4 : K) : K[X] :=
  monomial 2 1 + monomial 0 (a4 / 3)

/-- The third Faber polynomial, the polynomial part of `f^(1/2)`. -/
noncomputable def GCD369CubeFaberThree {K : Type*} [Field K]
    (_a0 _a1 _a2 a3 a4 : K) : K[X] :=
  monomial 3 1 + monomial 1 (a4 / 2) + monomial 0 (a3 / 2)

/-- The fourth Faber polynomial, the polynomial part of `f^(2/3)`. -/
noncomputable def GCD369CubeFaberFour {K : Type*} [Field K]
    (_a0 _a1 a2 a3 a4 : K) : K[X] :=
  monomial 4 1 + monomial 2 (2 * a4 / 3) +
    monomial 1 (2 * a3 / 3) +
    monomial 0 (2 * a2 / 3 - a4 ^ 2 / 9)

/-- The fifth Faber polynomial, the polynomial part of `f^(5/6)`. -/
noncomputable def GCD369CubeFaberFive {K : Type*} [Field K]
    (_a0 a1 a2 a3 a4 : K) : K[X] :=
  monomial 5 1 + monomial 3 (5 * a4 / 6) +
    monomial 2 (5 * a3 / 6) +
    monomial 1 (5 * a2 / 6 - 5 * a4 ^ 2 / 72) +
    monomial 0 (5 * a1 / 6 - 5 * a3 * a4 / 36)

/-- The sixth Faber polynomial is the depressed sextic itself. -/
noncomputable def GCD369CubeFaberSix {K : Type*} [Field K]
    (a0 a1 a2 a3 a4 : K) : K[X] :=
  GCD369CubeDepressedSextic a0 a1 a2 a3 a4

/-- The seventh Faber polynomial, i.e. the polynomial part of `f^(7/6)`. -/
noncomputable def GCD369CubeFaberSeven {K : Type*} [Field K]
    (a0 a1 a2 a3 a4 : K) : K[X] :=
  monomial 7 1 + monomial 5 (7 * a4 / 6) +
    monomial 4 (7 * a3 / 6) +
    monomial 3 (7 * a2 / 6 + 7 * a4 ^ 2 / 72) +
    monomial 2 (7 * a1 / 6 + 7 * a3 * a4 / 36) +
    monomial 1 (7 * a0 / 6 + 7 * a2 * a4 / 36 +
      7 * a3 ^ 2 / 72 - 35 * a4 ^ 3 / 1296) +
    monomial 0 (7 * a1 * a4 / 36 + 7 * a2 * a3 / 36 -
      35 * a3 * a4 ^ 2 / 432)

/-- The eighth Faber polynomial, i.e. the polynomial part of `f^(4/3)`. -/
noncomputable def GCD369CubeFaberEight {K : Type*} [Field K]
    (a0 a1 a2 a3 a4 : K) : K[X] :=
  monomial 8 1 + monomial 6 (4 * a4 / 3) +
    monomial 5 (4 * a3 / 3) +
    monomial 4 (4 * a2 / 3 + 2 * a4 ^ 2 / 9) +
    monomial 3 (4 * a1 / 3 + 4 * a3 * a4 / 9) +
    monomial 2 (4 * a0 / 3 + 4 * a2 * a4 / 9 +
      2 * a3 ^ 2 / 9 - 4 * a4 ^ 3 / 81) +
    monomial 1 (4 * a1 * a4 / 9 + 4 * a2 * a3 / 9 -
      4 * a3 * a4 ^ 2 / 27) +
    monomial 0 (4 * a0 * a4 / 9 + 4 * a1 * a3 / 9 +
      2 * a2 ^ 2 / 9 - 4 * a2 * a4 ^ 2 / 27 -
      4 * a3 ^ 2 * a4 / 27 + 5 * a4 ^ 4 / 243)

/-- The ninth Faber polynomial, i.e. the polynomial part of the formal
power `f^(3/2)` for the depressed sextic `f`. -/
noncomputable def GCD369CubeFaberNine {K : Type*} [Field K]
    (a0 a1 a2 a3 a4 : K) : K[X] :=
  monomial 9 1 + monomial 7 (3 * a4 / 2) +
    monomial 6 (3 * a3 / 2) +
    monomial 5 (3 * a2 / 2 + 3 * a4 ^ 2 / 8) +
    monomial 4 (3 * a1 / 2 + 3 * a3 * a4 / 4) +
    monomial 3 (3 * a0 / 2 + 3 * a2 * a4 / 4 +
      3 * a3 ^ 2 / 8 - a4 ^ 3 / 16) +
    monomial 2 (3 * a1 * a4 / 4 + 3 * a2 * a3 / 4 -
      3 * a3 * a4 ^ 2 / 16) +
    monomial 1 (3 * a0 * a4 / 4 + 3 * a1 * a3 / 4 +
      3 * a2 ^ 2 / 8 - 3 * a2 * a4 ^ 2 / 16 -
      3 * a3 ^ 2 * a4 / 16 + 3 * a4 ^ 4 / 128) +
    monomial 0 (3 * a0 * a3 / 4 + 3 * a1 * a2 / 4 -
      3 * a1 * a4 ^ 2 / 16 - 3 * a2 * a3 * a4 / 8 -
      a3 ^ 3 / 16 + 3 * a3 * a4 ^ 3 / 32)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All outer rows above degree four cancel in the bracket of a depressed
sextic with its ninth Faber polynomial. -/
theorem GCD369CubeFaberNine_highRows
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
      (GCD369CubeFaberNine a0 a1 a2 a3 a4)).natDegree ≤ 4 := by
  have hD0 : GCD369CubeRatFuncDerivative (0 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_zero
  have hD1 : GCD369CubeRatFuncDerivative (1 : RatFunc k) = 0 := by
    simpa using GCD369CubeRatFuncDerivative_C (1 : k)
  have hD2 : GCD369CubeRatFuncDerivative (2 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 2
  have hD3 : GCD369CubeRatFuncDerivative (3 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 3
  have hD4 : GCD369CubeRatFuncDerivative (4 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 4
  have hD8 : GCD369CubeRatFuncDerivative (8 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 8
  have hD16 : GCD369CubeRatFuncDerivative (16 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 16
  have hD32 : GCD369CubeRatFuncDerivative (32 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 32
  have hD128 : GCD369CubeRatFuncDerivative (128 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 128
  let f := GCD369CubeDepressedSextic a0 a1 a2 a3 a4
  let g := GCD369CubeFaberNine a0 a1 a2 a3 a4
  let B := GCD369CubeRatFuncJacobian f g
  have hf : f.natDegree = 6 := by
    dsimp [f, GCD369CubeDepressedSextic]
    compute_degree <;> norm_num
  have hg : g.natDegree = 9 := by
    dsimp [g, GCD369CubeFaberNine]
    compute_degree <;> norm_num
  have hB : B.natDegree ≤ 14 := by
    dsimp only [B, GCD369CubeRatFuncJacobian]
    apply le_trans (natDegree_sub_le _ _)
    apply max_le
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le f)
        (natDegree_derivative_le g))
      omega
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (natDegree_derivative_le f)
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le g))
      omega
  change B.natDegree ≤ 4
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hn14 : n ≤ 14
  · interval_cases n <;>
      rw [GCD369CubeRatFuncJacobian_coeff] <;>
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;>
      norm_num [Finset.sum_range_succ, f, g,
        GCD369CubeDepressedSextic, GCD369CubeFaberNine,
        coeff_add, coeff_monomial,
        GCD369CubeRatFuncDerivative_add, GCD369CubeRatFuncDerivative_mul,
        GCD369CubeRatFuncDerivative_neg, GCD369CubeRatFuncDerivative_sub,
        GCD369CubeRatFuncDerivative_pow,
        GCD369CubeRatFuncDerivative_div_general,
        hD0, hD1, hD2, hD3, hD4, hD8, hD16, hD32, hD128] at hn ⊢ <;>
      ring
  · exact natDegree_le_iff_coeff_eq_zero.mp hB n (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The eighth Faber polynomial has the same high-row cancellation. -/
theorem GCD369CubeFaberEight_highRows
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
      (GCD369CubeFaberEight a0 a1 a2 a3 a4)).natDegree ≤ 4 := by
  have hD0 : GCD369CubeRatFuncDerivative (0 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_zero
  have hD1 : GCD369CubeRatFuncDerivative (1 : RatFunc k) = 0 := by
    simpa using GCD369CubeRatFuncDerivative_C (1 : k)
  have hD2 : GCD369CubeRatFuncDerivative (2 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 2
  have hD3 : GCD369CubeRatFuncDerivative (3 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 3
  have hD4 : GCD369CubeRatFuncDerivative (4 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 4
  have hD5 : GCD369CubeRatFuncDerivative (5 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 5
  have hD9 : GCD369CubeRatFuncDerivative (9 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 9
  have hD27 : GCD369CubeRatFuncDerivative (27 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 27
  have hD81 : GCD369CubeRatFuncDerivative (81 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 81
  have hD243 : GCD369CubeRatFuncDerivative (243 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 243
  let f := GCD369CubeDepressedSextic a0 a1 a2 a3 a4
  let g := GCD369CubeFaberEight a0 a1 a2 a3 a4
  let B := GCD369CubeRatFuncJacobian f g
  have hf : f.natDegree = 6 := by
    dsimp [f, GCD369CubeDepressedSextic]
    compute_degree <;> norm_num
  have hg : g.natDegree = 8 := by
    dsimp [g, GCD369CubeFaberEight]
    compute_degree <;> norm_num
  have hB : B.natDegree ≤ 13 := by
    dsimp only [B, GCD369CubeRatFuncJacobian]
    apply le_trans (natDegree_sub_le _ _)
    apply max_le
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le f)
        (natDegree_derivative_le g))
      omega
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (natDegree_derivative_le f)
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le g))
      omega
  change B.natDegree ≤ 4
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hn13 : n ≤ 13
  · interval_cases n <;>
      rw [GCD369CubeRatFuncJacobian_coeff] <;>
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;>
      norm_num [Finset.sum_range_succ, f, g,
        GCD369CubeDepressedSextic, GCD369CubeFaberEight,
        coeff_add, coeff_monomial,
        GCD369CubeRatFuncDerivative_add, GCD369CubeRatFuncDerivative_mul,
        GCD369CubeRatFuncDerivative_neg, GCD369CubeRatFuncDerivative_sub,
        GCD369CubeRatFuncDerivative_pow,
        GCD369CubeRatFuncDerivative_div_general,
        hD0, hD1, hD2, hD3, hD4, hD5, hD9, hD27, hD81, hD243] at hn ⊢ <;>
      ring
  · exact natDegree_le_iff_coeff_eq_zero.mp hB n (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The seventh Faber polynomial has the same high-row cancellation. -/
theorem GCD369CubeFaberSeven_highRows
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
      (GCD369CubeFaberSeven a0 a1 a2 a3 a4)).natDegree ≤ 4 := by
  have hD0 : GCD369CubeRatFuncDerivative (0 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_zero
  have hD1 : GCD369CubeRatFuncDerivative (1 : RatFunc k) = 0 := by
    simpa using GCD369CubeRatFuncDerivative_C (1 : k)
  have hD6 : GCD369CubeRatFuncDerivative (6 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 6
  have hD7 : GCD369CubeRatFuncDerivative (7 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 7
  have hD35 : GCD369CubeRatFuncDerivative (35 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 35
  have hD36 : GCD369CubeRatFuncDerivative (36 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 36
  have hD72 : GCD369CubeRatFuncDerivative (72 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 72
  have hD432 : GCD369CubeRatFuncDerivative (432 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 432
  have hD1296 : GCD369CubeRatFuncDerivative (1296 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 1296
  let f := GCD369CubeDepressedSextic a0 a1 a2 a3 a4
  let g := GCD369CubeFaberSeven a0 a1 a2 a3 a4
  let B := GCD369CubeRatFuncJacobian f g
  have hf : f.natDegree = 6 := by
    dsimp [f, GCD369CubeDepressedSextic]
    compute_degree <;> norm_num
  have hg : g.natDegree = 7 := by
    dsimp [g, GCD369CubeFaberSeven]
    compute_degree <;> norm_num
  have hB : B.natDegree ≤ 12 := by
    dsimp only [B, GCD369CubeRatFuncJacobian]
    apply le_trans (natDegree_sub_le _ _)
    apply max_le
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le f)
        (natDegree_derivative_le g))
      omega
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (natDegree_derivative_le f)
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le g))
      omega
  change B.natDegree ≤ 4
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hn12 : n ≤ 12
  · interval_cases n <;>
      rw [GCD369CubeRatFuncJacobian_coeff] <;>
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;>
      norm_num [Finset.sum_range_succ, f, g,
        GCD369CubeDepressedSextic, GCD369CubeFaberSeven,
        coeff_add, coeff_monomial,
        GCD369CubeRatFuncDerivative_add, GCD369CubeRatFuncDerivative_mul,
        GCD369CubeRatFuncDerivative_neg, GCD369CubeRatFuncDerivative_sub,
        GCD369CubeRatFuncDerivative_pow,
        GCD369CubeRatFuncDerivative_div_general,
        hD0, hD1, hD6, hD7, hD35, hD36, hD72, hD432, hD1296] at hn ⊢ <;>
      ring
  · exact natDegree_le_iff_coeff_eq_zero.mp hB n (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The fifth Faber polynomial has the same high-row cancellation. -/
theorem GCD369CubeFaberFive_highRows
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
      (GCD369CubeFaberFive a0 a1 a2 a3 a4)).natDegree ≤ 4 := by
  have hD0 : GCD369CubeRatFuncDerivative (0 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_zero
  have hD1 : GCD369CubeRatFuncDerivative (1 : RatFunc k) = 0 := by
    simpa using GCD369CubeRatFuncDerivative_C (1 : k)
  have hD5 : GCD369CubeRatFuncDerivative (5 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 5
  have hD6 : GCD369CubeRatFuncDerivative (6 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 6
  have hD36 : GCD369CubeRatFuncDerivative (36 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 36
  have hD72 : GCD369CubeRatFuncDerivative (72 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 72
  let f := GCD369CubeDepressedSextic a0 a1 a2 a3 a4
  let g := GCD369CubeFaberFive a0 a1 a2 a3 a4
  let B := GCD369CubeRatFuncJacobian f g
  have hf : f.natDegree = 6 := by
    dsimp [f, GCD369CubeDepressedSextic]
    compute_degree <;> norm_num
  have hg : g.natDegree = 5 := by
    dsimp [g, GCD369CubeFaberFive]
    compute_degree <;> norm_num
  have hB : B.natDegree ≤ 10 := by
    dsimp only [B, GCD369CubeRatFuncJacobian]
    apply le_trans (natDegree_sub_le _ _)
    apply max_le
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le f)
        (natDegree_derivative_le g))
      omega
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (natDegree_derivative_le f)
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le g))
      omega
  change B.natDegree ≤ 4
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hn10 : n ≤ 10
  · interval_cases n <;>
      rw [GCD369CubeRatFuncJacobian_coeff] <;>
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;>
      norm_num [Finset.sum_range_succ, f, g,
        GCD369CubeDepressedSextic, GCD369CubeFaberFive,
        coeff_add, coeff_monomial,
        GCD369CubeRatFuncDerivative_add, GCD369CubeRatFuncDerivative_mul,
        GCD369CubeRatFuncDerivative_neg, GCD369CubeRatFuncDerivative_sub,
        GCD369CubeRatFuncDerivative_pow,
        GCD369CubeRatFuncDerivative_div_general,
        hD0, hD1, hD5, hD6, hD36, hD72] at hn ⊢ <;>
      ring
  · exact natDegree_le_iff_coeff_eq_zero.mp hB n (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The fourth Faber polynomial has the same high-row cancellation. -/
theorem GCD369CubeFaberFour_highRows
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
      (GCD369CubeFaberFour a0 a1 a2 a3 a4)).natDegree ≤ 4 := by
  have hD0 : GCD369CubeRatFuncDerivative (0 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_zero
  have hD1 : GCD369CubeRatFuncDerivative (1 : RatFunc k) = 0 := by
    simpa using GCD369CubeRatFuncDerivative_C (1 : k)
  have hD2 : GCD369CubeRatFuncDerivative (2 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 2
  have hD3 : GCD369CubeRatFuncDerivative (3 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 3
  have hD9 : GCD369CubeRatFuncDerivative (9 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 9
  let f := GCD369CubeDepressedSextic a0 a1 a2 a3 a4
  let g := GCD369CubeFaberFour a0 a1 a2 a3 a4
  let B := GCD369CubeRatFuncJacobian f g
  have hf : f.natDegree = 6 := by
    dsimp [f, GCD369CubeDepressedSextic]
    compute_degree <;> norm_num
  have hg : g.natDegree = 4 := by
    dsimp [g, GCD369CubeFaberFour]
    compute_degree <;> norm_num
  have hB : B.natDegree ≤ 9 := by
    dsimp only [B, GCD369CubeRatFuncJacobian]
    apply le_trans (natDegree_sub_le _ _)
    apply max_le
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le f)
        (natDegree_derivative_le g))
      omega
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (natDegree_derivative_le f)
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le g))
      omega
  change B.natDegree ≤ 4
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hn9 : n ≤ 9
  · interval_cases n <;>
      rw [GCD369CubeRatFuncJacobian_coeff] <;>
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;>
      norm_num [Finset.sum_range_succ, f, g,
        GCD369CubeDepressedSextic, GCD369CubeFaberFour,
        coeff_add, coeff_monomial,
        GCD369CubeRatFuncDerivative_add, GCD369CubeRatFuncDerivative_mul,
        GCD369CubeRatFuncDerivative_neg, GCD369CubeRatFuncDerivative_sub,
        GCD369CubeRatFuncDerivative_pow,
        GCD369CubeRatFuncDerivative_div_general,
        hD0, hD1, hD2, hD3, hD9] at hn ⊢ <;>
      ring
  · exact natDegree_le_iff_coeff_eq_zero.mp hB n (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The third Faber polynomial has the same high-row cancellation. -/
theorem GCD369CubeFaberThree_highRows
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
      (GCD369CubeFaberThree a0 a1 a2 a3 a4)).natDegree ≤ 4 := by
  have hD0 : GCD369CubeRatFuncDerivative (0 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_zero
  have hD1 : GCD369CubeRatFuncDerivative (1 : RatFunc k) = 0 := by
    simpa using GCD369CubeRatFuncDerivative_C (1 : k)
  have hD2 : GCD369CubeRatFuncDerivative (2 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 2
  let f := GCD369CubeDepressedSextic a0 a1 a2 a3 a4
  let g := GCD369CubeFaberThree a0 a1 a2 a3 a4
  let B := GCD369CubeRatFuncJacobian f g
  have hf : f.natDegree = 6 := by
    dsimp [f, GCD369CubeDepressedSextic]
    compute_degree <;> norm_num
  have hg : g.natDegree = 3 := by
    dsimp [g, GCD369CubeFaberThree]
    compute_degree <;> norm_num
  have hB : B.natDegree ≤ 8 := by
    dsimp only [B, GCD369CubeRatFuncJacobian]
    apply le_trans (natDegree_sub_le _ _)
    apply max_le
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le f)
        (natDegree_derivative_le g))
      omega
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (natDegree_derivative_le f)
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le g))
      omega
  change B.natDegree ≤ 4
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hn8 : n ≤ 8
  · interval_cases n <;>
      rw [GCD369CubeRatFuncJacobian_coeff] <;>
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;>
      norm_num [Finset.sum_range_succ, f, g,
        GCD369CubeDepressedSextic, GCD369CubeFaberThree,
        coeff_add, coeff_monomial,
        GCD369CubeRatFuncDerivative_add, GCD369CubeRatFuncDerivative_mul,
        GCD369CubeRatFuncDerivative_neg, GCD369CubeRatFuncDerivative_sub,
        GCD369CubeRatFuncDerivative_pow,
        GCD369CubeRatFuncDerivative_div_general,
        hD0, hD1, hD2] at hn ⊢ <;>
      ring
  · exact natDegree_le_iff_coeff_eq_zero.mp hB n (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The second Faber polynomial has the same high-row cancellation. -/
theorem GCD369CubeFaberTwo_highRows
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
      (GCD369CubeFaberTwo a0 a1 a2 a3 a4)).natDegree ≤ 4 := by
  have hD0 : GCD369CubeRatFuncDerivative (0 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_zero
  have hD1 : GCD369CubeRatFuncDerivative (1 : RatFunc k) = 0 := by
    simpa using GCD369CubeRatFuncDerivative_C (1 : k)
  have hD3 : GCD369CubeRatFuncDerivative (3 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_ofNat 3
  let f := GCD369CubeDepressedSextic a0 a1 a2 a3 a4
  let g := GCD369CubeFaberTwo a0 a1 a2 a3 a4
  let B := GCD369CubeRatFuncJacobian f g
  have hf : f.natDegree = 6 := by
    dsimp [f, GCD369CubeDepressedSextic]
    compute_degree <;> norm_num
  have hg : g.natDegree = 2 := by
    dsimp [g, GCD369CubeFaberTwo]
    compute_degree <;> norm_num
  have hB : B.natDegree ≤ 7 := by
    dsimp only [B, GCD369CubeRatFuncJacobian]
    apply le_trans (natDegree_sub_le _ _)
    apply max_le
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le f)
        (natDegree_derivative_le g))
      omega
    · apply le_trans natDegree_mul_le
      apply le_trans (Nat.add_le_add
        (natDegree_derivative_le f)
        (GCD369CubeRatFuncCoefficientDerivative_natDegree_le g))
      omega
  change B.natDegree ≤ 4
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hn7 : n ≤ 7
  · interval_cases n <;>
      rw [GCD369CubeRatFuncJacobian_coeff] <;>
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;>
      norm_num [Finset.sum_range_succ, f, g,
        GCD369CubeDepressedSextic, GCD369CubeFaberTwo,
        coeff_add, coeff_monomial,
        GCD369CubeRatFuncDerivative_add, GCD369CubeRatFuncDerivative_mul,
        GCD369CubeRatFuncDerivative_neg, GCD369CubeRatFuncDerivative_sub,
        GCD369CubeRatFuncDerivative_pow,
        GCD369CubeRatFuncDerivative_div_general,
        hD0, hD1, hD3] at hn ⊢ <;>
      ring
  · exact natDegree_le_iff_coeff_eq_zero.mp hB n (by omega)

/-- The sixth Faber polynomial brackets with itself to zero. -/
theorem GCD369CubeFaberSix_highRows
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
      (GCD369CubeFaberSix a0 a1 a2 a3 a4)).natDegree ≤ 4 := by
  unfold GCD369CubeRatFuncJacobian GCD369CubeFaberSix
  ring
  norm_num

/-- The first Faber bracket is the coefficientwise derivative of the
depressed sextic, hence has outer degree at most four. -/
theorem GCD369CubeFaberOne_highRows
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
      (GCD369CubeFaberOne a0 a1 a2 a3 a4)).natDegree ≤ 4 := by
  have hD0 : GCD369CubeRatFuncDerivative (0 : RatFunc k) = 0 :=
    GCD369CubeRatFuncDerivative_zero
  have hD1 : GCD369CubeRatFuncDerivative (1 : RatFunc k) = 0 := by
    simpa using GCD369CubeRatFuncDerivative_C (1 : k)
  unfold GCD369CubeRatFuncJacobian GCD369CubeDepressedSextic
    GCD369CubeFaberOne
  simp only [GCD369CubeRatFuncCoefficientDerivative_add,
    GCD369CubeRatFuncCoefficientDerivative_monomial,
    derivative_add, derivative_monomial, hD0, hD1]
  norm_num
  compute_degree

/-- The zeroth Faber polynomial is constant, so its bracket vanishes. -/
theorem GCD369CubeFaberZero_highRows
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 : RatFunc k) :
    (GCD369CubeRatFuncJacobian
      (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
      (GCD369CubeFaberZero a0 a1 a2 a3 a4)).natDegree ≤ 4 := by
  unfold GCD369CubeRatFuncJacobian GCD369CubeFaberZero
  simp [GCD369CubeRatFuncCoefficientDerivative_one]

/-- A literal normalized polynomial cube source at partial degrees `(6,9)`.
The two leading coefficients are the actual sixth and ninth powers of the
same nonzero polynomial, and the original Jacobian is a nonzero scalar. -/
structure GCD369CubePolynomialSource (k : Type u) [Field k] where
  s : k[X]
  p : k[X][X]
  q : k[X][X]
  j : k
  hs : s ≠ 0
  hj : j ≠ 0
  hp : p.natDegree = 6
  hq : q.natDegree = 9
  hp6 : p.coeff 6 = s ^ 6
  hq9 : q.coeff 9 = s ^ 9
  hjac : GCD369CubeBivariateJacobian p q = C (C j)

namespace GCD369CubePolynomialSource

/-- The rational-function image of the cube root. -/
noncomputable def sRat {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) : RatFunc k :=
  algebraMap k[X] (RatFunc k) S.s

/-- The normalized fifth sextic coefficient `A=a₅/s⁵`. -/
noncomputable def A {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) : RatFunc k :=
  algebraMap k[X] (RatFunc k) (S.p.coeff 5) / S.sRat ^ 5

/-- The normalized eighth nonic coefficient `B=b₈/s⁸`. -/
noncomputable def B {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) : RatFunc k :=
  algebraMap k[X] (RatFunc k) (S.q.coeff 8) / S.sRat ^ 8

/-- The canonical coefficient embedding into the rational function field. -/
noncomputable def coefficientMap {k : Type u} [Field k]
    (_S : GCD369CubePolynomialSource k) : k[X] →+* RatFunc k :=
  algebraMap k[X] (RatFunc k)

/-- The original sextic after embedding its coefficient polynomials in
`k(x)`. -/
noncomputable def pRat {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) : (RatFunc k)[X] :=
  S.p.map S.coefficientMap

/-- The original nonic after embedding its coefficient polynomials in
`k(x)`. -/
noncomputable def qRat {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) : (RatFunc k)[X] :=
  S.q.map S.coefficientMap

/-- Translation used to depress the normalized sextic. -/
noncomputable def translation {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) : RatFunc k := S.A / 6

/-- The exact transformed sextic in the coordinate `z=s*y+r`. -/
noncomputable def normalizedP {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) : (RatFunc k)[X] :=
  GCD369CubeSourceTransform S.pRat S.sRat⁻¹
    (-(S.sRat⁻¹ * S.translation))

/-- The exact transformed nonic in the same coordinate `z=s*y+r`. -/
noncomputable def normalizedQ {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) : (RatFunc k)[X] :=
  GCD369CubeSourceTransform S.qRat S.sRat⁻¹
    (-(S.sRat⁻¹ * S.translation))

@[simp] theorem pRat_coeff
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) (n : ℕ) :
    S.pRat.coeff n = algebraMap k[X] (RatFunc k) (S.p.coeff n) := by
  simp [pRat, coefficientMap]

@[simp] theorem qRat_coeff
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) (n : ℕ) :
    S.qRat.coeff n = algebraMap k[X] (RatFunc k) (S.q.coeff n) := by
  simp [qRat, coefficientMap]

/-- Coefficientwise rational differentiation of the embedded sextic is the
embedded inner-source derivative. -/
theorem pRat_coefficientDerivative
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) :
    GCD369CubeRatFuncCoefficientDerivative S.pRat =
      (GCD369CubeSourceXDeriv S.p).map S.coefficientMap := by
  ext n
  simp [GCD369CubeRatFuncDerivative_polynomial,
    GCD369CubeSourceXDeriv_coeff, coefficientMap]

/-- Coefficientwise rational differentiation of the embedded nonic is the
embedded inner-source derivative. -/
theorem qRat_coefficientDerivative
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) :
    GCD369CubeRatFuncCoefficientDerivative S.qRat =
      (GCD369CubeSourceXDeriv S.q).map S.coefficientMap := by
  ext n
  simp [GCD369CubeRatFuncDerivative_polynomial,
    GCD369CubeSourceXDeriv_coeff, coefficientMap]

/-- Ordinary outer differentiation commutes with coefficient embedding for
the sextic. -/
theorem pRat_derivative
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) :
    derivative S.pRat = (derivative S.p).map S.coefficientMap := by
  simp [pRat, derivative_map]

/-- Ordinary outer differentiation commutes with coefficient embedding for
the nonic. -/
theorem qRat_derivative
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) :
    derivative S.qRat = (derivative S.q).map S.coefficientMap := by
  simp [qRat, derivative_map]

/-- Embedding the original bivariate source into `k(x)[y]` preserves its
scalar Jacobian exactly. -/
theorem pRat_qRat_jacobian
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) :
    GCD369CubeRatFuncJacobian S.pRat S.qRat =
      C (algebraMap k (RatFunc k) S.j) := by
  calc
    GCD369CubeRatFuncJacobian S.pRat S.qRat =
        (GCD369CubeBivariateJacobian S.p S.q).map S.coefficientMap := by
      simp [GCD369CubeRatFuncJacobian, GCD369CubeBivariateJacobian,
        S.pRat_coefficientDerivative, S.qRat_coefficientDerivative,
        S.pRat_derivative, S.qRat_derivative]
    _ = (C (C S.j)).map S.coefficientMap := by rw [S.hjac]
    _ = C (algebraMap k (RatFunc k) S.j) := by
      simp [coefficientMap, RatFunc.algebraMap_C,
        RatFunc.algebraMap_eq_C]

theorem pRat_natDegree
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) :
    S.pRat.natDegree = 6 := by
  rw [pRat, natDegree_map_eq_of_injective]
  · exact S.hp
  · exact RatFunc.algebraMap_injective k

theorem qRat_natDegree
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) :
    S.qRat.natDegree = 9 := by
  rw [qRat, natDegree_map_eq_of_injective]
  · exact S.hq
  · exact RatFunc.algebraMap_injective k

/-- The normalized sextic is monic. -/
theorem normalizedP_coeff_six
    {k : Type u} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    S.normalizedP.coeff 6 = 1 := by
  rw [normalizedP, GCD369CubeSourceTransformCoeff]
  have hhasse : hasseDeriv 6 S.pRat = C S.pRat.leadingCoeff := by
    simpa [S.pRat_natDegree] using hasseDeriv_natDegree_eq_C S.pRat
  rw [hhasse, eval_C]
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  have hlead : S.pRat.leadingCoeff = S.sRat ^ 6 := by
    rw [leadingCoeff, S.pRat_natDegree, S.pRat_coeff, S.hp6]
    simp [sRat]
  rw [hlead]
  field_simp [hsRat]

/-- The translation `r=A/6` removes the fifth sextic coefficient exactly. -/
theorem normalizedP_coeff_five
    {k : Type u} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    S.normalizedP.coeff 5 = 0 := by
  rw [normalizedP, GCD369CubeSourceTransformCoeff,
    GCD369CubeHasseFiveOfDegreeSix S.pRat S.pRat_natDegree]
  simp only [eval_add, eval_C, eval_mul, eval_X, S.pRat_coeff]
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  rw [S.hp6]
  simp only [map_pow]
  dsimp only [translation, A]
  field_simp [hsRat]
  simp [sRat]

/-- The normalized nonic is monic. -/
theorem normalizedQ_coeff_nine
    {k : Type u} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    S.normalizedQ.coeff 9 = 1 := by
  rw [normalizedQ, GCD369CubeSourceTransformCoeff]
  have hhasse : hasseDeriv 9 S.qRat = C S.qRat.leadingCoeff := by
    simpa [S.qRat_natDegree] using hasseDeriv_natDegree_eq_C S.qRat
  rw [hhasse, eval_C]
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  have hlead : S.qRat.leadingCoeff = S.sRat ^ 9 := by
    rw [leadingCoeff, S.qRat_natDegree, S.qRat_coeff, S.hq9]
    simp [sRat]
  rw [hlead]
  field_simp [hsRat]

/-- The same translation turns the eighth nonic coefficient into the
base-field constant `-delta/2` supplied by the source Jacobian row. -/
theorem normalizedQ_coeff_eight
    {k : Type u} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (delta : k)
    (hdelta : 3 * S.A - 2 * S.B = algebraMap k (RatFunc k) delta) :
    S.normalizedQ.coeff 8 = algebraMap k (RatFunc k) (-delta / 2) := by
  have hcoeff : S.normalizedQ.coeff 8 = S.B - 9 * S.translation := by
    rw [normalizedQ, GCD369CubeSourceTransformCoeff,
      GCD369CubeHasseEightOfDegreeNine S.qRat S.qRat_natDegree]
    simp only [eval_add, eval_C, eval_mul, eval_X, S.qRat_coeff]
    have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
    rw [S.hq9]
    simp only [map_pow]
    dsimp only [translation, B]
    field_simp [hsRat]
    simp [sRat]
    ring
  rw [hcoeff]
  dsimp only [translation]
  rw [_root_.map_div₀ (algebraMap k (RatFunc k)),
    map_neg, map_ofNat]
  rw [← hdelta]
  ring

/-- The invertible affine normalization preserves the sextic degree. -/
theorem normalizedP_natDegree
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) :
    S.normalizedP.natDegree = 6 := by
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  unfold normalizedP GCD369CubeSourceTransform
  let L : (RatFunc k)[X] :=
    C S.sRat⁻¹ * X + C (-(S.sRat⁻¹ * S.translation))
  change (S.pRat.comp L).natDegree = 6
  have hLdegree : L.natDegree = 1 := by
    exact natDegree_linear (inv_ne_zero hsRat)
  have hp0 : S.pRat ≠ 0 := by
    intro hp0
    have hdegree := congrArg natDegree hp0
    rw [S.pRat_natDegree, natDegree_zero] at hdegree
    omega
  have hL0 : L ≠ 0 := by
    intro hL0
    have hdegree := congrArg natDegree hL0
    rw [hLdegree, natDegree_zero] at hdegree
    omega
  rw [natDegree_comp_eq_of_mul_ne_zero]
  · rw [S.pRat_natDegree, hLdegree]
  · exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp0)
      (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hL0))

/-- The same affine normalization preserves the nonic degree. -/
theorem normalizedQ_natDegree
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) :
    S.normalizedQ.natDegree = 9 := by
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  unfold normalizedQ GCD369CubeSourceTransform
  let L : (RatFunc k)[X] :=
    C S.sRat⁻¹ * X + C (-(S.sRat⁻¹ * S.translation))
  change (S.qRat.comp L).natDegree = 9
  have hLdegree : L.natDegree = 1 := by
    exact natDegree_linear (inv_ne_zero hsRat)
  have hq0 : S.qRat ≠ 0 := by
    intro hq0
    have hdegree := congrArg natDegree hq0
    rw [S.qRat_natDegree, natDegree_zero] at hdegree
    omega
  have hL0 : L ≠ 0 := by
    intro hL0
    have hdegree := congrArg natDegree hL0
    rw [hLdegree, natDegree_zero] at hdegree
    omega
  rw [natDegree_comp_eq_of_mul_ne_zero]
  · rw [S.qRat_natDegree, hLdegree]
  · exact mul_ne_zero (leadingCoeff_ne_zero.mpr hq0)
      (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hL0))

/-- The normalized sextic is literally the depressed sextic determined by
its five lower coefficients. -/
theorem normalizedP_eq_depressed
    {k : Type u} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    S.normalizedP = GCD369CubeDepressedSextic
      (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
      (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
      (S.normalizedP.coeff 4) := by
  ext n
  by_cases hn : n ≤ 6
  · interval_cases n <;>
      simp [GCD369CubeDepressedSextic, coeff_monomial,
        S.normalizedP_coeff_five,
        S.normalizedP_coeff_six]
  · have hn6 : 6 < n := by omega
    have hleft : S.normalizedP.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa [S.normalizedP_natDegree]
    rw [hleft]
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    have hn6' : n ≠ 6 := by omega
    simp [GCD369CubeDepressedSextic, coeff_monomial, coeff_C, hn0,
      hn1.symm, hn2.symm, hn3.symm, hn4.symm, hn6'.symm]

/-- The common affine source normalization divides the original scalar
Jacobian by the cube-root polynomial, with all derivatives of the moving
scale and translation cancelling by the chain rule. -/
theorem normalized_jacobian
    {k : Type u} [Field k] (S : GCD369CubePolynomialSource k) :
    GCD369CubeRatFuncJacobian S.normalizedP S.normalizedQ =
      C (algebraMap k (RatFunc k) S.j / S.sRat) := by
  rw [normalizedP, normalizedQ]
  simp only [GCD369CubeSourceTransform]
  rw [GCD369CubeRatFuncJacobian_comp, S.pRat_qRat_jacobian]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X,
    mul_one, zero_mul, add_zero, zero_add, C_comp]
  rw [← C_mul]
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  congr 1
  field_simp [hsRat]

/-- The denominator-cleared source row forced by the original Jacobian. -/
theorem firstRow
    {k : Type u} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    (3 : k[X]) * S.s ^ 4 * (S.p.coeff 5).derivative -
        (15 : k[X]) * S.s ^ 3 * S.p.coeff 5 * S.s.derivative -
      (2 : k[X]) * S.s * (S.q.coeff 8).derivative +
        (16 : k[X]) * S.q.coeff 8 * S.s.derivative = 0 := by
  have hrow := GCD369CubeNextJacobianRow S.hp S.hq S.hjac
  rw [S.hp6, S.hq9] at hrow
  have hC8 : C (8 : k) = (8 : k[X]) := C_eq_natCast 8
  have hC9 : C (9 : k) = (9 : k[X]) := C_eq_natCast 9
  have hC6 : C (6 : k) = (6 : k[X]) := C_eq_natCast 6
  have hC5 : C (5 : k) = (5 : k[X]) := C_eq_natCast 5
  rw [hC8, hC9, hC6, hC5] at hrow
  have hscaled : (3 : k[X]) * S.s ^ 5 *
      ((3 : k[X]) * S.s ^ 4 * (S.p.coeff 5).derivative -
          (15 : k[X]) * S.s ^ 3 * S.p.coeff 5 * S.s.derivative -
        (2 : k[X]) * S.s * (S.q.coeff 8).derivative +
          (16 : k[X]) * S.q.coeff 8 * S.s.derivative) = 0 := by
    calc
      (3 : k[X]) * S.s ^ 5 *
          ((3 : k[X]) * S.s ^ 4 * (S.p.coeff 5).derivative -
              (15 : k[X]) * S.s ^ 3 * S.p.coeff 5 * S.s.derivative -
            (2 : k[X]) * S.s * (S.q.coeff 8).derivative +
              (16 : k[X]) * S.q.coeff 8 * S.s.derivative) =
          (S.s ^ 6).derivative * (S.q.coeff 8 * (8 : k[X])) +
            (S.p.coeff 5).derivative * (S.s ^ 9 * (9 : k[X])) -
          ((S.s ^ 6 * (6 : k[X])) * (S.q.coeff 8).derivative +
            (S.p.coeff 5 * (5 : k[X])) * (S.s ^ 9).derivative) := by
              simp only [derivative_pow, C_eq_natCast]
              ring
      _ = 0 := hrow
  exact (mul_eq_zero.mp hscaled).resolve_left
    (mul_ne_zero (by norm_num) (pow_ne_zero 5 S.hs))

/-- The alignment discriminator has one reduced rational presentation with
denominator `s⁸`. -/
theorem alignmentPresentation
    {k : Type u} [Field k]
    (S : GCD369CubePolynomialSource k) :
    3 * S.A - 2 * S.B =
      algebraMap k[X] (RatFunc k)
          (3 * S.s ^ 3 * S.p.coeff 5 - 2 * S.q.coeff 8) /
        algebraMap k[X] (RatFunc k) (S.s ^ 8) := by
  have hsRat : S.sRat ≠ 0 := RatFunc.algebraMap_ne_zero S.hs
  dsimp only [A, B, sRat]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  field_simp [hsRat]

/-- The literal first Jacobian row makes the rational alignment
discriminator derivative vanish. -/
theorem alignmentDerivative_zero
    {k : Type u} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    GCD369CubeRatFuncDerivative (3 * S.A - 2 * S.B) = 0 := by
  let N : k[X] := 3 * S.s ^ 3 * S.p.coeff 5 - 2 * S.q.coeff 8
  let D : k[X] := S.s ^ 8
  have hD : D ≠ 0 := pow_ne_zero 8 S.hs
  have hpresentation : 3 * S.A - 2 * S.B =
      algebraMap k[X] (RatFunc k) N /
        algebraMap k[X] (RatFunc k) D := by
    exact S.alignmentPresentation
  rw [hpresentation, GCD369CubeRatFuncDerivative_div N D hD]
  have hnumerator : D * N.derivative - N * D.derivative = 0 := by
    calc
      D * N.derivative - N * D.derivative =
          S.s ^ 7 *
            ((3 : k[X]) * S.s ^ 4 * (S.p.coeff 5).derivative -
                (15 : k[X]) * S.s ^ 3 * S.p.coeff 5 * S.s.derivative -
              (2 : k[X]) * S.s * (S.q.coeff 8).derivative +
                (16 : k[X]) * S.q.coeff 8 * S.s.derivative) := by
            dsimp only [N, D]
            simp only [derivative_sub, derivative_mul, derivative_pow,
              derivative_ofNat, zero_mul, zero_add, C_eq_natCast]
            ring
      _ = 0 := by rw [S.firstRow, mul_zero]
  rw [← map_mul, ← map_mul, ← map_sub, hnumerator, map_zero, zero_div]

/-- The alignment discriminator is therefore an actual base-field
constant, derived from the literal polynomial source. -/
theorem alignmentConstant
    {k : Type u} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    ∃ delta : k, 3 * S.A - 2 * S.B = algebraMap k (RatFunc k) delta := by
  exact GCD369CubeRatFuncConstants _ S.alignmentDerivative_zero

end GCD369CubePolynomialSource

#print axioms GCD369CubeNextJacobianRow
#print axioms GCD369CubeRatFuncJacobian_comp
#print axioms GCD369CubeRatFuncJacobian_coeff
#print axioms GCD369CubeFaberNine_highRows
#print axioms GCD369CubeFaberEight_highRows
#print axioms GCD369CubeFaberSeven_highRows
#print axioms GCD369CubeFaberSix_highRows
#print axioms GCD369CubeFaberFive_highRows
#print axioms GCD369CubeFaberFour_highRows
#print axioms GCD369CubeFaberThree_highRows
#print axioms GCD369CubeFaberTwo_highRows
#print axioms GCD369CubeFaberOne_highRows
#print axioms GCD369CubeFaberZero_highRows
#print axioms GCD369CubePolynomialSource.pRat_qRat_jacobian
#print axioms GCD369CubePolynomialSource.normalizedP_eq_depressed
#print axioms GCD369CubePolynomialSource.normalized_jacobian
#print axioms GCD369CubePolynomialSource.firstRow
#print axioms GCD369CubePolynomialSource.alignmentPresentation
#print axioms GCD369CubePolynomialSource.alignmentDerivative_zero
#print axioms GCD369CubePolynomialSource.alignmentConstant
