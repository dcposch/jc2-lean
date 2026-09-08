import LowScale68Infinity

/-! # Polynomial weighted-boundary bridge for `(6,8)`

At common scale zero, all depressed coefficients are literal polynomials in
the source coordinate.  This module begins the source-honest passage from the
three remaining polynomial one-form rows to the scalar system eliminated in
`LowScale68Infinity`.

The integer `n` below is a common weighted radius.  The five sextic loads
`A,B,C,D,E` have bounds `2n,3n,4n,5n,6n`; the four octic coefficients used by
the lower rows have bounds `5n,6n,7n,8n`.  Coefficients at the boundary are
multiplicative under precisely these bounds, so no Laurent-series machinery
is needed in the scale-zero branch.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section PolynomialBoundary68

variable {k : Type*} [Field k] [CharZero k]

/-- The polynomial version of the integrated septic coefficient. -/
def integratedSPolynomial68
    (l alpha beta delta : k) (A B C0 D : k[X]) : k[X] :=
  (4 / 3 : k) • D + (4 / 9 : k) • (A * B) +
    l • ((7 / 6 : k) • C0 + (7 / 72 : k) • A ^ 2) +
    alpha • B + (5 / 6 * beta : k) • A + C delta

/-- The polynomial version of the integrated sextic coefficient. -/
def integratedTPolynomial68
    (l alpha beta gamma epsilon : k) (A B C0 D E : k[X]) : k[X] :=
  (4 / 3 : k) • E + (2 / 9 : k) • B ^ 2 +
    (4 / 9 : k) • (A * C0) - (4 / 81 : k) • A ^ 3 +
    l • ((7 / 6 : k) • D + (7 / 36 : k) • (A * B)) +
    alpha • C0 + (5 / 6 * beta : k) • B +
    (2 / 3 * gamma : k) • A + C epsilon

/-- The polynomial version of the integrated linear coefficient. -/
def integratedUPolynomial68
    (l alpha beta gamma delta zeta : k)
    (A B C0 D E : k[X]) : k[X] :=
  (4 / 9 : k) • (B * C0) + (4 / 9 : k) • (A * D) -
    (4 / 27 : k) • (A ^ 2 * B) +
    l • ((7 / 6 : k) • E + (7 / 72 : k) • B ^ 2 +
      (7 / 36 : k) • (A * C0) - (35 / 1296 : k) • A ^ 3) +
    alpha • D + beta • ((5 / 6 : k) • C0 - (5 / 72 : k) • A ^ 2) +
    (2 / 3 * gamma : k) • B + (1 / 2 * delta : k) • A + C zeta

/-- The polynomial version of the integrated constant coefficient. -/
def integratedVPolynomial68
    (l alpha beta gamma delta epsilon eta : k)
    (A B C0 D E : k[X]) : k[X] :=
  (2 / 9 : k) • C0 ^ 2 + (4 / 9 : k) • (B * D) +
    (4 / 9 : k) • (A * E) - (4 / 27 : k) • (A * B ^ 2) -
    (4 / 27 : k) • (A ^ 2 * C0) + (5 / 243 : k) • A ^ 4 +
    l • ((7 / 36 : k) • (B * C0) + (7 / 36 : k) • (A * D) -
      (35 / 432 : k) • (A ^ 2 * B)) +
    alpha • E + beta • ((5 / 6 : k) • D - (5 / 36 : k) • (A * B)) +
    gamma • ((2 / 3 : k) • C0 - (1 / 9 : k) • A ^ 2) +
    (1 / 2 * delta : k) • B + (1 / 3 * epsilon : k) • A + C eta

/-- Polynomial representative of the first exact lower-row invariant. -/
def firstIntegralFourPolynomial68
    (l beta gamma delta epsilon zeta : k)
    (A B C0 D E : k[X]) : k[X] :=
  (-8 / 27 : k) • B ^ 3 + zeta • A + (2 * epsilon : k) • B +
    (3 * delta : k) • C0 + (4 * gamma : k) • D + (5 * beta : k) • E -
    (8 / 9 : k) • (A ^ 2 * D) - (5 / 12 * beta : k) • B ^ 2 -
    (3 / 4 * delta : k) • A ^ 2 + (7 / 12 * l : k) • C0 ^ 2 +
    (8 / 3 : k) • (B * E) + (8 / 3 : k) • (C0 * D) +
    (35 / 216 * beta : k) • A ^ 3 + (40 / 81 : k) • (A ^ 3 * B) +
    (385 / 5184 * l : k) • A ^ 4 -
    (35 / 72 * l : k) • (A * B ^ 2) -
    (35 / 72 * l : k) • (A ^ 2 * C0) -
    (16 / 9 : k) • (A * B * C0) -
    (5 / 6 * beta : k) • (A * C0) -
    (4 / 3 * gamma : k) • (A * B) +
    (7 / 6 * l : k) • (A * E) + (7 / 6 * l : k) • (B * D)

/-- Polynomial representative of the second exact lower-row invariant. -/
def firstIntegralThreePolynomial68
    (l beta gamma delta epsilon zeta : k)
    (A B C0 D E : k[X]) : k[X] :=
  (-16 / 243 : k) • A ^ 5 + (4 / 3 : k) • D ^ 2 + zeta • B +
    (2 * epsilon : k) • C0 + (3 * delta : k) • D +
    (4 * gamma : k) • E - (35 / 216 * l : k) • B ^ 3 -
    (8 / 9 : k) • (A * C0 ^ 2) - (8 / 9 : k) • (B ^ 2 * C0) -
    (8 / 9 : k) • (A ^ 2 * E) - (2 / 3 * epsilon : k) • A ^ 2 -
    (2 / 3 * gamma : k) • B ^ 2 + (8 / 3 : k) • (C0 * E) +
    (8 / 27 * gamma : k) • A ^ 3 + (20 / 27 : k) • (A ^ 2 * B ^ 2) +
    (40 / 81 : k) • (A ^ 3 * C0) - (35 / 72 * l : k) • (A ^ 2 * D) -
    (16 / 9 : k) • (A * B * D) - (5 / 6 * beta : k) • (A * D) -
    (5 / 6 * beta : k) • (B * C0) - (4 / 3 * gamma : k) • (A * C0) -
    (3 / 2 * delta : k) • (A * B) + (7 / 6 * l : k) • (B * E) +
    (7 / 6 * l : k) • (C0 * D) + (35 / 72 * beta : k) • (A ^ 2 * B) +
    (385 / 1296 * l : k) • (A ^ 3 * B) -
    (35 / 36 * l : k) • (A * B * C0)

/-- Polynomial pullback of the first irreducible one-form row. -/
def lowerRowTwoPolynomial68
    (S T U V B C0 D E : k[X]) : k[X] :=
  U * derivative C0 + (2 : k) • (T * derivative D) +
    (3 : k) • (S * derivative E) - (3 : k) • (B * derivative V) -
    (2 : k) • (C0 * derivative U) - D * derivative T

/-- Polynomial pullback of the second irreducible one-form row. -/
def lowerRowOnePolynomial68
    (T U V C0 D E : k[X]) : k[X] :=
  U * derivative D + (2 : k) • (T * derivative E) -
    (2 : k) • (C0 * derivative V) - D * derivative U

/-- Polynomial pullback of the terminal one-form row. -/
def lowerRowZeroPolynomial68 (U V D E : k[X]) : k[X] :=
  U * derivative E - D * derivative V

/-- The polynomial integrated coefficients map to the differential-field
formulas used by the source bridge. -/
theorem algebraMap_integratedSPolynomial68
    (l alpha beta delta : k) (A B C0 D : k[X]) :
    algebraMap k[X] (RatFunc k)
        (integratedSPolynomial68 l alpha beta delta A B C0 D) =
      integratedS68 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta) := by
  simp only [integratedSPolynomial68, integratedS68, map_add, map_sub,
    Polynomial.smul_eq_C_mul, map_mul, map_pow, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

theorem algebraMap_integratedTPolynomial68
    (l alpha beta gamma epsilon : k) (A B C0 D E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E) =
      integratedT68 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D)
        (algebraMap k[X] (RatFunc k) E)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C epsilon) := by
  simp only [integratedTPolynomial68, integratedT68, map_add, map_sub,
    Polynomial.smul_eq_C_mul, map_mul, map_pow, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

theorem algebraMap_integratedUPolynomial68
    (l alpha beta gamma delta zeta : k) (A B C0 D E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E) =
      integratedU68 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D)
        (algebraMap k[X] (RatFunc k) E)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C zeta) := by
  simp only [integratedUPolynomial68, integratedU68, map_add, map_sub,
    Polynomial.smul_eq_C_mul, map_mul, map_pow, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

theorem algebraMap_integratedVPolynomial68
    (l alpha beta gamma delta epsilon eta : k) (A B C0 D E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          A B C0 D E) =
      integratedV68 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D)
        (algebraMap k[X] (RatFunc k) E)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C eta) := by
  simp only [integratedVPolynomial68, integratedV68, map_add, map_sub,
    Polynomial.smul_eq_C_mul, map_mul, map_pow, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

theorem algebraMap_firstIntegralFourPolynomial68
    (l beta gamma delta epsilon zeta : k) (A B C0 D E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
          A B C0 D E) =
      firstIntegralFour68 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D)
        (algebraMap k[X] (RatFunc k) E)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) := by
  simp only [firstIntegralFourPolynomial68, firstIntegralFour68, map_add,
    map_sub, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

theorem algebraMap_firstIntegralThreePolynomial68
    (l beta gamma delta epsilon zeta : k) (A B C0 D E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
          A B C0 D E) =
      firstIntegralThree68 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D)
        (algebraMap k[X] (RatFunc k) E)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) := by
  simp only [firstIntegralThreePolynomial68, firstIntegralThree68, map_add,
    map_sub, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

/-- The three polynomial one-form rows map exactly to the three remaining
rational-function rows. -/
theorem algebraMap_lowerRowTwoPolynomial68
    (S T U V B C0 D E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (lowerRowTwoPolynomial68 S T U V B C0 D E) =
      algebraMap k[X] (RatFunc k) U *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) C0) +
        2 * algebraMap k[X] (RatFunc k) T *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) D) +
        3 * algebraMap k[X] (RatFunc k) S *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) E) -
        3 * algebraMap k[X] (RatFunc k) B *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) V) -
        2 * algebraMap k[X] (RatFunc k) C0 *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) U) -
        algebraMap k[X] (RatFunc k) D *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) T) := by
  rw [show ratFuncDerivation68 = ratFuncDerivation46 from rfl]
  rw [ratFuncDerivation46_polynomial, ratFuncDerivation46_polynomial,
    ratFuncDerivation46_polynomial, ratFuncDerivation46_polynomial,
    ratFuncDerivation46_polynomial, ratFuncDerivation46_polynomial]
  simp only [lowerRowTwoPolynomial68, Polynomial.smul_eq_C_mul, map_add,
    map_sub, map_mul, RatFunc.algebraMap_C]
  simp only [map_ofNat]
  ring

theorem algebraMap_lowerRowOnePolynomial68
    (T U V C0 D E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (lowerRowOnePolynomial68 T U V C0 D E) =
      algebraMap k[X] (RatFunc k) U *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) D) +
        2 * algebraMap k[X] (RatFunc k) T *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) E) -
        2 * algebraMap k[X] (RatFunc k) C0 *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) V) -
        algebraMap k[X] (RatFunc k) D *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) U) := by
  rw [show ratFuncDerivation68 = ratFuncDerivation46 from rfl]
  rw [ratFuncDerivation46_polynomial, ratFuncDerivation46_polynomial,
    ratFuncDerivation46_polynomial, ratFuncDerivation46_polynomial]
  simp only [lowerRowOnePolynomial68, Polynomial.smul_eq_C_mul, map_add,
    map_sub, map_mul, RatFunc.algebraMap_C]
  simp only [map_ofNat]
  ring

theorem algebraMap_lowerRowZeroPolynomial68 (U V D E : k[X]) :
    algebraMap k[X] (RatFunc k) (lowerRowZeroPolynomial68 U V D E) =
      algebraMap k[X] (RatFunc k) U *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) E) -
        algebraMap k[X] (RatFunc k) D *
          ratFuncDerivation68 (algebraMap k[X] (RatFunc k) V) := by
  rw [show ratFuncDerivation68 = ratFuncDerivation46 from rfl]
  rw [ratFuncDerivation46_polynomial, ratFuncDerivation46_polynomial]
  simp only [lowerRowZeroPolynomial68, map_sub, map_mul]

/-- A product has the expected coefficient at an arbitrary weighted
boundary whenever the two factors satisfy their separate degree bounds. -/
theorem coeff_mul_weightedBoundary68
    (p q : k[X]) (u v n : ℕ)
    (hp : p.natDegree ≤ u * n) (hq : q.natDegree ≤ v * n) :
    (p * q).coeff ((u + v) * n) =
      p.coeff (u * n) * q.coeff (v * n) := by
  simpa [Nat.add_mul] using coeff_mul_add_eq_of_natDegree_le hp hq

/-- A power has the expected coefficient at an arbitrary weighted
boundary. -/
theorem coeff_pow_weightedBoundary68
    (p : k[X]) (u m n : ℕ) (hp : p.natDegree ≤ u * n) :
    (p ^ m).coeff ((m * u) * n) = p.coeff (u * n) ^ m := by
  simpa [Nat.mul_assoc] using (coeff_pow_of_natDegree_le (m := m) hp)

/-- A term of strictly smaller weight has zero coefficient at a higher
positive weighted boundary. -/
theorem coeff_weightedBoundary_eq_zero68
    (p : k[X]) (u v n : ℕ) (hn : 0 < n) (huv : u < v)
    (hp : p.natDegree ≤ u * n) :
    p.coeff (v * n) = 0 := by
  exact coeff_eq_zero_of_natDegree_lt (hp.trans_lt (by nlinarith))

/-- Coefficient of a derivative at the top of a positive weighted
boundary. -/
theorem coeff_derivative_weightedBoundary68
    (p : k[X]) (u n : ℕ) (hu : 0 < u) (hn : 0 < n) :
    (derivative p).coeff (u * n - 1) =
      p.coeff (u * n) * (u * n : ℕ) := by
  have hun : 0 < u * n := Nat.mul_pos hu hn
  rw [coeff_derivative]
  have hindex : u * n - 1 + 1 = u * n := by omega
  rw [hindex]
  have hcast : (↑(u * n - 1) + 1 : k) = ↑(u * n) := by
    exact_mod_cast hindex
  rw [hcast]

/-- The top coefficient of `p*q'` is the product of the two boundary
coefficients times the weighted derivative exponent. -/
theorem coeff_mul_derivative_weightedBoundary68
    (p q : k[X]) (u v n : ℕ) (hv : 0 < v) (hn : 0 < n)
    (hp : p.natDegree ≤ u * n) (hq : q.natDegree ≤ v * n) :
    (p * derivative q).coeff ((u + v) * n - 1) =
      p.coeff (u * n) * q.coeff (v * n) * (v * n : ℕ) := by
  have hdq : (derivative q).natDegree ≤ v * n - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have hmul := coeff_mul_add_eq_of_natDegree_le hp hdq
  rw [coeff_derivative_weightedBoundary68 q v n hv hn] at hmul
  have hvn : 0 < v * n := Nat.mul_pos hv hn
  have hindex : (u + v) * n - 1 = u * n + (v * n - 1) := by
    rw [Nat.add_mul]
    omega
  rw [hindex]
  simpa [mul_assoc] using hmul

/-- The top coefficient of the integrated septic coefficient is independent
of every ground-field integration load. -/
theorem integratedSPolynomial68_topCoeff
    (l alpha beta delta : k) (A B C0 D : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC : C0.natDegree ≤ 4 * n) (hD : D.natDegree ≤ 5 * n) :
    (integratedSPolynomial68 l alpha beta delta A B C0 D).coeff (5 * n) =
      (4 / 3 : k) * D.coeff (5 * n) +
        (4 / 9 : k) * A.coeff (2 * n) * B.coeff (3 * n) := by
  have hAB := coeff_mul_weightedBoundary68 A B 2 3 n hA hB
  have hC5 := coeff_weightedBoundary_eq_zero68 C0 4 5 n hn (by omega) hC
  have hA2 : (A ^ 2).natDegree ≤ 4 * n := by
    exact natDegree_pow_le.trans (by nlinarith)
  have hA25 := coeff_weightedBoundary_eq_zero68 (A ^ 2) 4 5 n hn
    (by omega) hA2
  have hB5 := coeff_weightedBoundary_eq_zero68 B 3 5 n hn (by omega) hB
  have hA5 := coeff_weightedBoundary_eq_zero68 A 2 5 n hn (by omega) hA
  have hCconst : (C delta : k[X]).coeff (5 * n) = 0 := by
    rw [coeff_C]
    split_ifs with h
    · omega
    · rfl
  simp only [integratedSPolynomial68, coeff_add, coeff_sub, coeff_smul,
    hAB, hC5, hA25, hB5, hA5, hCconst, mul_zero, add_zero, sub_zero,
    smul_eq_mul]
  ring

/-- The top coefficient of the integrated sextic coefficient. -/
theorem integratedTPolynomial68_topCoeff
    (l alpha beta gamma epsilon : k) (A B C0 D E : k[X])
    (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC : C0.natDegree ≤ 4 * n) (hD : D.natDegree ≤ 5 * n)
    (hE : E.natDegree ≤ 6 * n) :
    (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E).coeff
        (6 * n) =
      (4 / 3 : k) * E.coeff (6 * n) +
      (2 / 9 : k) * B.coeff (3 * n) ^ 2 +
      (4 / 9 : k) * A.coeff (2 * n) * C0.coeff (4 * n) -
      (4 / 81 : k) * A.coeff (2 * n) ^ 3 := by
  have hB2 := coeff_pow_weightedBoundary68 B 3 2 n hB
  have hAC := coeff_mul_weightedBoundary68 A C0 2 4 n hA hC
  have hA3 := coeff_pow_weightedBoundary68 A 2 3 n hA
  have hD6 := coeff_weightedBoundary_eq_zero68 D 5 6 n hn (by omega) hD
  have hABdeg : (A * B).natDegree ≤ 5 * n := by
    exact natDegree_mul_le.trans (by nlinarith)
  have hAB6 := coeff_weightedBoundary_eq_zero68 (A * B) 5 6 n hn
    (by omega) hABdeg
  have hC6 := coeff_weightedBoundary_eq_zero68 C0 4 6 n hn (by omega) hC
  have hB6 := coeff_weightedBoundary_eq_zero68 B 3 6 n hn (by omega) hB
  have hA6 := coeff_weightedBoundary_eq_zero68 A 2 6 n hn (by omega) hA
  have hconst : (C epsilon : k[X]).coeff (6 * n) = 0 := by
    rw [coeff_C]
    split_ifs with h
    · omega
    · rfl
  simp only [integratedTPolynomial68, coeff_add, coeff_sub, coeff_smul,
    hB2, hAC, hA3, hD6, hAB6, hC6, hB6, hA6, hconst, mul_zero,
    add_zero, sub_zero, smul_eq_mul]
  ring

/-- The top coefficient of the integrated linear octic coefficient. -/
theorem integratedUPolynomial68_topCoeff
    (l alpha beta gamma delta zeta : k) (A B C0 D E : k[X])
    (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC : C0.natDegree ≤ 4 * n) (hD : D.natDegree ≤ 5 * n)
    (hE : E.natDegree ≤ 6 * n) :
    (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E).coeff
        (7 * n) =
      (4 / 9 : k) * B.coeff (3 * n) * C0.coeff (4 * n) +
      (4 / 9 : k) * A.coeff (2 * n) * D.coeff (5 * n) -
      (4 / 27 : k) * A.coeff (2 * n) ^ 2 * B.coeff (3 * n) := by
  have hBC := coeff_mul_weightedBoundary68 B C0 3 4 n hB hC
  have hAD := coeff_mul_weightedBoundary68 A D 2 5 n hA hD
  have hA2 : (A ^ 2).natDegree ≤ 4 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hA2B := coeff_mul_weightedBoundary68 (A ^ 2) B 4 3 n hA2 hB
  have hA2c := coeff_pow_weightedBoundary68 A 2 2 n hA
  have hlower (p : k[X]) (u : ℕ) (hu : u < 7)
      (hp : p.natDegree ≤ u * n) : p.coeff (7 * n) = 0 :=
    coeff_weightedBoundary_eq_zero68 p u 7 n hn hu hp
  have hE7 := hlower E 6 (by omega) hE
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hB27 := hlower (B ^ 2) 6 (by omega) hB2deg
  have hACdeg : (A * C0).natDegree ≤ 6 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hAC7 := hlower (A * C0) 6 (by omega) hACdeg
  have hA3deg : (A ^ 3).natDegree ≤ 6 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hA37 := hlower (A ^ 3) 6 (by omega) hA3deg
  have hD7 := hlower D 5 (by omega) hD
  have hC7 := hlower C0 4 (by omega) hC
  have hA27 := hlower (A ^ 2) 4 (by omega) hA2
  have hB7 := hlower B 3 (by omega) hB
  have hA7 := hlower A 2 (by omega) hA
  have hconst : (C zeta : k[X]).coeff (7 * n) = 0 := by
    rw [coeff_C]
    split_ifs with h
    · omega
    · rfl
  simp only [integratedUPolynomial68, coeff_add, coeff_sub, coeff_smul,
    hBC, hAD, hA2B, hA2c, hE7, hB27, hAC7, hA37, hD7, hC7,
    hA27, hB7, hA7, hconst, mul_zero, add_zero, sub_zero, smul_eq_mul]
  ring

/-- The top coefficient of the integrated constant octic coefficient. -/
theorem integratedVPolynomial68_topCoeff
    (l alpha beta gamma delta epsilon eta : k) (A B C0 D E : k[X])
    (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC : C0.natDegree ≤ 4 * n) (hD : D.natDegree ≤ 5 * n)
    (hE : E.natDegree ≤ 6 * n) :
    (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E).coeff (8 * n) =
      (2 / 9 : k) * C0.coeff (4 * n) ^ 2 +
      (4 / 9 : k) * B.coeff (3 * n) * D.coeff (5 * n) +
      (4 / 9 : k) * A.coeff (2 * n) * E.coeff (6 * n) -
      (4 / 27 : k) * A.coeff (2 * n) * B.coeff (3 * n) ^ 2 -
      (4 / 27 : k) * A.coeff (2 * n) ^ 2 * C0.coeff (4 * n) +
      (5 / 243 : k) * A.coeff (2 * n) ^ 4 := by
  have hC2 := coeff_pow_weightedBoundary68 C0 4 2 n hC
  have hBD := coeff_mul_weightedBoundary68 B D 3 5 n hB hD
  have hAE := coeff_mul_weightedBoundary68 A E 2 6 n hA hE
  have hB2 : (B ^ 2).natDegree ≤ 6 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hAB2 := coeff_mul_weightedBoundary68 A (B ^ 2) 2 6 n hA hB2
  have hB2c := coeff_pow_weightedBoundary68 B 3 2 n hB
  have hA2 : (A ^ 2).natDegree ≤ 4 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hA2C := coeff_mul_weightedBoundary68 (A ^ 2) C0 4 4 n hA2 hC
  have hA2c := coeff_pow_weightedBoundary68 A 2 2 n hA
  have hA4 := coeff_pow_weightedBoundary68 A 2 4 n hA
  have hlower (p : k[X]) (u : ℕ) (hu : u < 8)
      (hp : p.natDegree ≤ u * n) : p.coeff (8 * n) = 0 :=
    coeff_weightedBoundary_eq_zero68 p u 8 n hn hu hp
  have hBCdeg : (B * C0).natDegree ≤ 7 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hBC8 := hlower (B * C0) 7 (by omega) hBCdeg
  have hADdeg : (A * D).natDegree ≤ 7 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hAD8 := hlower (A * D) 7 (by omega) hADdeg
  have hA2Bdeg : (A ^ 2 * B).natDegree ≤ 7 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hA2B8 := hlower (A ^ 2 * B) 7 (by omega) hA2Bdeg
  have hE8 := hlower E 6 (by omega) hE
  have hD8 := hlower D 5 (by omega) hD
  have hABdeg : (A * B).natDegree ≤ 5 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hAB8 := hlower (A * B) 5 (by omega) hABdeg
  have hC8 := hlower C0 4 (by omega) hC
  have hA28 := hlower (A ^ 2) 4 (by omega) hA2
  have hB8 := hlower B 3 (by omega) hB
  have hA8 := hlower A 2 (by omega) hA
  have hconst : (C eta : k[X]).coeff (8 * n) = 0 := by
    rw [coeff_C]
    split_ifs with h
    · omega
    · rfl
  simp only [integratedVPolynomial68, coeff_add, coeff_sub, coeff_smul,
    hC2, hBD, hAE, hAB2, hB2c, hA2C, hA2c, hA4, hBC8, hAD8,
    hA2B8, hE8, hD8, hAB8, hC8, hA28, hB8, hA8, hconst,
    mul_zero, add_zero, sub_zero, smul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in
/-- The first irreducible one-form row extracts `topRowTwo68` at its weighted
boundary. -/
theorem lowerRowTwoPolynomial68_topCoeff
    (A B C0 D E S T U V : k[X]) (n : ℕ) (hn : 0 < n)
    (hB : B.natDegree ≤ 3 * n) (hC : C0.natDegree ≤ 4 * n)
    (hD : D.natDegree ≤ 5 * n) (hE : E.natDegree ≤ 6 * n)
    (hSdeg : S.natDegree ≤ 5 * n) (hTdeg : T.natDegree ≤ 6 * n)
    (hUdeg : U.natDegree ≤ 7 * n) (hVdeg : V.natDegree ≤ 8 * n)
    (hS : S.coeff (5 * n) =
      (4 / 3 : k) * D.coeff (5 * n) +
        (4 / 9 : k) * A.coeff (2 * n) * B.coeff (3 * n))
    (hT : T.coeff (6 * n) =
      (4 / 3 : k) * E.coeff (6 * n) +
      (2 / 9 : k) * B.coeff (3 * n) ^ 2 +
      (4 / 9 : k) * A.coeff (2 * n) * C0.coeff (4 * n) -
      (4 / 81 : k) * A.coeff (2 * n) ^ 3)
    (hU : U.coeff (7 * n) =
      (4 / 9 : k) * B.coeff (3 * n) * C0.coeff (4 * n) +
      (4 / 9 : k) * A.coeff (2 * n) * D.coeff (5 * n) -
      (4 / 27 : k) * A.coeff (2 * n) ^ 2 * B.coeff (3 * n))
    (hV : V.coeff (8 * n) =
      (2 / 9 : k) * C0.coeff (4 * n) ^ 2 +
      (4 / 9 : k) * B.coeff (3 * n) * D.coeff (5 * n) +
      (4 / 9 : k) * A.coeff (2 * n) * E.coeff (6 * n) -
      (4 / 27 : k) * A.coeff (2 * n) * B.coeff (3 * n) ^ 2 -
      (4 / 27 : k) * A.coeff (2 * n) ^ 2 * C0.coeff (4 * n) +
      (5 / 243 : k) * A.coeff (2 * n) ^ 4) :
    (lowerRowTwoPolynomial68 S T U V B C0 D E).coeff (11 * n - 1) =
      (-8 / 81 : k) * (n : k) * topRowTwo68
        (A.coeff (2 * n)) (B.coeff (3 * n)) (C0.coeff (4 * n))
        (D.coeff (5 * n)) (E.coeff (6 * n)) := by
  have hUC := coeff_mul_derivative_weightedBoundary68 U C0 7 4 n
    (by omega) hn hUdeg hC
  have hTD := coeff_mul_derivative_weightedBoundary68 T D 6 5 n
    (by omega) hn hTdeg hD
  have hSE := coeff_mul_derivative_weightedBoundary68 S E 5 6 n
    (by omega) hn hSdeg hE
  have hBV := coeff_mul_derivative_weightedBoundary68 B V 3 8 n
    (by omega) hn hB hVdeg
  have hCU := coeff_mul_derivative_weightedBoundary68 C0 U 4 7 n
    (by omega) hn hC hUdeg
  have hDT := coeff_mul_derivative_weightedBoundary68 D T 5 6 n
    (by omega) hn hD hTdeg
  simp only [lowerRowTwoPolynomial68, coeff_add, coeff_sub, coeff_smul,
    hUC, hTD, hSE, hBV, hCU, hDT, smul_eq_mul]
  rw [hS, hT, hU, hV]
  simp only [topRowTwo68]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- The second irreducible one-form row extracts `topRowOne68`. -/
theorem lowerRowOnePolynomial68_topCoeff
    (A B C0 D E T U V : k[X]) (n : ℕ) (hn : 0 < n)
    (hC : C0.natDegree ≤ 4 * n) (hD : D.natDegree ≤ 5 * n)
    (hE : E.natDegree ≤ 6 * n) (hTdeg : T.natDegree ≤ 6 * n)
    (hUdeg : U.natDegree ≤ 7 * n) (hVdeg : V.natDegree ≤ 8 * n)
    (hT : T.coeff (6 * n) =
      (4 / 3 : k) * E.coeff (6 * n) +
      (2 / 9 : k) * B.coeff (3 * n) ^ 2 +
      (4 / 9 : k) * A.coeff (2 * n) * C0.coeff (4 * n) -
      (4 / 81 : k) * A.coeff (2 * n) ^ 3)
    (hU : U.coeff (7 * n) =
      (4 / 9 : k) * B.coeff (3 * n) * C0.coeff (4 * n) +
      (4 / 9 : k) * A.coeff (2 * n) * D.coeff (5 * n) -
      (4 / 27 : k) * A.coeff (2 * n) ^ 2 * B.coeff (3 * n))
    (hV : V.coeff (8 * n) =
      (2 / 9 : k) * C0.coeff (4 * n) ^ 2 +
      (4 / 9 : k) * B.coeff (3 * n) * D.coeff (5 * n) +
      (4 / 9 : k) * A.coeff (2 * n) * E.coeff (6 * n) -
      (4 / 27 : k) * A.coeff (2 * n) * B.coeff (3 * n) ^ 2 -
      (4 / 27 : k) * A.coeff (2 * n) ^ 2 * C0.coeff (4 * n) +
      (5 / 243 : k) * A.coeff (2 * n) ^ 4) :
    (lowerRowOnePolynomial68 T U V C0 D E).coeff (12 * n - 1) =
      (-8 / 243 : k) * (n : k) * topRowOne68
        (A.coeff (2 * n)) (B.coeff (3 * n)) (C0.coeff (4 * n))
        (D.coeff (5 * n)) (E.coeff (6 * n)) := by
  have hUD := coeff_mul_derivative_weightedBoundary68 U D 7 5 n
    (by omega) hn hUdeg hD
  have hTE := coeff_mul_derivative_weightedBoundary68 T E 6 6 n
    (by omega) hn hTdeg hE
  have hCV := coeff_mul_derivative_weightedBoundary68 C0 V 4 8 n
    (by omega) hn hC hVdeg
  have hDU := coeff_mul_derivative_weightedBoundary68 D U 5 7 n
    (by omega) hn hD hUdeg
  simp only [lowerRowOnePolynomial68, coeff_add, coeff_sub, coeff_smul,
    hUD, hTE, hCV, hDU, smul_eq_mul]
  rw [hT, hU, hV]
  simp only [topRowOne68]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- The terminal one-form row extracts `topRowZero68`. -/
theorem lowerRowZeroPolynomial68_topCoeff
    (A B C0 D E U V : k[X]) (n : ℕ) (hn : 0 < n)
    (hD : D.natDegree ≤ 5 * n) (hE : E.natDegree ≤ 6 * n)
    (hUdeg : U.natDegree ≤ 7 * n) (hVdeg : V.natDegree ≤ 8 * n)
    (hU : U.coeff (7 * n) =
      (4 / 9 : k) * B.coeff (3 * n) * C0.coeff (4 * n) +
      (4 / 9 : k) * A.coeff (2 * n) * D.coeff (5 * n) -
      (4 / 27 : k) * A.coeff (2 * n) ^ 2 * B.coeff (3 * n))
    (hV : V.coeff (8 * n) =
      (2 / 9 : k) * C0.coeff (4 * n) ^ 2 +
      (4 / 9 : k) * B.coeff (3 * n) * D.coeff (5 * n) +
      (4 / 9 : k) * A.coeff (2 * n) * E.coeff (6 * n) -
      (4 / 27 : k) * A.coeff (2 * n) * B.coeff (3 * n) ^ 2 -
      (4 / 27 : k) * A.coeff (2 * n) ^ 2 * C0.coeff (4 * n) +
      (5 / 243 : k) * A.coeff (2 * n) ^ 4) :
    (lowerRowZeroPolynomial68 U V D E).coeff (13 * n - 1) =
      (-8 / 243 : k) * (n : k) * topRowZero68
        (A.coeff (2 * n)) (B.coeff (3 * n)) (C0.coeff (4 * n))
        (D.coeff (5 * n)) (E.coeff (6 * n)) := by
  have hUE := coeff_mul_derivative_weightedBoundary68 U E 7 6 n
    (by omega) hn hUdeg hE
  have hDV := coeff_mul_derivative_weightedBoundary68 D V 5 8 n
    (by omega) hn hD hVdeg
  simp only [lowerRowZeroPolynomial68, coeff_sub, hUE, hDV]
  rw [hU, hV]
  simp only [topRowZero68]
  push_cast
  ring

set_option maxHeartbeats 2000000 in
/-- The degree-nine boundary of the first exact invariant is the first
scalar top row, up to a nonzero normalization. -/
theorem firstIntegralFourPolynomial68_topCoeff
    (l beta gamma delta epsilon zeta : k) (A B C0 D E : k[X])
    (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC : C0.natDegree ≤ 4 * n) (hD : D.natDegree ≤ 5 * n)
    (hE : E.natDegree ≤ 6 * n) :
    (firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        A B C0 D E).coeff (9 * n) =
      (8 / 81 : k) * topRowFour68
        (A.coeff (2 * n)) (B.coeff (3 * n)) (C0.coeff (4 * n))
        (D.coeff (5 * n)) (E.coeff (6 * n)) := by
  let a := A.coeff (2 * n)
  let b := B.coeff (3 * n)
  let c := C0.coeff (4 * n)
  let d := D.coeff (5 * n)
  let e := E.coeff (6 * n)
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hA3deg : (A ^ 3).natDegree ≤ 6 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hA4deg : (A ^ 4).natDegree ≤ 8 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hC2deg : (C0 ^ 2).natDegree ≤ 8 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hB3 : (B ^ 3).coeff (9 * n) = b ^ 3 := by
    simpa [b] using coeff_pow_weightedBoundary68 B 3 3 n hB
  have hA2D : (A ^ 2 * D).coeff (9 * n) = a ^ 2 * d := by
    have h := coeff_mul_weightedBoundary68 (A ^ 2) D 4 5 n hA2deg hD
    rw [coeff_pow_weightedBoundary68 A 2 2 n hA] at h
    simpa [a, d] using h
  have hBE : (B * E).coeff (9 * n) = b * e := by
    simpa [b, e] using coeff_mul_weightedBoundary68 B E 3 6 n hB hE
  have hCD : (C0 * D).coeff (9 * n) = c * d := by
    simpa [c, d] using coeff_mul_weightedBoundary68 C0 D 4 5 n hC hD
  have hA3B : (A ^ 3 * B).coeff (9 * n) = a ^ 3 * b := by
    have h := coeff_mul_weightedBoundary68 (A ^ 3) B 6 3 n hA3deg hB
    rw [coeff_pow_weightedBoundary68 A 2 3 n hA] at h
    simpa [a, b] using h
  have hABdeg : (A * B).natDegree ≤ 5 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hABC : (A * B * C0).coeff (9 * n) = a * b * c := by
    have h := coeff_mul_weightedBoundary68 (A * B) C0 5 4 n hABdeg hC
    rw [coeff_mul_weightedBoundary68 A B 2 3 n hA hB] at h
    simpa [a, b, c] using h
  have lower (p : k[X]) (u : ℕ) (hu : u < 9)
      (hp : p.natDegree ≤ u * n) : p.coeff (9 * n) = 0 :=
    coeff_weightedBoundary_eq_zero68 p u 9 n hn hu hp
  have hA9 := lower A 2 (by omega) hA
  have hB9 := lower B 3 (by omega) hB
  have hC9 := lower C0 4 (by omega) hC
  have hD9 := lower D 5 (by omega) hD
  have hE9 := lower E 6 (by omega) hE
  have hB29 := lower (B ^ 2) 6 (by omega) hB2deg
  have hA29 := lower (A ^ 2) 4 (by omega) hA2deg
  have hC29 := lower (C0 ^ 2) 8 (by omega) hC2deg
  have hA39 := lower (A ^ 3) 6 (by omega) hA3deg
  have hA49 := lower (A ^ 4) 8 (by omega) hA4deg
  have hAB2deg : (A * B ^ 2).natDegree ≤ 8 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hAB29 := lower (A * B ^ 2) 8 (by omega) hAB2deg
  have hA2Cdeg : (A ^ 2 * C0).natDegree ≤ 8 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hA2C9 := lower (A ^ 2 * C0) 8 (by omega) hA2Cdeg
  have hACdeg : (A * C0).natDegree ≤ 6 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hAC9 := lower (A * C0) 6 (by omega) hACdeg
  have hAB9 := lower (A * B) 5 (by omega) hABdeg
  have hAEdeg : (A * E).natDegree ≤ 8 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hAE9 := lower (A * E) 8 (by omega) hAEdeg
  have hBDdeg : (B * D).natDegree ≤ 8 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hBD9 := lower (B * D) 8 (by omega) hBDdeg
  simp only [firstIntegralFourPolynomial68, coeff_add, coeff_sub, coeff_smul,
    hB3, hA9, hB9, hC9, hD9, hE9, hA2D, hB29, hA29, hC29,
    hBE, hCD, hA39, hA3B, hA49, hAB29, hA2C9, hABC, hAC9, hAB9,
    hAE9, hBD9, mul_zero, add_zero, sub_zero, smul_eq_mul]
  dsimp only [a, b, c, d, e]
  simp only [topRowFour68]
  ring

set_option maxHeartbeats 2000000 in
/-- The degree-ten boundary of the second exact invariant is the second
scalar top row, up to a nonzero normalization. -/
theorem firstIntegralThreePolynomial68_topCoeff
    (l beta gamma delta epsilon zeta : k) (A B C0 D E : k[X])
    (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC : C0.natDegree ≤ 4 * n) (hD : D.natDegree ≤ 5 * n)
    (hE : E.natDegree ≤ 6 * n) :
    (firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        A B C0 D E).coeff (10 * n) =
      (-4 / 243 : k) * topRowThree68
        (A.coeff (2 * n)) (B.coeff (3 * n)) (C0.coeff (4 * n))
        (D.coeff (5 * n)) (E.coeff (6 * n)) := by
  let a := A.coeff (2 * n)
  let b := B.coeff (3 * n)
  let c := C0.coeff (4 * n)
  let d := D.coeff (5 * n)
  let e := E.coeff (6 * n)
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hA3deg : (A ^ 3).natDegree ≤ 6 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hA5deg : (A ^ 5).natDegree ≤ 10 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hC2deg : (C0 ^ 2).natDegree ≤ 8 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hD2deg : (D ^ 2).natDegree ≤ 10 * n :=
    natDegree_pow_le.trans (by nlinarith)
  have hA5 : (A ^ 5).coeff (10 * n) = a ^ 5 := by
    simpa [a] using coeff_pow_weightedBoundary68 A 2 5 n hA
  have hD2 : (D ^ 2).coeff (10 * n) = d ^ 2 := by
    simpa [d] using coeff_pow_weightedBoundary68 D 5 2 n hD
  have hAC2 : (A * C0 ^ 2).coeff (10 * n) = a * c ^ 2 := by
    have h := coeff_mul_weightedBoundary68 A (C0 ^ 2) 2 8 n hA hC2deg
    rw [coeff_pow_weightedBoundary68 C0 4 2 n hC] at h
    simpa [a, c] using h
  have hB2C : (B ^ 2 * C0).coeff (10 * n) = b ^ 2 * c := by
    have h := coeff_mul_weightedBoundary68 (B ^ 2) C0 6 4 n hB2deg hC
    rw [coeff_pow_weightedBoundary68 B 3 2 n hB] at h
    simpa [b, c] using h
  have hA2E : (A ^ 2 * E).coeff (10 * n) = a ^ 2 * e := by
    have h := coeff_mul_weightedBoundary68 (A ^ 2) E 4 6 n hA2deg hE
    rw [coeff_pow_weightedBoundary68 A 2 2 n hA] at h
    simpa [a, e] using h
  have hCE : (C0 * E).coeff (10 * n) = c * e := by
    simpa [c, e] using coeff_mul_weightedBoundary68 C0 E 4 6 n hC hE
  have hA2B2 : (A ^ 2 * B ^ 2).coeff (10 * n) = a ^ 2 * b ^ 2 := by
    have h := coeff_mul_weightedBoundary68 (A ^ 2) (B ^ 2) 4 6 n
      hA2deg hB2deg
    rw [coeff_pow_weightedBoundary68 A 2 2 n hA,
      coeff_pow_weightedBoundary68 B 3 2 n hB] at h
    simpa [a, b] using h
  have hA3C : (A ^ 3 * C0).coeff (10 * n) = a ^ 3 * c := by
    have h := coeff_mul_weightedBoundary68 (A ^ 3) C0 6 4 n hA3deg hC
    rw [coeff_pow_weightedBoundary68 A 2 3 n hA] at h
    simpa [a, c] using h
  have hABdeg : (A * B).natDegree ≤ 5 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hABD : (A * B * D).coeff (10 * n) = a * b * d := by
    have h := coeff_mul_weightedBoundary68 (A * B) D 5 5 n hABdeg hD
    rw [coeff_mul_weightedBoundary68 A B 2 3 n hA hB] at h
    simpa [a, b, d] using h
  have lower (p : k[X]) (u : ℕ) (hu : u < 10)
      (hp : p.natDegree ≤ u * n) : p.coeff (10 * n) = 0 :=
    coeff_weightedBoundary_eq_zero68 p u 10 n hn hu hp
  have hB10 := lower B 3 (by omega) hB
  have hC10 := lower C0 4 (by omega) hC
  have hD10 := lower D 5 (by omega) hD
  have hE10 := lower E 6 (by omega) hE
  have hB310 := lower (B ^ 3) 9 (by omega) hB3deg
  have hA210 := lower (A ^ 2) 4 (by omega) hA2deg
  have hB210 := lower (B ^ 2) 6 (by omega) hB2deg
  have hA310 := lower (A ^ 3) 6 (by omega) hA3deg
  have hA2Ddeg : (A ^ 2 * D).natDegree ≤ 9 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hA2D10 := lower (A ^ 2 * D) 9 (by omega) hA2Ddeg
  have hADdeg : (A * D).natDegree ≤ 7 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hAD10 := lower (A * D) 7 (by omega) hADdeg
  have hBCdeg : (B * C0).natDegree ≤ 7 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hBC10 := lower (B * C0) 7 (by omega) hBCdeg
  have hACdeg : (A * C0).natDegree ≤ 6 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hAC10 := lower (A * C0) 6 (by omega) hACdeg
  have hAB10 := lower (A * B) 5 (by omega) hABdeg
  have hBEdeg : (B * E).natDegree ≤ 9 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hBE10 := lower (B * E) 9 (by omega) hBEdeg
  have hCDdeg : (C0 * D).natDegree ≤ 9 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hCD10 := lower (C0 * D) 9 (by omega) hCDdeg
  have hA2Bdeg : (A ^ 2 * B).natDegree ≤ 7 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hA2B10 := lower (A ^ 2 * B) 7 (by omega) hA2Bdeg
  have hA3Bdeg : (A ^ 3 * B).natDegree ≤ 9 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hA3B10 := lower (A ^ 3 * B) 9 (by omega) hA3Bdeg
  have hABCdeg : (A * B * C0).natDegree ≤ 9 * n :=
    natDegree_mul_le.trans (by nlinarith)
  have hABC10 := lower (A * B * C0) 9 (by omega) hABCdeg
  simp only [firstIntegralThreePolynomial68, coeff_add, coeff_sub, coeff_smul,
    hA5, hD2, hB10, hC10, hD10, hE10, hB310, hAC2, hB2C, hA2E,
    hA210, hB210, hCE, hA310, hA2B2, hA3C, hA2D10, hABD, hAD10,
    hBC10, hAC10, hAB10, hBE10, hCD10, hA2B10, hA3B10, hABC10,
    mul_zero, add_zero, sub_zero, smul_eq_mul]
  dsimp only [a, b, c, d, e]
  simp only [topRowThree68]
  ring

/-- The four integrated octic coefficients have exactly the boundary
coefficients used by the three lower one-form rows. -/
structure IntegratedBoundaryCoefficients68
    (A B C0 D E S T U V : k[X]) (n : ℕ) : Prop where
  s_eq : S.coeff (5 * n) =
    (4 / 3 : k) * D.coeff (5 * n) +
      (4 / 9 : k) * A.coeff (2 * n) * B.coeff (3 * n)
  t_eq : T.coeff (6 * n) =
    (4 / 3 : k) * E.coeff (6 * n) +
    (2 / 9 : k) * B.coeff (3 * n) ^ 2 +
    (4 / 9 : k) * A.coeff (2 * n) * C0.coeff (4 * n) -
    (4 / 81 : k) * A.coeff (2 * n) ^ 3
  u_eq : U.coeff (7 * n) =
    (4 / 9 : k) * B.coeff (3 * n) * C0.coeff (4 * n) +
    (4 / 9 : k) * A.coeff (2 * n) * D.coeff (5 * n) -
    (4 / 27 : k) * A.coeff (2 * n) ^ 2 * B.coeff (3 * n)
  v_eq : V.coeff (8 * n) =
    (2 / 9 : k) * C0.coeff (4 * n) ^ 2 +
    (4 / 9 : k) * B.coeff (3 * n) * D.coeff (5 * n) +
    (4 / 9 : k) * A.coeff (2 * n) * E.coeff (6 * n) -
    (4 / 27 : k) * A.coeff (2 * n) * B.coeff (3 * n) ^ 2 -
    (4 / 27 : k) * A.coeff (2 * n) ^ 2 * C0.coeff (4 * n) +
    (5 / 243 : k) * A.coeff (2 * n) ^ 4

/-- The literal integrated polynomial formulas supply the complete boundary
coefficient package. -/
theorem integratedPolynomial68_boundaryCoefficients
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B C0 D E : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC : C0.natDegree ≤ 4 * n) (hD : D.natDegree ≤ 5 * n)
    (hE : E.natDegree ≤ 6 * n) :
    IntegratedBoundaryCoefficients68 A B C0 D E
      (integratedSPolynomial68 l alpha beta delta A B C0 D)
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) n := by
  exact ⟨
    integratedSPolynomial68_topCoeff l alpha beta delta A B C0 D n hn
      hA hB hC hD,
    integratedTPolynomial68_topCoeff l alpha beta gamma epsilon
      A B C0 D E n hn hA hB hC hD hE,
    integratedUPolynomial68_topCoeff l alpha beta gamma delta zeta
      A B C0 D E n hn hA hB hC hD hE,
    integratedVPolynomial68_topCoeff l alpha beta gamma delta epsilon eta
      A B C0 D E n hn hA hB hC hD hE⟩

set_option maxHeartbeats 2000000 in
/-- The four literal integrated polynomials satisfy their expected weighted
degree bounds. -/
theorem integratedPolynomial68_degreeBounds
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B C0 D E : k[X]) (n : ℕ)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC : C0.natDegree ≤ 4 * n) (hD : D.natDegree ≤ 5 * n)
    (hE : E.natDegree ≤ 6 * n) :
    (integratedSPolynomial68 l alpha beta delta A B C0 D).natDegree ≤ 5 * n ∧
    (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E).natDegree ≤
      6 * n ∧
    (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E).natDegree ≤
      7 * n ∧
    (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
      A B C0 D E).natDegree ≤ 8 * n := by
  simp only [integratedSPolynomial68, integratedTPolynomial68,
    integratedUPolynomial68, integratedVPolynomial68]
  constructor
  · compute_degree
    omega
  constructor
  · compute_degree
    omega
  constructor <;> compute_degree <;> omega

set_option maxHeartbeats 2000000 in
/-- Exact polynomial extraction of the complete scalar infinity system when
the terminal row has zero coefficient at the tested boundary.  Consequently
the five boundary coefficients have the unique depressed cubic-core shape. -/
theorem polynomialLowerSystem_cubicCore68_of_terminalCoeff_zero
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B C0 D E S T U V : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC : C0.natDegree ≤ 4 * n) (hD : D.natDegree ≤ 5 * n)
    (hE : E.natDegree ≤ 6 * n)
    (hSdeg : S.natDegree ≤ 5 * n) (hTdeg : T.natDegree ≤ 6 * n)
    (hUdeg : U.natDegree ≤ 7 * n) (hVdeg : V.natDegree ≤ 8 * n)
    (htop : IntegratedBoundaryCoefficients68 A B C0 D E S T U V n)
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3)
    (h2 : lowerRowTwoPolynomial68 S T U V B C0 D E = 0)
    (h1 : lowerRowOnePolynomial68 T U V C0 D E = 0)
    (h0top : (lowerRowZeroPolynomial68 U V D E).coeff (13 * n - 1) = 0) :
    B.coeff (3 * n) = 0 ∧ D.coeff (5 * n) = 0 ∧
      C0.coeff (4 * n) = A.coeff (2 * n) ^ 2 / 3 ∧
      E.coeff (6 * n) = A.coeff (2 * n) ^ 3 / 27 := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnk : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have h9 : 9 * n ≠ 0 := by omega
  have h10 : 10 * n ≠ 0 := by omega
  have hfour := congrArg (fun p : k[X] => p.coeff (9 * n)) hI4
  rw [firstIntegralFourPolynomial68_topCoeff l beta gamma delta epsilon zeta
    A B C0 D E n hn hA hB hC hD hE] at hfour
  simp [coeff_C, h9] at hfour
  have hrow4 : topRowFour68 (A.coeff (2 * n)) (B.coeff (3 * n))
      (C0.coeff (4 * n)) (D.coeff (5 * n)) (E.coeff (6 * n)) = 0 :=
    hfour
  have hthree := congrArg (fun p : k[X] => p.coeff (10 * n)) hI3
  rw [firstIntegralThreePolynomial68_topCoeff l beta gamma delta epsilon zeta
    A B C0 D E n hn hA hB hC hD hE] at hthree
  simp [coeff_C, h10] at hthree
  have hrow3 : topRowThree68 (A.coeff (2 * n)) (B.coeff (3 * n))
      (C0.coeff (4 * n)) (D.coeff (5 * n)) (E.coeff (6 * n)) = 0 :=
    hthree
  have htwo := congrArg (fun p : k[X] => p.coeff (11 * n - 1)) h2
  rw [lowerRowTwoPolynomial68_topCoeff A B C0 D E S T U V n hn
    hB hC hD hE hSdeg hTdeg hUdeg hVdeg htop.s_eq htop.t_eq
    htop.u_eq htop.v_eq] at htwo
  simp only [coeff_zero] at htwo
  have hfactor2 : (-8 / 81 : k) * (n : k) ≠ 0 :=
    mul_ne_zero (by norm_num) hnk
  have hrow2 : topRowTwo68 (A.coeff (2 * n)) (B.coeff (3 * n))
      (C0.coeff (4 * n)) (D.coeff (5 * n)) (E.coeff (6 * n)) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left hfactor2
  have hone := congrArg (fun p : k[X] => p.coeff (12 * n - 1)) h1
  rw [lowerRowOnePolynomial68_topCoeff A B C0 D E T U V n hn hC hD hE
    hTdeg hUdeg hVdeg htop.t_eq htop.u_eq htop.v_eq] at hone
  simp only [coeff_zero] at hone
  have hfactor1 : (-8 / 243 : k) * (n : k) ≠ 0 :=
    mul_ne_zero (by norm_num) hnk
  have hrow1 : topRowOne68 (A.coeff (2 * n)) (B.coeff (3 * n))
      (C0.coeff (4 * n)) (D.coeff (5 * n)) (E.coeff (6 * n)) = 0 :=
    (mul_eq_zero.mp hone).resolve_left hfactor1
  have hzero := h0top
  rw [lowerRowZeroPolynomial68_topCoeff A B C0 D E U V n hn hD hE
    hUdeg hVdeg htop.u_eq htop.v_eq] at hzero
  have hfactor0 : (-8 / 243 : k) * (n : k) ≠ 0 :=
    mul_ne_zero (by norm_num) hnk
  have hrow0 : topRowZero68 (A.coeff (2 * n)) (B.coeff (3 * n))
      (C0.coeff (4 * n)) (D.coeff (5 * n)) (E.coeff (6 * n)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hfactor0
  exact topRows_cubicCore68 (A.coeff (2 * n)) (B.coeff (3 * n))
    (C0.coeff (4 * n)) (D.coeff (5 * n)) (E.coeff (6 * n))
    hrow4 hrow3 hrow2 hrow1 hrow0

set_option maxHeartbeats 2000000 in
/-- Exact polynomial extraction for a constant terminal row. -/
theorem polynomialLowerSystem_cubicCore68
    (l beta gamma delta epsilon zeta i4 i3 terminal : k)
    (A B C0 D E S T U V : k[X]) (n : ℕ) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n)
    (hC : C0.natDegree ≤ 4 * n) (hD : D.natDegree ≤ 5 * n)
    (hE : E.natDegree ≤ 6 * n)
    (hSdeg : S.natDegree ≤ 5 * n) (hTdeg : T.natDegree ≤ 6 * n)
    (hUdeg : U.natDegree ≤ 7 * n) (hVdeg : V.natDegree ≤ 8 * n)
    (htop : IntegratedBoundaryCoefficients68 A B C0 D E S T U V n)
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3)
    (h2 : lowerRowTwoPolynomial68 S T U V B C0 D E = 0)
    (h1 : lowerRowOnePolynomial68 T U V C0 D E = 0)
    (h0 : lowerRowZeroPolynomial68 U V D E = C terminal) :
    B.coeff (3 * n) = 0 ∧ D.coeff (5 * n) = 0 ∧
      C0.coeff (4 * n) = A.coeff (2 * n) ^ 2 / 3 ∧
      E.coeff (6 * n) = A.coeff (2 * n) ^ 3 / 27 := by
  have h13m1 : 13 * n - 1 ≠ 0 := by omega
  have hcoeff := congrArg (fun p : k[X] => p.coeff (13 * n - 1)) h0
  have h0top : (lowerRowZeroPolynomial68 U V D E).coeff (13 * n - 1) = 0 := by
    simpa [coeff_C, h13m1] using hcoeff
  exact polynomialLowerSystem_cubicCore68_of_terminalCoeff_zero
    l beta gamma delta epsilon zeta i4 i3 A B C0 D E S T U V n hn
    hA hB hC hD hE hSdeg hTdeg hUdeg hVdeg htop hI4 hI3 h2 h1 h0top

set_option maxHeartbeats 2000000 in
/-- Source-facing bridge for the scale-zero polynomial boundary.  Once the
five sextic coefficients have polynomial representatives with the displayed
degree bounds, the integrated rational-function lower system forces their
weighted boundary into the cubic-core locus. -/
theorem integratedRationalLowerSystem_polynomialBoundary_cubicCore68
    (A B C0 D E : RatFunc k) (A0 B0 C00 D0 E0 : k[X])
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (hA0 : algebraMap k[X] (RatFunc k) A0 = A)
    (hB0 : algebraMap k[X] (RatFunc k) B0 = B)
    (hC0 : algebraMap k[X] (RatFunc k) C00 = C0)
    (hD0 : algebraMap k[X] (RatFunc k) D0 = D)
    (hE0 : algebraMap k[X] (RatFunc k) E0 = E)
    (hbracket :
      let P := integratedP68 A (RatFunc.C alpha)
      let Q := integratedQ68 (RatFunc.C l) A B (RatFunc.C beta)
      let R := integratedR68 (RatFunc.C l) A B C0 (RatFunc.C alpha)
        (RatFunc.C gamma)
      let S := integratedS68 (RatFunc.C l) A B C0 D (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C delta)
      let T := integratedT68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon)
      let U := integratedU68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta)
      let V := integratedV68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C eta)
      differentialJacobian ratFuncDerivation68 (depressedSextic68 A B C0 D E)
        (depressedOctic68 (RatFunc.C l) P Q R S T U V) =
          C (RatFunc.C terminal))
    (n : ℕ) (hn : 0 < n)
    (hAdeg : A0.natDegree ≤ 2 * n) (hBdeg : B0.natDegree ≤ 3 * n)
    (hCdeg : C00.natDegree ≤ 4 * n) (hDdeg : D0.natDegree ≤ 5 * n)
    (hEdeg : E0.natDegree ≤ 6 * n) :
    B0.coeff (3 * n) = 0 ∧ D0.coeff (5 * n) = 0 ∧
      C00.coeff (4 * n) = A0.coeff (2 * n) ^ 2 / 3 ∧
      E0.coeff (6 * n) = A0.coeff (2 * n) ^ 3 / 27 := by
  let S0 := integratedSPolynomial68 l alpha beta delta A0 B0 C00 D0
  let T0 := integratedTPolynomial68 l alpha beta gamma epsilon
    A0 B0 C00 D0 E0
  let U0 := integratedUPolynomial68 l alpha beta gamma delta zeta
    A0 B0 C00 D0 E0
  let V0 := integratedVPolynomial68 l alpha beta gamma delta epsilon eta
    A0 B0 C00 D0 E0
  have hdegrees := integratedPolynomial68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A0 B0 C00 D0 E0 n
    hAdeg hBdeg hCdeg hDdeg hEdeg
  have htop : IntegratedBoundaryCoefficients68 A0 B0 C00 D0 E0
      S0 T0 U0 V0 n := by
    dsimp only [S0, T0, U0, V0]
    exact integratedPolynomial68_boundaryCoefficients
      l alpha beta gamma delta epsilon zeta eta A0 B0 C00 D0 E0 n hn
      hAdeg hBdeg hCdeg hDdeg hEdeg
  have hSmap : algebraMap k[X] (RatFunc k) S0 =
      integratedS68 (RatFunc.C l) A B C0 D (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C delta) := by
    dsimp only [S0]
    rw [algebraMap_integratedSPolynomial68, hA0, hB0, hC0, hD0]
  have hTmap : algebraMap k[X] (RatFunc k) T0 =
      integratedT68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon) := by
    dsimp only [T0]
    rw [algebraMap_integratedTPolynomial68, hA0, hB0, hC0, hD0, hE0]
  have hUmap : algebraMap k[X] (RatFunc k) U0 =
      integratedU68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta) := by
    dsimp only [U0]
    rw [algebraMap_integratedUPolynomial68, hA0, hB0, hC0, hD0, hE0]
  have hVmap : algebraMap k[X] (RatFunc k) V0 =
      integratedV68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C eta) := by
    dsimp only [V0]
    rw [algebraMap_integratedVPolynomial68, hA0, hB0, hC0, hD0, hE0]
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    A B C0 D E (RatFunc.C terminal) l alpha beta gamma delta epsilon zeta eta
    hbracket
  simp only [RatFunc.algebraMap_eq_C] at hi4 hi3
  have hconst (a : k) : ratFuncDerivation68 (RatFunc.C a) = 0 := by
    have hp := ratFuncDerivation46_polynomial (C a : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hp
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
      (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
      (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
      (RatFunc.C terminal) (hconst l) (hconst alpha) (hconst beta)
      (hconst gamma) (hconst delta) (hconst epsilon) (hconst zeta)
      (hconst eta) hbracket
  dsimp only at hlow
  have hI4poly : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A0 B0 C00 D0 E0 = C i4 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_firstIntegralFourPolynomial68, RatFunc.algebraMap_C,
      hA0, hB0, hC0, hD0, hE0]
    exact hi4
  have hI3poly : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A0 B0 C00 D0 E0 = C i3 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_firstIntegralThreePolynomial68, RatFunc.algebraMap_C,
      hA0, hB0, hC0, hD0, hE0]
    exact hi3
  have h2poly : lowerRowTwoPolynomial68 S0 T0 U0 V0 B0 C00 D0 E0 = 0 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_lowerRowTwoPolynomial68, map_zero, hSmap, hTmap, hUmap,
      hVmap, hB0, hC0, hD0, hE0]
    exact hlow.2.2.1
  have h1poly : lowerRowOnePolynomial68 T0 U0 V0 C00 D0 E0 = 0 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_lowerRowOnePolynomial68, map_zero, hTmap, hUmap, hVmap,
      hC0, hD0, hE0]
    exact hlow.2.2.2.1
  have h0poly : lowerRowZeroPolynomial68 U0 V0 D0 E0 = C terminal := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    rw [algebraMap_lowerRowZeroPolynomial68, RatFunc.algebraMap_C,
      hUmap, hVmap, hD0, hE0]
    exact hlow.2.2.2.2
  exact polynomialLowerSystem_cubicCore68 l beta gamma delta epsilon zeta
    i4 i3 terminal A0 B0 C00 D0 E0 S0 T0 U0 V0 n hn
    hAdeg hBdeg hCdeg hDdeg hEdeg
    hdegrees.1 hdegrees.2.1 hdegrees.2.2.1 hdegrees.2.2.2
    htop hI4poly hI3poly h2poly h1poly h0poly

end PolynomialBoundary68

#print axioms coeff_mul_weightedBoundary68
#print axioms coeff_pow_weightedBoundary68
#print axioms coeff_mul_derivative_weightedBoundary68
#print axioms algebraMap_integratedSPolynomial68
#print axioms algebraMap_integratedTPolynomial68
#print axioms algebraMap_integratedUPolynomial68
#print axioms algebraMap_integratedVPolynomial68
#print axioms algebraMap_firstIntegralFourPolynomial68
#print axioms algebraMap_firstIntegralThreePolynomial68
#print axioms algebraMap_lowerRowTwoPolynomial68
#print axioms algebraMap_lowerRowOnePolynomial68
#print axioms algebraMap_lowerRowZeroPolynomial68
#print axioms integratedSPolynomial68_topCoeff
#print axioms integratedTPolynomial68_topCoeff
#print axioms integratedUPolynomial68_topCoeff
#print axioms integratedVPolynomial68_topCoeff
#print axioms lowerRowTwoPolynomial68_topCoeff
#print axioms lowerRowOnePolynomial68_topCoeff
#print axioms lowerRowZeroPolynomial68_topCoeff
#print axioms firstIntegralFourPolynomial68_topCoeff
#print axioms firstIntegralThreePolynomial68_topCoeff
#print axioms integratedPolynomial68_boundaryCoefficients
#print axioms integratedPolynomial68_degreeBounds
#print axioms polynomialLowerSystem_cubicCore68_of_terminalCoeff_zero
#print axioms polynomialLowerSystem_cubicCore68
#print axioms integratedRationalLowerSystem_polynomialBoundary_cubicCore68

end Max11DegreeRoutes
