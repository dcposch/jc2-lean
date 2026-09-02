import Grok610ScaleZeroValuationEndgameScratch
import LowScale68ScaleZero

/-! # Scale-zero cone cascade for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroValuationEndgameScratch` on the constant
core `H = (C t)²`.  That file reconstructed the nine triangular Faber
coordinates of the depressed decic and excluded a differentially constant
free core.  This file supplies the missing `(4,10)`-style polynomial
trajectory: the depressed sextic letters `(A, B, C₀, D₀, E₀)` have
literal representatives in `k[x]`, the weight-fifteen primitive of the
integrated trajectory is a polynomial in those letters whose derivative
is the nonzero constant `j / t`, and therefore that primitive has Newton
degree one.

The degree-one identity bounds the free core.  If every letter is a
constant polynomial the primitive is constant, contradicting degree one.
If `A` is the unique highest-degree letter and `L ≠ 0`, the face
`A⁷ L` is unique of degree `7 deg A ≥ 7`.  If `L = 0` and `B` is
nonconstant, `A⁶ B` is unique.  If `L = 0`, `B = 0` and `β ≠ 0`, the
load face `β A⁶` is unique.  If `B` is the unique highest-degree letter
on the extreme cone `3 deg A < 2 deg B` with `L = 0` or `7 deg A < 5 deg B`,
the face `B⁵` is unique.  If `D₀` is the only nonconstant letter, the
face `D₀³` is unique of degree at least three.  If `E₀` is the only
nonconstant letter and `β ≠ 0`, the face `β E₀²` is unique of degree
at least two.

The leaf is not closed.  The residual Newton cone is a nonconstant
polynomial core in which either two or more letters share the maximal
degree, or else `A` uniquely leads with `L = 0` and `B` a (possibly
zero) constant, and in the `B = 0` case also `β = 0`, or else `E₀` is
the unique nonconstant letter with `β = 0`.  The already-constant first
integrals `κ, λ, μ` and the weight-seventy residual `ο` remain available
and are not consumed.  No total-degree or twice-prime theorem is used.
No finite-root shortcut is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Degree bookkeeping -/

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

/-- A polynomial with nonzero constant derivative has exact degree one. -/
theorem natDegree_eq_one_of_derivative_eq_nonzero_C610
    (P : k[X]) (j : k) (hj : j ≠ 0) (h : derivative P = C j) :
    P.natDegree = 1 := by
  have hder : derivative P ≠ 0 := by
    intro hz
    rw [hz] at h
    exact hj (C_eq_zero.mp h.symm)
  have hdegder : (derivative P).natDegree = 0 := by
    rw [h, natDegree_C]
  have hpositive : 0 < P.natDegree :=
    Nat.pos_of_ne_zero (derivative_ne_zero.mp hder)
  rw [natDegree_derivative] at hdegder
  omega

/-- A nonzero scalar multiple of a unique positive-degree leading monomial
cannot equal a constant polynomial. -/
theorem smul_add_lower_ne_C610 (c q : k) (M R : k[X]) (d : ℕ)
    (hc : c ≠ 0) (hM : M ≠ 0) (hd : 0 < d)
    (hMdeg : M.natDegree = d) (hRdeg : R.natDegree < d) :
    c • M + R ≠ C q := by
  intro heq
  have hRcoeff : R.coeff d = 0 := coeff_eq_zero_of_natDegree_lt hRdeg
  have hCcoeff : (C q : k[X]).coeff d = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hMcoeff : M.coeff d = M.leadingCoeff := by
    rw [← hMdeg, coeff_natDegree]
  have hcoeff := congrArg (fun P : k[X] => P.coeff d) heq
  rw [coeff_add, coeff_smul, hMcoeff, hRcoeff, add_zero, hCcoeff] at hcoeff
  simp only [smul_eq_mul] at hcoeff
  exact (mul_ne_zero hc (leadingCoeff_ne_zero.mpr hM)) hcoeff

theorem natDegree_add_lt610 {p q : k[X]} {d : ℕ}
    (hp : p.natDegree < d) (hq : q.natDegree < d) :
    (p + q).natDegree < d :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

theorem natDegree_add_le610 {p q : k[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    (p + q).natDegree ≤ d :=
  (natDegree_add_le p q).trans (max_le hp hq)

theorem natDegree_smul_le610 (c : k) (p : k[X]) :
    (c • p).natDegree ≤ p.natDegree := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, natDegree_zero]
    exact Nat.zero_le _
  · rw [natDegree_smul _ hc]

theorem natDegree_smul_lt610 (c : k) {p : k[X]} {d : ℕ}
    (hp : p.natDegree < d) : (c • p).natDegree < d :=
  (natDegree_smul_le610 c p).trans_lt hp

theorem natDegree_smul_le_of_le610 (c : k) {p : k[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) : (c • p).natDegree ≤ d :=
  (natDegree_smul_le610 c p).trans hp

theorem natDegree_add8_lt610
    {p1 p2 p3 p4 p5 p6 p7 p8 : k[X]} {d : ℕ}
    (h1 : p1.natDegree < d) (h2 : p2.natDegree < d)
    (h3 : p3.natDegree < d) (h4 : p4.natDegree < d)
    (h5 : p5.natDegree < d) (h6 : p6.natDegree < d)
    (h7 : p7.natDegree < d) (h8 : p8.natDegree < d) :
    (p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8).natDegree < d :=
  natDegree_add_lt610
    (natDegree_add_lt610
      (natDegree_add_lt610
        (natDegree_add_lt610
          (natDegree_add_lt610
            (natDegree_add_lt610 (natDegree_add_lt610 h1 h2) h3) h4) h5)
        h6)
      h7)
    h8

theorem natDegree_add8_le610
    {p1 p2 p3 p4 p5 p6 p7 p8 : k[X]} {d : ℕ}
    (h1 : p1.natDegree ≤ d) (h2 : p2.natDegree ≤ d)
    (h3 : p3.natDegree ≤ d) (h4 : p4.natDegree ≤ d)
    (h5 : p5.natDegree ≤ d) (h6 : p6.natDegree ≤ d)
    (h7 : p7.natDegree ≤ d) (h8 : p8.natDegree ≤ d) :
    (p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8).natDegree ≤ d :=
  natDegree_add_le610
    (natDegree_add_le610
      (natDegree_add_le610
        (natDegree_add_le610
          (natDegree_add_le610
            (natDegree_add_le610 (natDegree_add_le610 h1 h2) h3) h4) h5)
        h6)
      h7)
    h8

/-- Unique-max `A` cone: `A` strictly outranks the other four free letters. -/
def UniqueHighACone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    B.natDegree < A.natDegree ∧
    C0.natDegree < A.natDegree ∧
    D0.natDegree < A.natDegree ∧
    E0.natDegree < A.natDegree

/-- Unique-max `B` cone. -/
def UniqueHighBCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    A.natDegree < B.natDegree ∧
    C0.natDegree < B.natDegree ∧
    D0.natDegree < B.natDegree ∧
    E0.natDegree < B.natDegree

/-- Extreme high-`B` subcone on which `B⁵` outranks `A⁶ B` and `A⁷`. -/
def ExtremeHighBCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  UniqueHighBCone610 A B C0 D0 E0 ∧
    3 * A.natDegree < 2 * B.natDegree ∧
    7 * A.natDegree < 5 * B.natDegree

end DegreeLemmas610

/-! ## Polynomial pullback of the integrated primitive -/

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

/-- Polynomial pullback of `degreeZeroBaseGroup610`. -/
def degreeZeroBaseGroupPolynomial610
    (l : k) (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(10935 / 2239488 * l : k)) • A ^ 7 -
    (62720 / 2239488 : k) • (A ^ 6 * B) +
    (113724 / 2239488 * l : k) • (A ^ 5 * C0) +
    (92160 / 2239488 : k) • (A ^ 5 * D0) +
    (301806 / 2239488 * l : k) • (A ^ 4 * B ^ 2) +
    (491520 / 2239488 : k) • (A ^ 4 * B * C0) -
    (122472 / 2239488 * l : k) • (A ^ 4 * E0) +
    (343040 / 2239488 : k) • (A ^ 3 * B ^ 3) -
    (769824 / 2239488 * l : k) • (A ^ 3 * B * D0) -
    (483840 / 2239488 : k) • (A ^ 3 * B * E0) -
    (384912 / 2239488 * l : k) • (A ^ 3 * C0 ^ 2) -
    (668160 / 2239488 : k) • (A ^ 3 * C0 * D0) -
    (1224720 / 2239488 * l : k) • (A ^ 2 * B ^ 2 * C0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B ^ 2 * D0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B * C0 ^ 2) +
    (699840 / 2239488 * l : k) • (A ^ 2 * C0 * E0) +
    (559872 / 2239488 * l : k) • (A ^ 2 * D0 ^ 2) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) -
    (209952 / 2239488 * l : k) • (A * B ^ 4) -
    (737280 / 2239488 : k) • (A * B ^ 3 * C0) +
    (839808 / 2239488 * l : k) • (A * B ^ 2 * E0) +
    (2519424 / 2239488 * l : k) • (A * B * C0 * D0) +
    (1658880 / 2239488 : k) • (A * B * C0 * E0) +
    (1244160 / 2239488 : k) • (A * B * D0 ^ 2) +
    (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) -
    (36864 / 2239488 : k) • B ^ 5 +
    (419904 / 2239488 * l : k) • (B ^ 3 * D0) +
    (276480 / 2239488 : k) • (B ^ 3 * E0) +
    (629856 / 2239488 * l : k) • (B ^ 2 * C0 ^ 2) +
    (1244160 / 2239488 : k) • (B ^ 2 * C0 * D0) +
    (414720 / 2239488 : k) • (B * C0 ^ 3) -
    (1679616 / 2239488 * l : k) • (B * D0 * E0) -
    (839808 / 2239488 * l : k) • (C0 ^ 2 * E0) -
    (1679616 / 2239488 * l : k) • (C0 * D0 ^ 2) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) -
    (829440 / 2239488 : k) • D0 ^ 3

/-- Base group with the unique-`A` face `A⁷ L` deleted. -/
def degreeZeroBaseGroupHighARest610
    (l : k) (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(62720 / 2239488 : k)) • (A ^ 6 * B) +
    (113724 / 2239488 * l : k) • (A ^ 5 * C0) +
    (92160 / 2239488 : k) • (A ^ 5 * D0) +
    (301806 / 2239488 * l : k) • (A ^ 4 * B ^ 2) +
    (491520 / 2239488 : k) • (A ^ 4 * B * C0) -
    (122472 / 2239488 * l : k) • (A ^ 4 * E0) +
    (343040 / 2239488 : k) • (A ^ 3 * B ^ 3) -
    (769824 / 2239488 * l : k) • (A ^ 3 * B * D0) -
    (483840 / 2239488 : k) • (A ^ 3 * B * E0) -
    (384912 / 2239488 * l : k) • (A ^ 3 * C0 ^ 2) -
    (668160 / 2239488 : k) • (A ^ 3 * C0 * D0) -
    (1224720 / 2239488 * l : k) • (A ^ 2 * B ^ 2 * C0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B ^ 2 * D0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B * C0 ^ 2) +
    (699840 / 2239488 * l : k) • (A ^ 2 * C0 * E0) +
    (559872 / 2239488 * l : k) • (A ^ 2 * D0 ^ 2) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) -
    (209952 / 2239488 * l : k) • (A * B ^ 4) -
    (737280 / 2239488 : k) • (A * B ^ 3 * C0) +
    (839808 / 2239488 * l : k) • (A * B ^ 2 * E0) +
    (2519424 / 2239488 * l : k) • (A * B * C0 * D0) +
    (1658880 / 2239488 : k) • (A * B * C0 * E0) +
    (1244160 / 2239488 : k) • (A * B * D0 ^ 2) +
    (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) -
    (36864 / 2239488 : k) • B ^ 5 +
    (419904 / 2239488 * l : k) • (B ^ 3 * D0) +
    (276480 / 2239488 : k) • (B ^ 3 * E0) +
    (629856 / 2239488 * l : k) • (B ^ 2 * C0 ^ 2) +
    (1244160 / 2239488 : k) • (B ^ 2 * C0 * D0) +
    (414720 / 2239488 : k) • (B * C0 ^ 3) -
    (1679616 / 2239488 * l : k) • (B * D0 * E0) -
    (839808 / 2239488 * l : k) • (C0 ^ 2 * E0) -
    (1679616 / 2239488 * l : k) • (C0 * D0 ^ 2) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) -
    (829440 / 2239488 : k) • D0 ^ 3

/-- Unique-`A` rest with the next face `A⁶ B` also deleted. -/
def degreeZeroBaseGroupHighA_noA6B_Rest610
    (l : k) (A B C0 D0 E0 : k[X]) : k[X] :=
  (113724 / 2239488 * l : k) • (A ^ 5 * C0) +
    (92160 / 2239488 : k) • (A ^ 5 * D0) +
    (301806 / 2239488 * l : k) • (A ^ 4 * B ^ 2) +
    (491520 / 2239488 : k) • (A ^ 4 * B * C0) -
    (122472 / 2239488 * l : k) • (A ^ 4 * E0) +
    (343040 / 2239488 : k) • (A ^ 3 * B ^ 3) -
    (769824 / 2239488 * l : k) • (A ^ 3 * B * D0) -
    (483840 / 2239488 : k) • (A ^ 3 * B * E0) -
    (384912 / 2239488 * l : k) • (A ^ 3 * C0 ^ 2) -
    (668160 / 2239488 : k) • (A ^ 3 * C0 * D0) -
    (1224720 / 2239488 * l : k) • (A ^ 2 * B ^ 2 * C0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B ^ 2 * D0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B * C0 ^ 2) +
    (699840 / 2239488 * l : k) • (A ^ 2 * C0 * E0) +
    (559872 / 2239488 * l : k) • (A ^ 2 * D0 ^ 2) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) -
    (209952 / 2239488 * l : k) • (A * B ^ 4) -
    (737280 / 2239488 : k) • (A * B ^ 3 * C0) +
    (839808 / 2239488 * l : k) • (A * B ^ 2 * E0) +
    (2519424 / 2239488 * l : k) • (A * B * C0 * D0) +
    (1658880 / 2239488 : k) • (A * B * C0 * E0) +
    (1244160 / 2239488 : k) • (A * B * D0 ^ 2) +
    (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) -
    (36864 / 2239488 : k) • B ^ 5 +
    (419904 / 2239488 * l : k) • (B ^ 3 * D0) +
    (276480 / 2239488 : k) • (B ^ 3 * E0) +
    (629856 / 2239488 * l : k) • (B ^ 2 * C0 ^ 2) +
    (1244160 / 2239488 : k) • (B ^ 2 * C0 * D0) +
    (414720 / 2239488 : k) • (B * C0 ^ 3) -
    (1679616 / 2239488 * l : k) • (B * D0 * E0) -
    (839808 / 2239488 * l : k) • (C0 ^ 2 * E0) -
    (1679616 / 2239488 * l : k) • (C0 * D0 ^ 2) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) -
    (829440 / 2239488 : k) • D0 ^ 3

/-- Base group with the unique-`B` face `B⁵` deleted. -/
def degreeZeroBaseGroupHighBRest610
    (l : k) (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(10935 / 2239488 * l : k)) • A ^ 7 -
    (62720 / 2239488 : k) • (A ^ 6 * B) +
    (113724 / 2239488 * l : k) • (A ^ 5 * C0) +
    (92160 / 2239488 : k) • (A ^ 5 * D0) +
    (301806 / 2239488 * l : k) • (A ^ 4 * B ^ 2) +
    (491520 / 2239488 : k) • (A ^ 4 * B * C0) -
    (122472 / 2239488 * l : k) • (A ^ 4 * E0) +
    (343040 / 2239488 : k) • (A ^ 3 * B ^ 3) -
    (769824 / 2239488 * l : k) • (A ^ 3 * B * D0) -
    (483840 / 2239488 : k) • (A ^ 3 * B * E0) -
    (384912 / 2239488 * l : k) • (A ^ 3 * C0 ^ 2) -
    (668160 / 2239488 : k) • (A ^ 3 * C0 * D0) -
    (1224720 / 2239488 * l : k) • (A ^ 2 * B ^ 2 * C0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B ^ 2 * D0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B * C0 ^ 2) +
    (699840 / 2239488 * l : k) • (A ^ 2 * C0 * E0) +
    (559872 / 2239488 * l : k) • (A ^ 2 * D0 ^ 2) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) -
    (209952 / 2239488 * l : k) • (A * B ^ 4) -
    (737280 / 2239488 : k) • (A * B ^ 3 * C0) +
    (839808 / 2239488 * l : k) • (A * B ^ 2 * E0) +
    (2519424 / 2239488 * l : k) • (A * B * C0 * D0) +
    (1658880 / 2239488 : k) • (A * B * C0 * E0) +
    (1244160 / 2239488 : k) • (A * B * D0 ^ 2) +
    (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) +
    (419904 / 2239488 * l : k) • (B ^ 3 * D0) +
    (276480 / 2239488 : k) • (B ^ 3 * E0) +
    (629856 / 2239488 * l : k) • (B ^ 2 * C0 ^ 2) +
    (1244160 / 2239488 : k) • (B ^ 2 * C0 * D0) +
    (414720 / 2239488 : k) • (B * C0 ^ 3) -
    (1679616 / 2239488 * l : k) • (B * D0 * E0) -
    (839808 / 2239488 * l : k) • (C0 ^ 2 * E0) -
    (1679616 / 2239488 * l : k) • (C0 * D0 ^ 2) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) -
    (829440 / 2239488 : k) • D0 ^ 3

/-- Base group with the unique-`D₀` face `D₀³` deleted. -/
def degreeZeroBaseGroupHighDRest610
    (l : k) (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(10935 / 2239488 * l : k)) • A ^ 7 -
    (62720 / 2239488 : k) • (A ^ 6 * B) +
    (113724 / 2239488 * l : k) • (A ^ 5 * C0) +
    (92160 / 2239488 : k) • (A ^ 5 * D0) +
    (301806 / 2239488 * l : k) • (A ^ 4 * B ^ 2) +
    (491520 / 2239488 : k) • (A ^ 4 * B * C0) -
    (122472 / 2239488 * l : k) • (A ^ 4 * E0) +
    (343040 / 2239488 : k) • (A ^ 3 * B ^ 3) -
    (769824 / 2239488 * l : k) • (A ^ 3 * B * D0) -
    (483840 / 2239488 : k) • (A ^ 3 * B * E0) -
    (384912 / 2239488 * l : k) • (A ^ 3 * C0 ^ 2) -
    (668160 / 2239488 : k) • (A ^ 3 * C0 * D0) -
    (1224720 / 2239488 * l : k) • (A ^ 2 * B ^ 2 * C0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B ^ 2 * D0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B * C0 ^ 2) +
    (699840 / 2239488 * l : k) • (A ^ 2 * C0 * E0) +
    (559872 / 2239488 * l : k) • (A ^ 2 * D0 ^ 2) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) -
    (209952 / 2239488 * l : k) • (A * B ^ 4) -
    (737280 / 2239488 : k) • (A * B ^ 3 * C0) +
    (839808 / 2239488 * l : k) • (A * B ^ 2 * E0) +
    (2519424 / 2239488 * l : k) • (A * B * C0 * D0) +
    (1658880 / 2239488 : k) • (A * B * C0 * E0) +
    (1244160 / 2239488 : k) • (A * B * D0 ^ 2) +
    (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) -
    (36864 / 2239488 : k) • B ^ 5 +
    (419904 / 2239488 * l : k) • (B ^ 3 * D0) +
    (276480 / 2239488 : k) • (B ^ 3 * E0) +
    (629856 / 2239488 * l : k) • (B ^ 2 * C0 ^ 2) +
    (1244160 / 2239488 : k) • (B ^ 2 * C0 * D0) +
    (414720 / 2239488 : k) • (B * C0 ^ 3) -
    (1679616 / 2239488 * l : k) • (B * D0 * E0) -
    (839808 / 2239488 * l : k) • (C0 ^ 2 * E0) -
    (1679616 / 2239488 * l : k) • (C0 * D0 ^ 2) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0)

/-- Polynomial pullback of `degreeZeroAlphaGroup610`. -/
def degreeZeroAlphaGroupPolynomial610 (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 729 : k) • (A ^ 5 * B) -
    (51 / 729 : k) • (A ^ 4 * D0) -
    (222 / 729 : k) • (A ^ 3 * B * C0) -
    (117 / 729 : k) • (A ^ 2 * B ^ 3) +
    (189 / 729 : k) • (A ^ 2 * B * E0) +
    (297 / 729 : k) • (A ^ 2 * C0 * D0) +
    (324 / 729 : k) • (A * B ^ 2 * D0) +
    (324 / 729 : k) • (A * B * C0 ^ 2) -
    (324 / 729 : k) • (A * D0 * E0) +
    (108 / 729 : k) • (B ^ 3 * C0) -
    (324 / 729 : k) • (B * C0 * E0) -
    (324 / 729 : k) • (B * D0 ^ 2) -
    (324 / 729 : k) • (C0 ^ 2 * D0)

/-- Polynomial pullback of `degreeZeroBetaGroup610`. -/
def degreeZeroBetaGroupPolynomial610 (A B C0 D0 E0 : k[X]) : k[X] :=
  (2695 / 559872 : k) • A ^ 6 -
    (23940 / 559872 : k) • (A ^ 4 * C0) -
    (51660 / 559872 : k) • (A ^ 3 * B ^ 2) +
    (21168 / 559872 : k) • (A ^ 3 * E0) +
    (127008 / 559872 : k) • (A ^ 2 * B * D0) +
    (63504 / 559872 : k) • (A ^ 2 * C0 ^ 2) +
    (136080 / 559872 : k) • (A * B ^ 2 * C0) -
    (108864 / 559872 : k) • (A * C0 * E0) -
    (108864 / 559872 : k) • (A * D0 ^ 2) +
    (11340 / 559872 : k) • B ^ 4 -
    (54432 / 559872 : k) • (B ^ 2 * E0) -
    (217728 / 559872 : k) • (B * C0 * D0) -
    (36288 / 559872 : k) • C0 ^ 3 +
    (326592 / 559872 : k) • E0 ^ 2

/-- Beta group with the unique-`A` load face `A⁶` deleted. -/
def degreeZeroBetaGroupNoA6Polynomial610 (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(23940 / 559872 : k)) • (A ^ 4 * C0) -
    (51660 / 559872 : k) • (A ^ 3 * B ^ 2) +
    (21168 / 559872 : k) • (A ^ 3 * E0) +
    (127008 / 559872 : k) • (A ^ 2 * B * D0) +
    (63504 / 559872 : k) • (A ^ 2 * C0 ^ 2) +
    (136080 / 559872 : k) • (A * B ^ 2 * C0) -
    (108864 / 559872 : k) • (A * C0 * E0) -
    (108864 / 559872 : k) • (A * D0 ^ 2) +
    (11340 / 559872 : k) • B ^ 4 -
    (54432 / 559872 : k) • (B ^ 2 * E0) -
    (217728 / 559872 : k) • (B * C0 * D0) -
    (36288 / 559872 : k) • C0 ^ 3 +
    (326592 / 559872 : k) • E0 ^ 2

/-- Beta group with the unique-`E₀` face `E₀²` deleted. -/
def degreeZeroBetaGroupNoE2Polynomial610 (A B C0 D0 E0 : k[X]) : k[X] :=
  (2695 / 559872 : k) • A ^ 6 -
    (23940 / 559872 : k) • (A ^ 4 * C0) -
    (51660 / 559872 : k) • (A ^ 3 * B ^ 2) +
    (21168 / 559872 : k) • (A ^ 3 * E0) +
    (127008 / 559872 : k) • (A ^ 2 * B * D0) +
    (63504 / 559872 : k) • (A ^ 2 * C0 ^ 2) +
    (136080 / 559872 : k) • (A * B ^ 2 * C0) -
    (108864 / 559872 : k) • (A * C0 * E0) -
    (108864 / 559872 : k) • (A * D0 ^ 2) +
    (11340 / 559872 : k) • B ^ 4 -
    (54432 / 559872 : k) • (B ^ 2 * E0) -
    (217728 / 559872 : k) • (B * C0 * D0) -
    (36288 / 559872 : k) • C0 ^ 3

/-- Polynomial pullback of `degreeZeroDeltaGroup610`. -/
def degreeZeroDeltaGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (49 / 5184 : k) • A ^ 5 -
    (360 / 5184 : k) • (A ^ 3 * C0) -
    (600 / 5184 : k) • (A ^ 2 * B ^ 2) +
    (1440 / 5184 : k) • (A * B * D0) +
    (720 / 5184 : k) • (A * C0 ^ 2) +
    (720 / 5184 : k) • (B ^ 2 * C0) -
    (2160 / 5184 : k) • D0 ^ 2

/-- Polynomial pullback of `degreeZeroEpsilonGroup610`. -/
def degreeZeroEpsilonGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (-(7 / 54 : k)) • (A ^ 3 * B) +
    (9 / 54 : k) • (A ^ 2 * D0) +
    (24 / 54 : k) • (A * B * C0) +
    (4 / 54 : k) • B ^ 3 -
    (36 / 54 : k) • (C0 * D0)

/-- Polynomial pullback of `degreeZeroZetaGroup610`. -/
def degreeZeroZetaGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (-(7 / 192 : k)) • A ^ 4 +
    (40 / 192 : k) • (A ^ 2 * C0) +
    (48 / 192 : k) • (A * B ^ 2) -
    (96 / 192 : k) • (B * D0) -
    (48 / 192 : k) • C0 ^ 2

/-- Polynomial pullback of `degreeZeroEtaGroup610`. -/
def degreeZeroEtaGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (7 / 36 : k) • (A ^ 2 * B) -
    (12 / 36 : k) • (A * D0) -
    (12 / 36 : k) • (B * C0)

/-- Polynomial pullback of `degreeZeroThetaGroup610`. -/
def degreeZeroThetaGroupPolynomial610 (A B C0 E0 : k[X]) : k[X] :=
  (7 / 216 : k) • A ^ 3 -
    (36 / 216 : k) • (A * C0) -
    (18 / 216 : k) • B ^ 2 +
    (216 / 216 : k) • E0

/-- Integrated weight-fifteen primitive after the triangular residuals are
ground constants. -/
def degreeZeroIntegratedPrimitive610
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta delta epsilon zeta eta theta : F) : F :=
  degreeZeroBaseGroup610 L A B C0 D0 E0 +
    alpha * degreeZeroAlphaGroup610 A B C0 D0 E0 +
    beta * degreeZeroBetaGroup610 A B C0 D0 E0 +
    delta * degreeZeroDeltaGroup610 A B C0 D0 +
    epsilon * degreeZeroEpsilonGroup610 A B C0 D0 +
    zeta * degreeZeroZetaGroup610 A B C0 D0 +
    eta * degreeZeroEtaGroup610 A B C0 D0 +
    theta * degreeZeroThetaGroup610 A B C0 E0

/-- Polynomial representative of the integrated primitive. -/
def degreeZeroPrimitivePolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupPolynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

/-- Primitive with the unique-`A` face deleted. -/
def degreeZeroPrimitiveHighARest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupHighARest610 l A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupPolynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

/-- Primitive with the unique-`A` faces `A⁷ L` and `A⁶ B` deleted. -/
def degreeZeroPrimitiveHighA_noA6B_Rest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupHighA_noA6B_Rest610 l A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupPolynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

/-- Primitive with the unique-`B` face `B⁵` deleted. -/
def degreeZeroPrimitiveHighBRest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupHighBRest610 l A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupPolynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

/-- Primitive with the unique-`D₀` face `D₀³` deleted. -/
def degreeZeroPrimitiveHighDRest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupHighDRest610 l A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupPolynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

/-- Primitive with `B = 0` and the load face `β A⁶` deleted. -/
def degreeZeroPrimitiveHighA_B0_noA6_Rest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupHighA_noA6B_Rest610 l A 0 C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A 0 C0 D0 E0 +
    beta • degreeZeroBetaGroupNoA6Polynomial610 A 0 C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A 0 C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A 0 C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A 0 C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A 0 C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A 0 C0 E0

/-- Primitive with the unique-`E₀` face `β E₀²` deleted. -/
def degreeZeroPrimitiveHighERest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupNoE2Polynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

set_option maxHeartbeats 8000000 in
theorem degreeZeroBaseGroupPolynomial610_eq_A7_add_rest
    (l : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0 =
      (-(10935 / 2239488 * l : k)) • A ^ 7 +
        degreeZeroBaseGroupHighARest610 l A B C0 D0 E0 := by
  simp only [degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighARest610]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroPrimitivePolynomial610_eq_A7_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(10935 / 2239488 * l : k)) • A ^ 7 +
        degreeZeroPrimitiveHighARest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighARest610,
    degreeZeroBaseGroupPolynomial610_eq_A7_add_rest]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroPrimitivePolynomial610_eq_A6B_add_rest
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(62720 / 2239488 : k)) • (A ^ 6 * B) +
        degreeZeroPrimitiveHighA_noA6B_Rest610 0 alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighA_noA6B_Rest610,
    degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighA_noA6B_Rest610, zero_mul, neg_zero,
    zero_smul, zero_add]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_betaA6_add_rest
    (alpha beta delta epsilon zeta eta theta : k)
    (A C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta eta
        theta A 0 C0 D0 E0 =
      ((2695 / 559872 * beta : k) • A ^ 6) +
        degreeZeroPrimitiveHighA_B0_noA6_Rest610 0 alpha beta delta
          epsilon zeta eta theta A C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighA_B0_noA6_Rest610,
    degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighA_noA6B_Rest610,
    degreeZeroBetaGroupPolynomial610,
    degreeZeroBetaGroupNoA6Polynomial610, zero_mul, mul_zero, neg_zero,
    zero_smul, smul_zero, zero_add, add_zero, sub_zero]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_betaE2_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      ((326592 / 559872 * beta : k) • E0 ^ 2) +
        degreeZeroPrimitiveHighERest610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighERest610, degreeZeroBetaGroupPolynomial610,
    degreeZeroBetaGroupNoE2Polynomial610]
  module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitive610_eq_integratedPrimitive
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta gamma delta epsilon zeta eta theta iota : F) :
    degreeZeroPrimitive610 L A B C0 D0 E0
        (integratedP610 A alpha)
        (integratedQ610 L A B beta)
        (integratedR610 L A B C0 alpha gamma)
        (integratedS610 L A B C0 D0 alpha beta delta)
        (integratedT610 L A B C0 D0 E0 alpha beta gamma epsilon)
        (integratedU610 L A B C0 D0 E0 alpha beta gamma delta zeta)
        (integratedV610 L A B C0 D0 E0 alpha beta gamma delta epsilon eta)
        (integratedW610 L A B C0 D0 E0 alpha beta gamma delta epsilon zeta
          theta)
        (integratedX610 L A B C0 D0 E0 alpha beta gamma delta epsilon zeta
          eta iota) =
      degreeZeroIntegratedPrimitive610 L A B C0 D0 E0 alpha beta delta
        epsilon zeta eta theta := by
  obtain ⟨halpha, hbeta, _hgamma, hdelta, hepsilon, hzeta, heta, htheta,
      _hiota⟩ :=
    integratedResiduals610 L A B C0 D0 E0 alpha beta gamma delta epsilon
      zeta eta theta iota
  simp only [degreeZeroPrimitive610, degreeZeroIntegratedPrimitive610]
  rw [halpha, hbeta, hdelta, hepsilon, hzeta, heta, htheta]

set_option maxHeartbeats 32000000 in
theorem algebraMap_degreeZeroBaseGroupPolynomial610
    (l : k) (A B C0 D0 E0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0) =
      degreeZeroBaseGroup610 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0) := by
  simp only [degreeZeroBaseGroupPolynomial610, degreeZeroBaseGroup610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem algebraMap_degreeZeroAlphaGroupPolynomial610
    (A B C0 D0 E0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0) =
      degreeZeroAlphaGroup610
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0) := by
  simp only [degreeZeroAlphaGroupPolynomial610, degreeZeroAlphaGroup610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem algebraMap_degreeZeroBetaGroupPolynomial610
    (A B C0 D0 E0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0) =
      degreeZeroBetaGroup610
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0) := by
  simp only [degreeZeroBetaGroupPolynomial610, degreeZeroBetaGroup610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem algebraMap_degreeZeroDeltaGroupPolynomial610
    (A B C0 D0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0) =
      degreeZeroDeltaGroup610
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0) := by
  simp only [degreeZeroDeltaGroupPolynomial610, degreeZeroDeltaGroup610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem algebraMap_degreeZeroEpsilonGroupPolynomial610
    (A B C0 D0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0) =
      degreeZeroEpsilonGroup610
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0) := by
  simp only [degreeZeroEpsilonGroupPolynomial610, degreeZeroEpsilonGroup610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem algebraMap_degreeZeroZetaGroupPolynomial610
    (A B C0 D0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroZetaGroupPolynomial610 A B C0 D0) =
      degreeZeroZetaGroup610
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0) := by
  simp only [degreeZeroZetaGroupPolynomial610, degreeZeroZetaGroup610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem algebraMap_degreeZeroEtaGroupPolynomial610
    (A B C0 D0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroEtaGroupPolynomial610 A B C0 D0) =
      degreeZeroEtaGroup610
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0) := by
  simp only [degreeZeroEtaGroupPolynomial610, degreeZeroEtaGroup610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem algebraMap_degreeZeroThetaGroupPolynomial610
    (A B C0 E0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroThetaGroupPolynomial610 A B C0 E0) =
      degreeZeroThetaGroup610
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) E0) := by
  simp only [degreeZeroThetaGroupPolynomial610, degreeZeroThetaGroup610,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 16000000 in
theorem algebraMap_degreeZeroPrimitivePolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0) =
      degreeZeroIntegratedPrimitive610 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroIntegratedPrimitive610, map_add, Polynomial.smul_eq_C_mul,
    map_mul, RatFunc.algebraMap_C,
    algebraMap_degreeZeroBaseGroupPolynomial610,
    algebraMap_degreeZeroAlphaGroupPolynomial610,
    algebraMap_degreeZeroBetaGroupPolynomial610,
    algebraMap_degreeZeroDeltaGroupPolynomial610,
    algebraMap_degreeZeroEpsilonGroupPolynomial610,
    algebraMap_degreeZeroZetaGroupPolynomial610,
    algebraMap_degreeZeroEtaGroupPolynomial610,
    algebraMap_degreeZeroThetaGroupPolynomial610]

end PrimitivePolynomial610

/-! ## Polynomial representatives of the depressed free core -/

section PolynomialCore610

variable {k : Type*} [Field k] [CharZero k]

/-- At constant scale the monic sextic depression is a polynomial
substitution, so every free-core letter has a representative in `k[x]`. -/
theorem constantScale_monicSextic_polynomialCore610
    (p : k[X][X]) (t : k) (ht : t ≠ 0) :
    let r0 : k[X] := C ((6 * t ^ 5)⁻¹) * p.coeff 5
    let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
    let f : (RatFunc k)[X] :=
      affineDepress68 (RatFunc.C t)
        (sexticDepressionR610 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) (p.coeff 5)))
        (sourceToRatFunc68 p)
    algebraMap k[X] (RatFunc k) (p0.coeff 4) = f.coeff 4 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 3) = f.coeff 3 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 2) = f.coeff 2 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 1) = f.coeff 1 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 0) = f.coeff 0 := by
  intro r0 p0 f
  have hcenter :
      sexticDepressionR610 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) (p.coeff 5)) =
        algebraMap k[X] (RatFunc k) r0 := by
    dsimp only [r0, sexticDepressionR610]
    exact sexticDepressionR68_constantScale_eq_algebraMap p t
  have hf_eq : f = p0.map (algebraMap k[X] (RatFunc k)) := by
    dsimp only [f, p0]
    rw [hcenter]
    exact affineDepress_source_constantScale_map68 p t r0 ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hf_eq, Polynomial.coeff_map])

end PolynomialCore610

/-! ## Source-facing degree-one primitive -/

section SourcePrimitiveDegree610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 32000000 in
/-- Source-facing polynomial trajectory: the free core has representatives
in `k[x]`, the integrated primitive is a polynomial in those letters, and
that polynomial has derivative `C (j / t)` hence Newton degree one. -/
theorem normalized610ScaleZero_exists_primitivePolynomial
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      nonzeroLocalClearedFourteenthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C omicron ∧
      let hRF : RatFunc k := RatFunc.C t
      let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)
      let g : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 q)
      algebraMap k[X] (RatFunc k) A = f.coeff 4 ∧
        algebraMap k[X] (RatFunc k) B = f.coeff 3 ∧
        algebraMap k[X] (RatFunc k) C0 = f.coeff 2 ∧
        algebraMap k[X] (RatFunc k) D0 = f.coeff 1 ∧
        algebraMap k[X] (RatFunc k) E0 = f.coeff 0 ∧
        g.coeff 9 = RatFunc.C l ∧
        g.coeff 8 = integratedP610 (algebraMap k[X] (RatFunc k) A)
          (RatFunc.C alpha) ∧
        g.coeff 7 = integratedQ610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B) (RatFunc.C beta) ∧
        g.coeff 6 = integratedR610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (RatFunc.C alpha) (RatFunc.C gamma) ∧
        g.coeff 5 = integratedS610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta) ∧
        g.coeff 4 = integratedT610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C epsilon) ∧
        g.coeff 3 = integratedU610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C delta) (RatFunc.C zeta) ∧
        g.coeff 2 = integratedV610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C eta) ∧
        g.coeff 1 = integratedW610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
          (RatFunc.C theta) ∧
        g.coeff 0 = integratedX610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
          (RatFunc.C eta) (RatFunc.C iota) ∧
        derivative
            (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0) =
          C (j / t) ∧
        (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0).natDegree =
          1 := by
  dsimp only
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, ht, hj, hjdiv, hHsq, hrow, homicron,
      htraj⟩ :=
    normalized610ScaleZero_exists_integratedTrajectory hsource
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  let hRF : RatFunc k := RatFunc.C t
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 q)
  obtain ⟨hAmap, hBmap, hCmap, hDmap, hEmap⟩ :=
    constantScale_monicSextic_polynomialCore610 p t ht
  let r0 : k[X] := C ((6 * t ^ 5)⁻¹) * p.coeff 5
  let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
  let A : k[X] := p0.coeff 4
  let B : k[X] := p0.coeff 3
  let C0 : k[X] := p0.coeff 2
  let D0 : k[X] := p0.coeff 1
  let E0 : k[X] := p0.coeff 0
  have hA : algebraMap k[X] (RatFunc k) A = f.coeff 4 := by
    dsimp only [A, p0, r0, f, hRF, a5]
    exact hAmap
  have hB : algebraMap k[X] (RatFunc k) B = f.coeff 3 := by
    dsimp only [B, p0, r0, f, hRF, a5]
    exact hBmap
  have hC : algebraMap k[X] (RatFunc k) C0 = f.coeff 2 := by
    dsimp only [C0, p0, r0, f, hRF, a5]
    exact hCmap
  have hD : algebraMap k[X] (RatFunc k) D0 = f.coeff 1 := by
    dsimp only [D0, p0, r0, f, hRF, a5]
    exact hDmap
  have hE : algebraMap k[X] (RatFunc k) E0 = f.coeff 0 := by
    dsimp only [E0, p0, r0, f, hRF, a5]
    exact hEmap
  obtain ⟨hl, hP, hQ, hR, hS, hT, hU, hV, hW, hX, hprim⟩ := htraj
  have hP' : g.coeff 8 =
      integratedP610 (algebraMap k[X] (RatFunc k) A)
        (RatFunc.C alpha) := by
    simpa [hA] using hP
  have hQ' : g.coeff 7 =
      integratedQ610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B) (RatFunc.C beta) := by
    simpa [hA, hB] using hQ
  have hR' : g.coeff 6 =
      integratedR610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (RatFunc.C alpha) (RatFunc.C gamma) := by
    simpa [hA, hB, hC] using hR
  have hS' : g.coeff 5 =
      integratedS610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta) := by
    simpa [hA, hB, hC, hD] using hS
  have hT' : g.coeff 4 =
      integratedT610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C epsilon) := by
    simpa [hA, hB, hC, hD, hE] using hT
  have hU' : g.coeff 3 =
      integratedU610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C zeta) := by
    simpa [hA, hB, hC, hD, hE] using hU
  have hV' : g.coeff 2 =
      integratedV610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C eta) := by
    simpa [hA, hB, hC, hD, hE] using hV
  have hW' : g.coeff 1 =
      integratedW610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C theta) := by
    simpa [hA, hB, hC, hD, hE] using hW
  have hX' : g.coeff 0 =
      integratedX610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C iota) := by
    simpa [hA, hB, hC, hD, hE] using hX
  let prim : k[X] :=
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
      theta A B C0 D0 E0
  have hprimRF :
      degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) (g.coeff 0) =
        degreeZeroIntegratedPrimitive610 (RatFunc.C l)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
          (RatFunc.C theta) := by
    rw [← hA, ← hB, ← hC, ← hD, ← hE, hP', hQ', hR', hS', hT', hU',
      hV', hW', hX', hl]
    exact
      degreeZeroPrimitive610_eq_integratedPrimitive (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C theta) (RatFunc.C iota)
  have hmap :
      algebraMap k[X] (RatFunc k) prim =
        degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) (g.coeff 0) := by
    rw [hprimRF]
    exact algebraMap_degreeZeroPrimitivePolynomial610 l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0
  have hder :
      algebraMap k[X] (RatFunc k) (derivative prim) =
        algebraMap k[X] (RatFunc k) (C (j / t)) := by
    rw [← ratFuncDerivation46_polynomial]
    have hderiv :
        Differential.deriv (algebraMap k[X] (RatFunc k) prim) =
          RatFunc.C (j / t) := by
      rw [hmap]
      exact hprim
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply,
      RatFunc.algebraMap_C] using hderiv
  have hpolyder : derivative prim = C (j / t) :=
    (RatFunc.algebraMap_injective k) hder
  have hdeg : prim.natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 prim (j / t) hjdiv
      hpolyder
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq, ?_,
    ?_, ?_⟩
  · simpa [p, q] using hrow
  · simpa [p, q] using homicron
  · exact ⟨hA, hB, hC, hD, hE, hl, hP', hQ', hR', hS', hT', hU', hV',
      hW', hX', hpolyder, hdeg⟩

set_option maxHeartbeats 32000000 in
/-- A constant free core makes the polynomial primitive constant, hence
cannot support derivative `C (j / t) ≠ 0`. -/
theorem degreeZeroPrimitivePolynomial610_false_of_constant_core
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hle :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree ≤
        0 := by
    have hbase :
        (degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0).natDegree ≤ 0 := by
      simp only [degreeZeroBaseGroupPolynomial610]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree ≤ 0 := by
      simp only [degreeZeroAlphaGroupPolynomial610]
      compute_degree
      omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree ≤ 0 := by
      simp only [degreeZeroBetaGroupPolynomial610]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroDeltaGroupPolynomial610]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroEpsilonGroupPolynomial610]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroZetaGroupPolynomial610]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroEtaGroupPolynomial610]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree ≤ 0 := by
      simp only [degreeZeroThetaGroupPolynomial610]
      compute_degree
      omega
    simp only [degreeZeroPrimitivePolynomial610]
    exact natDegree_add8_le610 hbase (natDegree_smul_le_of_le610 alpha halpha)
      (natDegree_smul_le_of_le610 beta hbeta)
      (natDegree_smul_le_of_le610 delta hdelta)
      (natDegree_smul_le_of_le610 epsilon hepsilon)
      (natDegree_smul_le_of_le610 zeta hzeta)
      (natDegree_smul_le_of_le610 eta heta)
      (natDegree_smul_le_of_le610 theta htheta)
  omega

end SourcePrimitiveDegree610

/-! ## Unique-`A` cone -/

section HighACone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveHighARest610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : UniqueHighACone610 A B C0 D0 E0) :
    (degreeZeroPrimitiveHighARest610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  have hbase :
      (degreeZeroBaseGroupHighARest610 l A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroBaseGroupHighARest610]
    compute_degree
    omega
  have halpha :
      (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroAlphaGroupPolynomial610]
    compute_degree
    omega
  have hbeta :
      (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroBetaGroupPolynomial610]
    compute_degree
    omega
  have hdelta :
      (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroDeltaGroupPolynomial610]
    compute_degree
    omega
  have hepsilon :
      (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroEpsilonGroupPolynomial610]
    compute_degree
    omega
  have hzeta :
      (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroZetaGroupPolynomial610]
    compute_degree
    omega
  have heta :
      (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroEtaGroupPolynomial610]
    compute_degree
    omega
  have htheta :
      (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroThetaGroupPolynomial610]
    compute_degree
    omega
  simp only [degreeZeroPrimitiveHighARest610]
  exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
    (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
    (natDegree_smul_lt610 epsilon hepsilon) (natDegree_smul_lt610 zeta hzeta)
    (natDegree_smul_lt610 eta heta) (natDegree_smul_lt610 theta htheta)

theorem uniqueHighA_impossible_of_l_ne
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hl : l ≠ 0) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A B C0 D0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (-(10935 / 2239488 * l : k)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl)
  have hlead :
      ((-(10935 / 2239488 * l : k)) • A ^ 7).natDegree =
        7 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroPrimitiveHighARest610_natDegree_lt l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroPrimitivePolynomial610_eq_A7_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by
      rwa [hlead])] at hdeg
  rw [hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 16000000 in
theorem uniqueHighA_impossible_of_l_zero_B_pos
    (alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A B C0 D0 E0)
    (hBpos : 0 < B.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  have hc : (-(62720 / 2239488 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(62720 / 2239488 : k)) • (A ^ 6 * B)).natDegree =
        6 * A.natDegree + B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 6 hA) hBne,
      natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighA_noA6B_Rest610 0 alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0).natDegree <
        6 * A.natDegree + B.natDegree := by
    rcases hcone with ⟨hApos, hBlt, hC, hD, hE⟩
    have hbase :
        (degreeZeroBaseGroupHighA_noA6B_Rest610 0 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroBaseGroupHighA_noA6B_Rest610]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610]
      compute_degree
      omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroBetaGroupPolynomial610]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighA_noA6B_Rest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_A6B_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 16000000 in
theorem uniqueHighA_impossible_of_l_zero_B_zero_beta_ne
    (alpha beta delta epsilon zeta eta theta j : k)
    (A C0 D0 E0 : k[X]) (hj : j ≠ 0) (hbeta : beta ≠ 0)
    (hcone : UniqueHighACone610 A 0 C0 D0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon
            zeta eta theta A 0 C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta
          eta theta A 0 C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (2695 / 559872 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hbeta
  have hlead :
      ((2695 / 559872 * beta : k) • A ^ 6).natDegree =
        6 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighA_B0_noA6_Rest610 0 alpha beta delta epsilon
          zeta eta theta A C0 D0 E0).natDegree <
        6 * A.natDegree := by
    rcases hcone with ⟨hApos, _, hC, hD, hE⟩
    have hbase :
        (degreeZeroBaseGroupHighA_noA6B_Rest610 0 A 0 C0 D0 E0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroBaseGroupHighA_noA6B_Rest610]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A 0 C0 D0 E0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610]
      compute_degree
      omega
    have hbetaG :
        (degreeZeroBetaGroupNoA6Polynomial610 A 0 C0 D0 E0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroBetaGroupNoA6Polynomial610]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A 0 C0 E0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighA_B0_noA6_Rest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbetaG) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_betaA6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

end HighACone610

/-! ## Unique-`B` and unique-`D₀` extreme cones -/

section HighBAndDCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000 in
theorem degreeZeroPrimitivePolynomial610_eq_B5_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(36864 / 2239488 : k)) • B ^ 5 +
        degreeZeroPrimitiveHighBRest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighBRest610, degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighBRest610]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroPrimitivePolynomial610_eq_D3_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(829440 / 2239488 : k)) • D0 ^ 3 +
        degreeZeroPrimitiveHighDRest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighDRest610, degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighDRest610]
  module

set_option maxHeartbeats 16000000 in
theorem extremeHighB_impossible
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : ExtremeHighBCone610 A B C0 D0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hAB, hA7⟩
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  have hc : (-(36864 / 2239488 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(36864 / 2239488 : k)) • B ^ 5).natDegree =
        5 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighBRest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree <
        5 * B.natDegree := by
    have hbase :
        (degreeZeroBaseGroupHighBRest610 l A B C0 D0 E0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroBaseGroupHighBRest610]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610]
      compute_degree
      omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroBetaGroupPolynomial610]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighBRest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_B5_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

set_option maxHeartbeats 16000000 in
/-- If `D₀` is the only nonconstant free-core letter, the face `D₀³` has
degree at least three. -/
theorem uniqueNonconstantD0_impossible
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hDpos : 0 < D0.natDegree)
    (hE : E0.natDegree = 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hDne : D0 ≠ 0 := by
    intro hD0
    simp [hD0] at hDpos
  have hc : (-(829440 / 2239488 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(829440 / 2239488 : k)) • D0 ^ 3).natDegree =
        3 * D0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighDRest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree <
        3 * D0.natDegree := by
    have hbase :
        (degreeZeroBaseGroupHighDRest610 l A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroBaseGroupHighDRest610]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610]
      compute_degree
      omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroBetaGroupPolynomial610]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighDRest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_D3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

set_option maxHeartbeats 16000000 in
/-- If `B` is the only nonconstant free-core letter, the face `B⁵` has
degree at least five. -/
theorem uniqueNonconstantB_impossible
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hBpos : 0 < B.natDegree)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hcone : ExtremeHighBCone610 A B C0 D0 E0 := by
    refine ⟨⟨hBpos, hA.symm ▸ hBpos, hC.symm ▸ hBpos, hD.symm ▸ hBpos,
        hE.symm ▸ hBpos⟩, ?_, ?_⟩
    · omega
    · omega
  exact extremeHighB_impossible l alpha beta delta epsilon zeta eta theta
    j A B C0 D0 E0 hj hcone hder

set_option maxHeartbeats 16000000 in
/-- If `E₀` is the only nonconstant free-core letter and `β ≠ 0`, the
face `β E₀²` has degree at least two. -/
theorem uniqueNonconstantE0_impossible_of_beta_ne
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0) (hbeta : beta ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hEpos : 0 < E0.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hEne : E0 ≠ 0 := by
    intro hE0
    simp [hE0] at hEpos
  have hc : (326592 / 559872 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hbeta
  have hlead :
      ((326592 / 559872 * beta : k) • E0 ^ 2).natDegree =
        2 * E0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighERest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree <
        2 * E0.natDegree := by
    have hbase :
        (degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroBaseGroupPolynomial610]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610]
      compute_degree
      omega
    have hbetaG :
        (degreeZeroBetaGroupNoE2Polynomial610 A B C0 D0 E0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroBetaGroupNoE2Polynomial610]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighERest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbetaG) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_betaE2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end HighBAndDCone610

/-! ## Honest residual -/

section Residual610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact residual of the scale-zero cone cascade.

The free core has polynomial representatives, the integrated primitive
has Newton degree one, a constant core is impossible, the unique-`A`
cone is empty except the two leftover chambers `L = 0` with `B`
constant (and `β = 0` if `B = 0`), the extreme unique-`B` cone
`3 deg A < 2 deg B` with `7 deg A < 5 deg B` is empty, a unique
nonconstant `B` or `D₀` is empty, and a unique nonconstant `E₀` with
`β ≠ 0` is empty.

The leaf is not closed.  A nonconstant polynomial core remains in which
either two or more letters share the maximal degree, or else `A`
uniquely leads with `L = 0` and `B` a constant, and in the `B = 0`
chamber also `β = 0`, or else `E₀` is the unique nonconstant letter
with `β = 0`.  The already-constant first integrals `κ, λ, μ` and the
weight-seventy residual `ο` are not consumed. -/
theorem normalized610ScaleZero_coneCascadeResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C (j / t) ∧
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      (UniqueHighACone610 A B C0 D0 E0 →
        l = 0 ∧ B.natDegree = 0 ∧ (B = 0 → beta = 0)) ∧
      ¬ ExtremeHighBCone610 A B C0 D0 E0 ∧
      ¬ (A.natDegree = 0 ∧ 0 < B.natDegree ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ 0 < E0.natDegree ∧ beta ≠ 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
      _hrow, _homicron, hcore⟩ :=
    normalized610ScaleZero_exists_primitivePolynomial hsource
  obtain ⟨hA, hB, hC, hD, hE, hl, hP, hQ, hR, hS, hT, hU, hV, hW, hX,
      hder, hdeg⟩ := hcore
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq, hder,
    hdeg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hconst
    exact degreeZeroPrimitivePolynomial610_false_of_constant_core
      l alpha beta delta epsilon zeta eta theta (j / t) A B C0 D0 E0
      hjdiv hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.1
      hconst.2.2.2.2 hder
  · intro hcone
    refine ⟨?_, ?_, ?_⟩
    · by_contra hlne
      exact uniqueHighA_impossible_of_l_ne l alpha beta delta epsilon
        zeta eta theta (j / t) A B C0 D0 E0 hlne hjdiv hcone hder
    · by_contra hBpos
      have hpos : 0 < B.natDegree := Nat.pos_of_ne_zero hBpos
      have hl0 : l = 0 := by
        by_contra hlne
        exact uniqueHighA_impossible_of_l_ne l alpha beta delta epsilon
          zeta eta theta (j / t) A B C0 D0 E0 hlne hjdiv hcone hder
      subst hl0
      exact uniqueHighA_impossible_of_l_zero_B_pos alpha beta delta
        epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hcone hpos hder
    · intro hB0
      by_contra hbetane
      have hl0 : l = 0 := by
        by_contra hlne
        exact uniqueHighA_impossible_of_l_ne l alpha beta delta epsilon
          zeta eta theta (j / t) A B C0 D0 E0 hlne hjdiv hcone hder
      subst hl0
      subst hB0
      exact uniqueHighA_impossible_of_l_zero_B_zero_beta_ne alpha beta
        delta epsilon zeta eta theta (j / t) A C0 D0 E0 hjdiv hbetane
        hcone hder
  · intro hcone
    exact extremeHighB_impossible l alpha beta delta epsilon zeta eta
      theta (j / t) A B C0 D0 E0 hjdiv hcone hder
  · intro hBonly
    exact uniqueNonconstantB_impossible l alpha beta delta epsilon zeta
      eta theta (j / t) A B C0 D0 E0 hjdiv hBonly.1 hBonly.2.1
      hBonly.2.2.1 hBonly.2.2.2.1 hBonly.2.2.2.2 hder
  · intro hDonly
    exact uniqueNonconstantD0_impossible l alpha beta delta epsilon zeta
      eta theta (j / t) A B C0 D0 E0 hjdiv hDonly.1 hDonly.2.1
      hDonly.2.2.1 hDonly.2.2.2.1 hDonly.2.2.2.2 hder
  · intro hEonly
    exact uniqueNonconstantE0_impossible_of_beta_ne l alpha beta delta
      epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hEonly.2.2.2.2.2
      hEonly.1 hEonly.2.1 hEonly.2.2.1 hEonly.2.2.2.1 hEonly.2.2.2.2.1
      hder

end Residual610

#print axioms natDegree_eq_one_of_derivative_eq_nonzero_C610
#print axioms smul_add_lower_ne_C610
#print axioms UniqueHighACone610
#print axioms UniqueHighBCone610
#print axioms ExtremeHighBCone610
#print axioms degreeZeroBaseGroupPolynomial610
#print axioms degreeZeroPrimitivePolynomial610
#print axioms degreeZeroIntegratedPrimitive610
#print axioms degreeZeroPrimitive610_eq_integratedPrimitive
#print axioms algebraMap_degreeZeroPrimitivePolynomial610
#print axioms constantScale_monicSextic_polynomialCore610
#print axioms normalized610ScaleZero_exists_primitivePolynomial
#print axioms degreeZeroPrimitivePolynomial610_false_of_constant_core
#print axioms uniqueHighA_impossible_of_l_ne
#print axioms uniqueHighA_impossible_of_l_zero_B_pos
#print axioms uniqueHighA_impossible_of_l_zero_B_zero_beta_ne
#print axioms extremeHighB_impossible
#print axioms uniqueNonconstantD0_impossible
#print axioms uniqueNonconstantB_impossible
#print axioms uniqueNonconstantE0_impossible_of_beta_ne
#print axioms normalized610ScaleZero_coneCascadeResidual

end Max11DegreeRoutes
