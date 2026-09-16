import Grok610ScaleZeroValuationEndgameScratch
import LowScale68ScaleZero

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem natDegree_add_lt610 {p q : k[X]} {d : ℕ}
    (hp : p.natDegree < d) (hq : q.natDegree < d) :
    (p + q).natDegree < d :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem natDegree_add_le610 {p q : k[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    (p + q).natDegree ≤ d :=
  (natDegree_add_le p q).trans (max_le hp hq)

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem natDegree_smul_le610 (c : k) (p : k[X]) :
    (c • p).natDegree ≤ p.natDegree := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, natDegree_zero]
    exact Nat.zero_le _
  · rw [natDegree_smul _ hc]

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Unique-max `A` cone: `A` strictly outranks the other four free letters. -/
def UniqueHighACone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    B.natDegree < A.natDegree ∧
    C0.natDegree < A.natDegree ∧
    D0.natDegree < A.natDegree ∧
    E0.natDegree < A.natDegree

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Unique-max `B` cone. -/
def UniqueHighBCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    A.natDegree < B.natDegree ∧
    C0.natDegree < B.natDegree ∧
    D0.natDegree < B.natDegree ∧
    E0.natDegree < B.natDegree

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Polynomial pullback of `degreeZeroDeltaGroup610`. -/
def degreeZeroDeltaGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (49 / 5184 : k) • A ^ 5 -
    (360 / 5184 : k) • (A ^ 3 * C0) -
    (600 / 5184 : k) • (A ^ 2 * B ^ 2) +
    (1440 / 5184 : k) • (A * B * D0) +
    (720 / 5184 : k) • (A * C0 ^ 2) +
    (720 / 5184 : k) • (B ^ 2 * C0) -
    (2160 / 5184 : k) • D0 ^ 2

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Polynomial pullback of `degreeZeroEpsilonGroup610`. -/
def degreeZeroEpsilonGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (-(7 / 54 : k)) • (A ^ 3 * B) +
    (9 / 54 : k) • (A ^ 2 * D0) +
    (24 / 54 : k) • (A * B * C0) +
    (4 / 54 : k) • B ^ 3 -
    (36 / 54 : k) • (C0 * D0)

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Polynomial pullback of `degreeZeroZetaGroup610`. -/
def degreeZeroZetaGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (-(7 / 192 : k)) • A ^ 4 +
    (40 / 192 : k) • (A ^ 2 * C0) +
    (48 / 192 : k) • (A * B ^ 2) -
    (96 / 192 : k) • (B * D0) -
    (48 / 192 : k) • C0 ^ 2

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Polynomial pullback of `degreeZeroEtaGroup610`. -/
def degreeZeroEtaGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (7 / 36 : k) • (A ^ 2 * B) -
    (12 / 36 : k) • (A * D0) -
    (12 / 36 : k) • (B * C0)

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Polynomial pullback of `degreeZeroThetaGroup610`. -/
def degreeZeroThetaGroupPolynomial610 (A B C0 E0 : k[X]) : k[X] :=
  (7 / 216 : k) • A ^ 3 -
    (36 / 216 : k) • (A * C0) -
    (18 / 216 : k) • B ^ 2 +
    (216 / 216 : k) • E0

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PolynomialCore610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem natDegree_smul_lt610 (c : k) {p : k[X]} {d : ℕ}
    (hp : p.natDegree < d) : (c • p).natDegree < d :=
  (natDegree_smul_le610 c p).trans_lt hp

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem natDegree_smul_le_of_le610 (c : k) {p : k[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) : (c • p).natDegree ≤ d :=
  (natDegree_smul_le610 c p).trans hp

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Extreme high-`B` subcone on which `B⁵` outranks `A⁶ B` and `A⁷`. -/
def ExtremeHighBCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  UniqueHighBCone610 A B C0 D0 E0 ∧
    3 * A.natDegree < 2 * B.natDegree ∧
    7 * A.natDegree < 5 * B.natDegree

end DegreeLemmas610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroBaseGroupPolynomial610_eq_A7_add_rest
    (l : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0 =
      (-(10935 / 2239488 * l : k)) • A ^ 7 +
        degreeZeroBaseGroupHighARest610 l A B C0 D0 E0 := by
  simp only [degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighARest610]
  module

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end PrimitivePolynomial610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
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

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section SourcePrimitiveDegree610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
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
    rw [eq_C_of_natDegree_eq_zero hA, eq_C_of_natDegree_eq_zero hB,
      eq_C_of_natDegree_eq_zero hC, eq_C_of_natDegree_eq_zero hD,
      eq_C_of_natDegree_eq_zero hE]
    simp only [degreeZeroPrimitivePolynomial610, degreeZeroBaseGroupPolynomial610,
      degreeZeroAlphaGroupPolynomial610, degreeZeroBetaGroupPolynomial610,
      degreeZeroDeltaGroupPolynomial610, degreeZeroEpsilonGroupPolynomial610,
      degreeZeroZetaGroupPolynomial610, degreeZeroEtaGroupPolynomial610,
      degreeZeroThetaGroupPolynomial610, ← Polynomial.C_pow, ← Polynomial.C_mul,
      smul_C, ← Polynomial.C_add, ← Polynomial.C_sub, natDegree_C, le_refl]
  omega

end SourcePrimitiveDegree610

end Max11DegreeRoutes
