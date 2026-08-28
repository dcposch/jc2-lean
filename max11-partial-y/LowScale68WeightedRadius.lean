import LowScale68PolynomialBoundary
import Mathlib.Algebra.Polynomial.Expand

/-! # Integral maximal weighted radius for the `(6,8)` scale-zero leaf

The natural degree radius of the five depressed sextic loads has rational
weights `deg(A)/2`, `deg(B)/3`, `deg(C)/4`, `deg(D)/5`, and `deg(E)/6`.
Expanding every polynomial by `x ↦ x^60` clears all five denominators.  The
integer below is then the exact maximum radius; it supplies all five degree
bounds and, whenever one load is nonconstant, an attained nonzero boundary
coefficient.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section WeightedRadius68

variable {k : Type*} [Field k] [CharZero k]

/-- The denominator-cleared maximal weighted radius of the five sextic
coefficient loads. -/
def weightedRadius68 (A B C0 D E : k[X]) : ℕ :=
  max (30 * A.natDegree)
    (max (20 * B.natDegree)
      (max (15 * C0.natDegree) (max (12 * D.natDegree) (10 * E.natDegree))))

/-- Expanding by sixty gives the five degree bounds at the maximal radius. -/
theorem weightedRadius68_degreeBounds (A B C0 D E : k[X]) :
    (expand k 60 A).natDegree ≤ 2 * weightedRadius68 A B C0 D E ∧
    (expand k 60 B).natDegree ≤ 3 * weightedRadius68 A B C0 D E ∧
    (expand k 60 C0).natDegree ≤ 4 * weightedRadius68 A B C0 D E ∧
    (expand k 60 D).natDegree ≤ 5 * weightedRadius68 A B C0 D E ∧
    (expand k 60 E).natDegree ≤ 6 * weightedRadius68 A B C0 D E := by
  simp only [natDegree_expand, weightedRadius68]
  omega

/-- A nonconstant load makes the denominator-cleared radius positive. -/
theorem weightedRadius68_pos (A B C0 D E : k[X])
    (hload : 0 < max (max A.natDegree B.natDegree)
      (max C0.natDegree (max D.natDegree E.natDegree))) :
    0 < weightedRadius68 A B C0 D E := by
  simp only [weightedRadius68]
  omega

/-- At least one of the five expanded polynomials attains the maximal
weighted boundary. -/
theorem weightedRadius68_boundary_attained (A B C0 D E : k[X])
    (hn : 0 < weightedRadius68 A B C0 D E) :
    (expand k 60 A).coeff (2 * weightedRadius68 A B C0 D E) ≠ 0 ∨
    (expand k 60 B).coeff (3 * weightedRadius68 A B C0 D E) ≠ 0 ∨
    (expand k 60 C0).coeff (4 * weightedRadius68 A B C0 D E) ≠ 0 ∨
    (expand k 60 D).coeff (5 * weightedRadius68 A B C0 D E) ≠ 0 ∨
    (expand k 60 E).coeff (6 * weightedRadius68 A B C0 D E) ≠ 0 := by
  have hcases :
      weightedRadius68 A B C0 D E = 30 * A.natDegree ∨
      weightedRadius68 A B C0 D E = 20 * B.natDegree ∨
      weightedRadius68 A B C0 D E = 15 * C0.natDegree ∨
      weightedRadius68 A B C0 D E = 12 * D.natDegree ∨
      weightedRadius68 A B C0 D E = 10 * E.natDegree := by
    simp only [weightedRadius68]
    omega
  rcases hcases with hA | hB | hC | hD | hE
  · left
    have hdeg : 0 < A.natDegree := by omega
    have hne : A ≠ 0 := by
      intro hz
      simp [hz] at hdeg
    have hindex : 2 * weightedRadius68 A B C0 D E = A.natDegree * 60 := by
      rw [hA]
      omega
    rw [hindex, coeff_expand_mul (R := k) (by omega)]
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hne
  · right; left
    have hdeg : 0 < B.natDegree := by omega
    have hne : B ≠ 0 := by
      intro hz
      simp [hz] at hdeg
    have hindex : 3 * weightedRadius68 A B C0 D E = B.natDegree * 60 := by
      rw [hB]
      omega
    rw [hindex, coeff_expand_mul (R := k) (by omega)]
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hne
  · right; right; left
    have hdeg : 0 < C0.natDegree := by omega
    have hne : C0 ≠ 0 := by
      intro hz
      simp [hz] at hdeg
    have hindex : 4 * weightedRadius68 A B C0 D E = C0.natDegree * 60 := by
      rw [hC]
      omega
    rw [hindex, coeff_expand_mul (R := k) (by omega)]
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hne
  · right; right; right; left
    have hdeg : 0 < D.natDegree := by omega
    have hne : D ≠ 0 := by
      intro hz
      simp [hz] at hdeg
    have hindex : 5 * weightedRadius68 A B C0 D E = D.natDegree * 60 := by
      rw [hD]
      omega
    rw [hindex, coeff_expand_mul (R := k) (by omega)]
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hne
  · right; right; right; right
    have hdeg : 0 < E.natDegree := by omega
    have hne : E ≠ 0 := by
      intro hz
      simp [hz] at hdeg
    have hindex : 6 * weightedRadius68 A B C0 D E = E.natDegree * 60 := by
      rw [hE]
      omega
    rw [hindex, coeff_expand_mul (R := k) (by omega)]
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hne

/-- Complete maximal-radius package: after the common expansion, all five
weighted bounds hold and one top coefficient is nonzero. -/
theorem exists_positive_integral_weightedRadius68 (A B C0 D E : k[X])
    (hload : 0 < max (max A.natDegree B.natDegree)
      (max C0.natDegree (max D.natDegree E.natDegree))) :
    ∃ n : ℕ, 0 < n ∧
      (expand k 60 A).natDegree ≤ 2 * n ∧
      (expand k 60 B).natDegree ≤ 3 * n ∧
      (expand k 60 C0).natDegree ≤ 4 * n ∧
      (expand k 60 D).natDegree ≤ 5 * n ∧
      (expand k 60 E).natDegree ≤ 6 * n ∧
      ((expand k 60 A).coeff (2 * n) ≠ 0 ∨
       (expand k 60 B).coeff (3 * n) ≠ 0 ∨
       (expand k 60 C0).coeff (4 * n) ≠ 0 ∨
       (expand k 60 D).coeff (5 * n) ≠ 0 ∨
       (expand k 60 E).coeff (6 * n) ≠ 0) := by
  let n := weightedRadius68 A B C0 D E
  refine ⟨n, weightedRadius68_pos A B C0 D E hload, ?_⟩
  have hb := weightedRadius68_degreeBounds A B C0 D E
  have ha := weightedRadius68_boundary_attained A B C0 D E
    (weightedRadius68_pos A B C0 D E hload)
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2, ha⟩

/-- A nonzero terminal one-form row rules out the degenerate situation in
which all five sextic loads are constant. -/
theorem terminalRow68_forces_nonconstant_load
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hrow : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) D E = C terminal) :
    0 < max (max A.natDegree B.natDegree)
      (max C0.natDegree (max D.natDegree E.natDegree)) := by
  by_contra hnot
  have hdegrees : A.natDegree = 0 ∧ B.natDegree = 0 ∧
      C0.natDegree = 0 ∧ D.natDegree = 0 ∧ E.natDegree = 0 := by
    omega
  have hbounds := integratedPolynomial68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B C0 D E 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hEderiv : derivative E = 0 := derivative_eq_zero.mpr hdegrees.2.2.2.2
  have hVderiv : derivative
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) = 0 := by
    apply derivative_eq_zero.mpr
    omega
  have hterminal0 : terminal = 0 := by
    apply C_injective
    simpa [lowerRowZeroPolynomial68, hEderiv, hVderiv] using hrow.symm
  exact hterminal hterminal0

end WeightedRadius68

#print axioms weightedRadius68_degreeBounds
#print axioms weightedRadius68_boundary_attained
#print axioms exists_positive_integral_weightedRadius68
#print axioms terminalRow68_forces_nonconstant_load

end Max11DegreeRoutes
