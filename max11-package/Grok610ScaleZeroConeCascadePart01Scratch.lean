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
