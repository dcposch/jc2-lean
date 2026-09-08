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
