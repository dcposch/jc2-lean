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

theorem natDegree_smul_le610 (c : k) (p : k[X]) :
    (c • p).natDegree ≤ p.natDegree := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, natDegree_zero]
    exact Nat.zero_le _
  · rw [natDegree_smul _ hc]

end DegreeLemmas610

end Max11DegreeRoutes
