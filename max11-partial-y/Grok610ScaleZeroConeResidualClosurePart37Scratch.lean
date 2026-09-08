import Grok610ScaleZeroConeResidualClosurePart36Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section HighAResidualCone610

variable {k : Type*} [Field k] [CharZero k]

theorem natDegree_add_C_of_natDegree_eq_zero
    (c : k) {p : k[X]} (hp : p.natDegree = 0) :
    (p + C c).natDegree = 0 := by
  have hle : (p + C c).natDegree ≤ 0 :=
    (natDegree_add_le p (C c)).trans (max_le (hp.le) (by simp [natDegree_C]))
  exact natDegree_eq_zero_of_le_zero610 hle

end HighAResidualCone610

end Max11DegreeRoutes
