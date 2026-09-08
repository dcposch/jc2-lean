import Grok610ScaleZeroConeResidualClosurePart05Scratch
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

theorem highA_l0_constB_A6Coefficient610_natDegree_eq_zero
    (beta : k) {B : k[X]} (hB : B.natDegree = 0) :
    (highA_l0_constB_A6Coefficient610 beta B).natDegree = 0 := by
  have hsmul : ((-(62720 / 2239488 : k)) • B).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ B).trans hB.le
  have hc : (C (2695 / 559872 * beta : k) : k[X]).natDegree = 0 :=
    natDegree_C _
  change ((-(62720 / 2239488 : k)) • B +
      C (2695 / 559872 * beta : k)).natDegree = 0
  exact natDegree_eq_zero_of_le_zero610 <|
    (natDegree_add_le _ _).trans (max_le hsmul hc.le)

end HighAResidualCone610

end Max11DegreeRoutes
