import Grok610ScaleZeroConeResidualClosurePart06Scratch
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

theorem highA_l0_B0_beta0_A5Coefficient610_natDegree_eq_zero
    (delta : k) {D0 : k[X]} (hD : D0.natDegree = 0) :
    (highA_l0_B0_beta0_A5Coefficient610 delta D0).natDegree = 0 := by
  have hsmul : ((92160 / 2239488 : k) • D0).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ D0).trans hD.le
  have hc : (C (49 / 5184 * delta : k) : k[X]).natDegree = 0 :=
    natDegree_C _
  change ((92160 / 2239488 : k) • D0 + C (49 / 5184 * delta : k)).natDegree = 0
  exact natDegree_eq_zero_of_le_zero610 <|
    (natDegree_add_le _ _).trans (max_le hsmul hc.le)

end HighAResidualCone610

end Max11DegreeRoutes
