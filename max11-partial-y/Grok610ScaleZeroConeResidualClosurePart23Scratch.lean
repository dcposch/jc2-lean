import Grok610ScaleZeroConeResidualClosurePart05Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

theorem highA_l0_constB_A6_combined_eq
    (beta : k) (A B : k[X]) :
    (-(62720 / 2239488 : k)) • (A ^ 6 * B) +
        ((2695 / 559872 * beta : k) • A ^ 6) =
      A ^ 6 * highA_l0_constB_A6Coefficient610 beta B := by
  simp only [highA_l0_constB_A6Coefficient610, smul_eq_C_mul]
  ring

end ResidualSplittings610

end Max11DegreeRoutes
