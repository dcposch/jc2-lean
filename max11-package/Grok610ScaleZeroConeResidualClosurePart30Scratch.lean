import Grok610ScaleZeroConeResidualClosurePart06Scratch

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

theorem highA_l0_B0_beta0_A5_combined_eq
    (delta : k) (A D0 : k[X]) :
    (92160 / 2239488 : k) • (A ^ 5 * D0) +
        ((49 / 5184 * delta : k) • A ^ 5) =
      A ^ 5 * highA_l0_B0_beta0_A5Coefficient610 delta D0 := by
  simp only [highA_l0_B0_beta0_A5Coefficient610, smul_eq_C_mul]
  ring

end ResidualSplittings610

end Max11DegreeRoutes
