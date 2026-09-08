import Grok610ScaleZeroConeResidualClosurePart14Scratch

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

theorem degreeZeroPrimitive_l0_B0_D00_delta0_zeta0_eq_A3_add_rest
    (theta : k) (A C0 E0 : k[X]) :
    degreeZeroPrimitive_l0_B0_D00_beta0_610 0 0 theta A C0 E0 =
      (7 / 216 * theta : k) • A ^ 3 +
        ((-(36 / 216 * theta : k)) • (A * C0) + theta • E0) := by
  simp only [degreeZeroPrimitive_l0_B0_D00_beta0_610, zero_mul, zero_smul,
    smul_zero, add_zero, sub_zero, zero_add]
  module

end HighAResidualCone610

end Max11DegreeRoutes
