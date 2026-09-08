import Grok610ScaleZeroConeResidualClosurePart07Scratch

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

theorem uniqueC0_cubicFaces_eq_coefficient_mul
    (l beta : k) (A B C0 : k[X]) :
    (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
        (414720 / 2239488 : k) • (B * C0 ^ 3) +
          ((-(36288 / 559872 * beta : k)) • C0 ^ 3) =
      uniqueC0_cubicCoefficient610 l beta A B * C0 ^ 3 := by
  simp only [uniqueC0_cubicCoefficient610, smul_eq_C_mul]
  ring

end ResidualSplittings610

end Max11DegreeRoutes
