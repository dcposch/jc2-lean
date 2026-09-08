import Grok610ScaleZeroConeResidualClosurePart15Scratch
import Grok610ScaleZeroConeResidualClosurePart16Scratch

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

theorem degreeZeroE0Terms610_eq_linear_mul
    (l alpha theta : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroE0Terms610 l alpha theta A B C0 D0 E0 =
      degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0 * E0 := by
  simp only [degreeZeroE0Terms610, degreeZeroE0LinearPolynomial610,
    smul_eq_C_mul]
  ring

end ResidualSplittings610

end Max11DegreeRoutes
