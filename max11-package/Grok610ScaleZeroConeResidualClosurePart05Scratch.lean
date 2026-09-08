import Grok610ScaleZeroConeCascadeScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ExtraCones610

variable {k : Type*} [Field k] [CharZero k]

/-- Combined `A⁶` coefficient on the unique-`A` chamber `L = 0`,
`deg B = 0`. -/
def highA_l0_constB_A6Coefficient610 (beta : k) (B : k[X]) : k[X] :=
  (-(62720 / 2239488 : k)) • B + C (2695 / 559872 * beta : k)

end ExtraCones610

end Max11DegreeRoutes
