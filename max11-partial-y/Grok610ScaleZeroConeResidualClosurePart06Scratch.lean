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

/-- Combined `A⁵` coefficient on the unique-`A` chamber `L = 0`,
`B = 0`, `β = 0`, `D₀` constant. -/
def highA_l0_B0_beta0_A5Coefficient610 (delta : k) (D0 : k[X]) : k[X] :=
  (92160 / 2239488 : k) • D0 + C (49 / 5184 * delta : k)

end ExtraCones610

end Max11DegreeRoutes
