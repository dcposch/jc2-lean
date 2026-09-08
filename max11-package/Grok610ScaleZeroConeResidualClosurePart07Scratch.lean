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

/-- Combined `C₀³` coefficient on a unique-nonconstant `C₀` chamber. -/
def uniqueC0_cubicCoefficient610 (l beta : k) (A B : k[X]) : k[X] :=
  (419904 / 2239488 * l : k) • A +
    (414720 / 2239488 : k) • B +
    C (-(36288 / 559872 * beta : k))

end ExtraCones610

end Max11DegreeRoutes
