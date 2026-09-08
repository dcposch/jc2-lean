import Grok610ScaleZeroConeCascadeScratch

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

/-- Primitive with the face `A⁶ B` deleted, `A⁷` retained. -/
def degreeZeroPrimitiveNoA6B610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(10935 / 2239488 * l : k)) • A ^ 7 +
    degreeZeroPrimitiveHighA_noA6B_Rest610 l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0

end ResidualSplittings610

end Max11DegreeRoutes
