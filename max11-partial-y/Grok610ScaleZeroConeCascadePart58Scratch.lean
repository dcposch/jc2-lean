import Grok610ScaleZeroConeCascadePart28Scratch
import Grok610ScaleZeroConeCascadePart32Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighBAndDCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000 in
theorem degreeZeroPrimitivePolynomial610_eq_D3_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(829440 / 2239488 : k)) • D0 ^ 3 +
        degreeZeroPrimitiveHighDRest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighDRest610, degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighDRest610]
  module

end HighBAndDCone610

end Max11DegreeRoutes
