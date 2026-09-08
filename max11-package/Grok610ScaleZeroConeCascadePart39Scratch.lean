import Grok610ScaleZeroConeCascadePart28Scratch
import Grok610ScaleZeroConeCascadePart34Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_betaE2_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      ((326592 / 559872 * beta : k) • E0 ^ 2) +
        degreeZeroPrimitiveHighERest610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighERest610, degreeZeroBetaGroupPolynomial610,
    degreeZeroBetaGroupNoE2Polynomial610]
  module

end PrimitivePolynomial610

end Max11DegreeRoutes
