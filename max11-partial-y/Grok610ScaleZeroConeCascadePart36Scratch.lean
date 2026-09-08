import Grok610ScaleZeroConeCascadePart28Scratch
import Grok610ScaleZeroConeCascadePart29Scratch
import Grok610ScaleZeroConeCascadePart35Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000 in
theorem degreeZeroPrimitivePolynomial610_eq_A7_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(10935 / 2239488 * l : k)) • A ^ 7 +
        degreeZeroPrimitiveHighARest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighARest610,
    degreeZeroBaseGroupPolynomial610_eq_A7_add_rest]
  module

end PrimitivePolynomial610

end Max11DegreeRoutes
