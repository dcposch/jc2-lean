import Grok610ScaleZeroConeCascadePart13Scratch
import Grok610ScaleZeroConeCascadePart14Scratch

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
theorem degreeZeroBaseGroupPolynomial610_eq_A7_add_rest
    (l : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0 =
      (-(10935 / 2239488 * l : k)) • A ^ 7 +
        degreeZeroBaseGroupHighARest610 l A B C0 D0 E0 := by
  simp only [degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighARest610]
  module

end PrimitivePolynomial610

end Max11DegreeRoutes
