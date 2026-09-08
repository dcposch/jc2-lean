import Grok610ScaleZeroConeResidualClosurePart08Scratch
import Grok610ScaleZeroConeResidualClosurePart20Scratch

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

set_option maxHeartbeats 8000000 in
theorem degreeZeroPrimitivePolynomial610_eq_A6B_add_noA6B_withA7
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(62720 / 2239488 : k)) • (A ^ 6 * B) +
        degreeZeroPrimitiveNoA6B610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 := by
  rw [degreeZeroPrimitivePolynomial610_eq_A7_add_rest,
    degreeZeroPrimitiveHighARest610_eq_A6B_add_noA6B]
  simp only [degreeZeroPrimitiveNoA6B610]
  module

end ResidualSplittings610

end Max11DegreeRoutes
