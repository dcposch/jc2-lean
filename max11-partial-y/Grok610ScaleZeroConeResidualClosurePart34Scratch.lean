import Grok610ScaleZeroConeResidualClosurePart19Scratch

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

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_C03_faces_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
        (414720 / 2239488 : k) • (B * C0 ^ 3) +
          ((-(36288 / 559872 * beta : k)) • C0 ^ 3) +
            degreeZeroPrimitiveNoC03Rest610 l alpha beta delta epsilon zeta
              eta theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveNoC03Rest610, degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupNoC03Polynomial610, degreeZeroBetaGroupPolynomial610,
    degreeZeroBetaGroupNoC03Polynomial610]
  module

end ResidualSplittings610

end Max11DegreeRoutes
