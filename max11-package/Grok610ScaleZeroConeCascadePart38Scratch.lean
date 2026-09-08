import Grok610ScaleZeroConeCascadePart28Scratch
import Grok610ScaleZeroConeCascadePart33Scratch

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
theorem degreeZeroPrimitivePolynomial610_eq_betaA6_add_rest
    (alpha beta delta epsilon zeta eta theta : k)
    (A C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta eta
        theta A 0 C0 D0 E0 =
      ((2695 / 559872 * beta : k) • A ^ 6) +
        degreeZeroPrimitiveHighA_B0_noA6_Rest610 0 alpha beta delta
          epsilon zeta eta theta A C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighA_B0_noA6_Rest610,
    degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighA_noA6B_Rest610,
    degreeZeroBetaGroupPolynomial610,
    degreeZeroBetaGroupNoA6Polynomial610, zero_mul, mul_zero, neg_zero,
    zero_smul, smul_zero, zero_add, add_zero, sub_zero]
  module

end PrimitivePolynomial610

end Max11DegreeRoutes
