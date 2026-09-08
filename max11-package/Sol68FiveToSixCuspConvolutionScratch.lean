import Sol68FiveToSixCuspConvolutionPart03Scratch

/-! # Finite discriminant convolution at an arbitrary cusp depth

The exact first-integral combination from the third-jet file works at every
contracted depth.  Reflection turns its leading term `Delta*d` into an
ordinary coefficient convolution.  Since the edge coefficient of `d` is
nonzero, strong induction kills every `Delta` jet strictly before the first
load `mu = min(S, 7N-2G-S)`.  At `mu` the same convolution leaves exactly
the `d^2`, `zeta*A`, or simultaneous loaded scalar.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspConvolution68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

#print axioms mul_coeff_eq_left_edge_of_lower_zero68
#print axioms coeff_mul_at_reflect_of_left_lower_zero68
#print axioms fiveToSix_contractedCusp_firstLoad_convolution68
#print axioms fiveToSix_contractedEarlierFiniteStop_convolution68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_convolution_assembly68

end FiveToSixCuspConvolution68

end Max11DegreeRoutes
