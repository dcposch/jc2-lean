import LowScale68SecondaryLaterDeepFiveToSixRowOnePart06Scratch

/-! # The row-one face in the later-deep five-to-six chamber

This module closes the two spurious families left by the I4/I3/row-zero
classification.  The only surviving top packet is `e = 0`, `a*b = 3*d`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSixRowOne68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

end LaterDeepFiveToSixRowOne68

#print axioms coeff_mul_mul_derivative_at_bounds_nonneg68
#print axioms firstSecondaryCoreRowOnePolynomial68_coeff_fiveToSix
#print axioms cubicLoadRowOnePolynomial68_zero_beta_delta_exact
#print axioms integratedLowerRowOnePolynomial68_fiveToSix_forces_firstSecondaryOne
#print axioms firstSecondary_fiveToSix_classification_with_one68
#print axioms firstSecondary_mainFamily_attainment_split68
#print axioms firstSecondary_mainFamily_saturates_face68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_mainFamily68

end Max11DegreeRoutes
