import LowScale68SecondaryLaterDeepFiveToSixEndgamePart02Scratch

/-! # The remaining later-deep five-to-six window

The two invariant faces are already available.  Here the terminal lower row
is shown to retain its ordinary first-secondary scalar throughout
`5n < 2g ≤ 6n`, despite the deeper load chamber.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSix68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 14000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

end LaterDeepFiveToSix68

#print axioms lowerRowZeroPolynomial68_fiveToSix_forces_firstSecondaryZero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_topClassification68

end Max11DegreeRoutes
