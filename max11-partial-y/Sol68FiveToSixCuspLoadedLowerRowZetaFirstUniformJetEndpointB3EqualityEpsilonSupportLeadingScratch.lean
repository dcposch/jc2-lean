import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeadingPart03Scratch

/-! # The same-witness leading edge scalar after the support row

The retained `J` degree drop kills its actual top coefficient.  Together
with the cusp equation this is exactly `4*A_top*B_top^3+27*d_top*e_top=0`.
On the positive compensated-I4 branch, the row-one packet then gives the
additional division-free scalar `4*B_top^2*c_top+9*d_top^2=0`.  The
coefficient-zero coincidence `q=0` is kept verbatim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeading68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

#print axioms fiveToSix_zetaFirst_B3_equality_support_leading_scalar68
#print axioms fiveToSix_zetaFirst_B3_equality_support_leading_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_leading_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeading68

end Max11DegreeRoutes
