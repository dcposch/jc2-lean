import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderThirdPart03Scratch

/-! # Literal remainder transport for the third companion on `q=0`

The third source coefficient has exactly three exceptional arithmetic charts.
Their remainder contributions cancel against the two previously extracted
row-two jets; from `N ≥ 28` all four remainders vanish separately.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderThird68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_third_transport68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_clean_third_split68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_third_cancel68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderThird68

end Max11DegreeRoutes
