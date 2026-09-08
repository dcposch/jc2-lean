import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderNextPart03Scratch

/-! # The second companion's literal remainders on `q=0`

At the next source coefficients, the clean remainders have two exceptional
charts, `(N,S)=(7,9)` and `(14,18)`.  Their contributions cancel in the
second companion; from `N ≥ 21` they vanish separately.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_next_transport68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_clean_next_split68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_next_cancel68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderNext68

end Max11DegreeRoutes
