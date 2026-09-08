import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderPart06Scratch

/-! # Expanded one-lower remainders on the `q=0` support wall

Both named remainders are normalized back to the literal source rows and
expanded before applying degree bounds.  The equation `9*N=7*S` leaves
exactly the minimal chart `(N,S)=(7,9)` or `14≤N`.  Only in the latter are
the remaining `B*c'`, `c*B'`, and `B*A'*c` terms deleted by degree.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainder68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

#print axioms fiveToSix_zetaFirst_B3_equality_support_clean_rowZero_expansion68
#print axioms fiveToSix_zetaFirst_B3_equality_support_clean_rowTwo_expansion68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_transport68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_clean_split68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_clean_packet68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_source_split68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_source_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainder68

end Max11DegreeRoutes
