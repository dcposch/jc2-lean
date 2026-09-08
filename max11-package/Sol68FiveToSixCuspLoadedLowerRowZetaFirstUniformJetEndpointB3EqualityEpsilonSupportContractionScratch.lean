import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportContractionPart03Scratch

/-! # Exact contraction of the post-epsilon support wall

This contracts only the six literal top-support products retained by the
support-wall module.  The sole algebraic reduction used on those products is
the cusp relation `A_top * B_top^2 + 3*c_top^2 = 0`.  In particular the
coincident wall `D=T` (where the compensated `Fce` edge is constant) is kept.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportContraction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

#print axioms fiveToSix_zetaFirst_B3_equality_support_contracted_scalar68
#print axioms fiveToSix_zetaFirst_B3_equality_supportLoaded_contracted68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportContraction68

end Max11DegreeRoutes
