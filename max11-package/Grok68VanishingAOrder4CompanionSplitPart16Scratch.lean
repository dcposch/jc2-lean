import Grok68VanishingAOrder4CompanionSplitPart15Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 16 of 26, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem fiveToSix_qZero_vanishingA_Bc_weighted_algebra68
    (a b c bk ck : k) (hb : b ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hk : c * bk - b * ck = 0) :
    a * b * bk + (3 : k) * c * ck = 0 := by
  have hmul : b * (a * b * bk + (3 : k) * c * ck) = 0 := by
    linear_combination bk * hcusp - (3 : k) * c * hk
  exact (mul_eq_zero.mp hmul).resolve_left hb


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
