import Grok68VanishingAOrder4CompanionSplitPart16Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 17 of 26, so that no single
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

theorem fiveToSix_qZero_vanishingA_Bc_jet_four_algebra68
    (a b c b1 c1 b2 c2 b3 c3 b4 c4 : k)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hD1 : (2 : k) * a * b * b1 + (6 : k) * c * c1 = 0)
    (hD4 : a * ((2 : k) * b * b4 + (2 : k) * b1 * b3 + b2 ^ 2) +
      (6 : k) * (c * c4 + c1 * c3) + (3 : k) * c2 ^ 2 = 0)
    (h1 : c * b1 - b * c1 = 0)
    (h2 : c * b2 - b * c2 = 0)
    (h3 : c * b3 - b * c3 = 0) :
    c * b4 - b * c4 = 0 := by
  have hD1half : a * b * b1 + (3 : k) * c * c1 = 0 := by
    linear_combination (1 / 2 : k) * hD1
  have hsq2 : a * b2 ^ 2 + (3 : k) * c2 ^ 2 = 0 :=
    fiveToSix_qZero_vanishingA_Bc_sq_algebra68 a b c b2 c2 hb
      (fiveToSix_qZero_vanishingA_Bc_weighted_algebra68 a b c b2 c2 hb
        hcusp h2) h2
  have hcross13 : a * b1 * b3 + (3 : k) * c1 * c3 = 0 :=
    fiveToSix_qZero_vanishingA_Bc_cross_algebra68 a b c b1 c1 b3 c3 hb
      hD1half h3
  have hmul : (2 : k) * a * b * (c * b4 - b * c4) = 0 := by
    linear_combination c * hD4 - (2 : k) * c4 * hcusp -
      (2 : k) * c * hcross13 - c * hsq2
  have h2 : (2 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hmul).resolve_left
    (mul_ne_zero (mul_ne_zero h2 ha) hb)


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
