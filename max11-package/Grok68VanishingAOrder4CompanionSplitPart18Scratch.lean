import Grok68VanishingAOrder4CompanionSplitPart17Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 18 of 26, so that no single
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

theorem fiveToSix_qZero_vanishingA_ed_jet_four_algebra68
    (b c b1 c1 b2 c2 b3 c3 b4 c4 e0 e1 e2 e3 e4 d0 d1 d2 d3 d4 : k)
    (hb : b ≠ 0)
    (hI40 : b * e0 + c * d0 = 0)
    (hI44 : b4 * e0 + b3 * e1 + b2 * e2 + b1 * e3 + b * e4 +
      c4 * d0 + c3 * d1 + c2 * d2 + c1 * d3 + c * d4 = 0)
    (h1 : c * b1 - b * c1 = 0)
    (h2 : c * b2 - b * c2 = 0)
    (h3 : c * b3 - b * c3 = 0)
    (h4 : c * b4 - b * c4 = 0)
    (hE1 : b * e1 + c * d1 = 0)
    (hE2 : b * e2 + c * d2 = 0)
    (hE3 : b * e3 + c * d3 = 0) :
    b * e4 + c * d4 = 0 := by
  have hcross31 : b3 * e1 + c3 * d1 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68 b c b3 c3 e1 d1 hb hE1 h3
  have hcross22 : b2 * e2 + c2 * d2 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68 b c b2 c2 e2 d2 hb hE2 h2
  have hcross13 : b1 * e3 + c1 * d3 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68 b c b1 c1 e3 d3 hb hE3 h1
  have hmul : b * (b * e4 + c * d4) = 0 := by
    linear_combination b * hI44 - b4 * hI40 + d0 * h4 -
      b * hcross31 - b * hcross22 - b * hcross13
  exact (mul_eq_zero.mp hmul).resolve_left hb


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
