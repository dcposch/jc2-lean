import Grok68VanishingAOrder4CompanionSplitPart24Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 25 of 26, so that no single
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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_order4_companion68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAOrder4CompanionResidual68
      gamma epsilon A B c d e N S := by
  refine ⟨fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_charged_integral68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq, ?_, ?_, ?_, ?_, ?_⟩
  · exact (fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree_four68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        hterminal hs hq).2.2.2.2
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth_reduction68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_companion_split68
#print axioms fiveToSix_qZero_vanishingA_Bc_jet_four_algebra68
#print axioms fiveToSix_qZero_vanishingA_ed_jet_four_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet_four68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_order4_companion68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
