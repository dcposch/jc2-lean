import Grok68VanishingAOrder4CompanionSplitPart21Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 22 of 26, so that no single
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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    A.natDegree = p ∧ A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧
      A.coeff (p - 3) = 0 ∧ A.coeff (p - 4) = 0 := by
  let p := 2 * N
  have hA :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hsplit :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_companion_split68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hFne := fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hterminal hs hq
  dsimp only at hA hsplit
  rcases hsplit with hf | hA4
  · exact (hFne hf).elim
  · exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, hA4.2.2.2⟩


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
