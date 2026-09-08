import Grok68VanishingAOrder4CompanionSplitPart9Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 10 of 26, so that no single
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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_fourth_cancel68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
      alpha gamma epsilon zeta eta A B c d e
    let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
      alpha gamma epsilon zeta eta A B c d e
    (6 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * W0.coeff (2 * p - 5) +
      ((p : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * A.coeff p * W2.coeff (p - 5) +
      ((p - 4 : ℕ) : k) * ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) ^ 2 *
        A.coeff (p - 1) * W2.coeff (p - 4) +
      ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * A.coeff (p - 2) * W2.coeff (p - 3) +
      ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) ^ 2 * ((p - 2 : ℕ) : k) *
        A.coeff (p - 3) * W2.coeff (p - 2) = 0 := by
  let p := 2 * N
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hold := fiveToSix_zetaFirst_B3_equality_support_qZero_source_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hnext := fiveToSix_zetaFirst_B3_equality_support_qZero_clean_next_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hthird := fiveToSix_zetaFirst_B3_equality_support_qZero_clean_third_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hfourth :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_clean_fourth_split68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have htr4 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_fourth_transport68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have htr3 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_third_transport68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have htr2 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_next_transport68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hold hnext hthird hfourth htr4 htr3 htr2 ⊢
  rcases hfourth with h7 | h14 | h21 | h28 | hlarge
  · rcases h7 with ⟨hN, hS, hW0, hW24⟩
    rcases hthird with ht7 | ht14 | ht21 | htlarge
    · rcases ht7 with ⟨_, _, _, hW23⟩
      rcases hnext with hn7 | hn14 | hnlarge
      · rcases hn7 with ⟨_, _, _, hW22⟩
        rcases hold with ho7 | holarge
        · rcases ho7 with ⟨_, _, _, hW21⟩
          subst N; subst S
          norm_num at hW0 hW24 hW23 hW22 hW21 htr4 htr3 htr2 ⊢
          rw [htr4.1, hW0, htr4.2, hW24, htr3.2, hW23, htr2.2, hW22, hW21]
          ring
        · omega
      · omega
      · omega
    · omega
    · omega
    · omega
  · rcases h14 with ⟨hN, hS, hW0, hW24⟩
    rcases hthird with ht7 | ht14 | ht21 | htlarge
    · omega
    · rcases ht14 with ⟨_, _, _, hW23⟩
      rcases hnext with hn7 | hn14 | hnlarge
      · omega
      · rcases hn14 with ⟨_, _, _, hW22⟩
        rcases hold with ho7 | holarge
        · omega
        · rcases holarge with ⟨_, hW01, hW21⟩
          subst N; subst S
          norm_num at hW0 hW24 hW23 hW22 hW21 htr4 htr3 htr2 ⊢
          rw [htr4.1, hW0, htr4.2, hW24, htr3.2, hW23, htr2.2, hW22, hW21]
          ring
      · omega
    · omega
    · omega
  · rcases h21 with ⟨hN, hS, hW0, hW24⟩
    rcases hthird with ht7 | ht14 | ht21 | htlarge
    · omega
    · omega
    · rcases ht21 with ⟨_, _, _, hW23⟩
      rcases hnext with hn7 | hn14 | hnlarge
      · omega
      · omega
      · rcases hnlarge with ⟨_, _, hW22⟩
        rcases hold with ho7 | holarge
        · omega
        · rcases holarge with ⟨_, _, hW21⟩
          subst N; subst S
          norm_num at hW0 hW24 hW23 hW22 hW21 htr4 htr3 htr2 ⊢
          rw [htr4.1, hW0, htr4.2, hW24, htr3.2, hW23, htr2.2, hW22, hW21]
          ring
    · omega
  · rcases h28 with ⟨hN, hS, hW0, hW24⟩
    rcases hthird with ht7 | ht14 | ht21 | htlarge
    · omega
    · omega
    · omega
    · rcases htlarge with ⟨_, _, hW23⟩
      rcases hnext with hn7 | hn14 | hnlarge
      · omega
      · omega
      · rcases hnlarge with ⟨_, _, hW22⟩
        rcases hold with ho7 | holarge
        · omega
        · rcases holarge with ⟨_, _, hW21⟩
          subst N; subst S
          norm_num at hW0 hW24 hW23 hW22 hW21 htr4 htr3 htr2 ⊢
          rw [htr4.1, hW0, htr4.2, hW24, htr3.2, hW23, htr2.2, hW22, hW21]
          ring
  · rcases hlarge with ⟨hNl, hW0, hW24⟩
    rcases hthird with ht7 | ht14 | ht21 | htlarge
    · omega
    · omega
    · omega
    · rcases htlarge with ⟨_, hW03, hW23⟩
      rcases hnext with hn7 | hn14 | hnlarge
      · omega
      · omega
      · rcases hnlarge with ⟨_, hW02, hW22⟩
        rcases hold with ho7 | holarge
        · omega
        · rcases holarge with ⟨_, hW01, hW21⟩
          rw [show 2 * (2 * N) - 5 = 4 * N - 5 by omega]
          rw [htr4.1, hW0, htr4.2, hW24, htr3.2, hW23, htr2.2, hW22, hW21]
          ring


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
