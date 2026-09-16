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
/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 11 of 26, so that no single
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

/-- Exact polynomial certificate for the fourth load. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_algebra68
    (P a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
      d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 : k)
    (hb0 : b0 ≠ 0)
    (hD0 : a0 * b0 ^ 2 + 3 * c0 ^ 2 = 0)
    (hD1 : a1 * b0 ^ 2 + 2 * a0 * b0 * b1 + 6 * c0 * c1 = 0)
    (hD2 : a2 * b0 ^ 2 + 2 * a1 * b0 * b1 + a0 * (2 * b0 * b2 + b1 ^ 2) +
      3 * (2 * c0 * c2 + c1 ^ 2) = 0)
    (hD3 : a3 * b0 ^ 2 + 2 * a2 * b0 * b1 + a1 * (2 * b0 * b2 + b1 ^ 2) +
      a0 * (2 * b0 * b3 + 2 * b1 * b2) + 6 * (c0 * c3 + c1 * c2) = 0)
    (hD4 : a4 * b0 ^ 2 + 2 * a3 * b0 * b1 + a2 * (2 * b0 * b2 + b1 ^ 2) +
      a1 * (2 * b0 * b3 + 2 * b1 * b2) +
      a0 * (2 * b0 * b4 + 2 * b1 * b3 + b2 ^ 2) +
      6 * (c0 * c4 + c1 * c3) + 3 * c2 ^ 2 = 0)
    (hI40 : b0 * e0 + c0 * d0 = 0)
    (hI41 : b1 * e0 + b0 * e1 + c1 * d0 + c0 * d1 = 0)
    (hI42 : b2 * e0 + b1 * e1 + b0 * e2 + c2 * d0 + c1 * d1 + c0 * d2 = 0)
    (hI43 : b3 * e0 + b2 * e1 + b1 * e2 + b0 * e3 +
      c3 * d0 + c2 * d1 + c1 * d2 + c0 * d3 = 0)
    (hI44 : b4 * e0 + b3 * e1 + b2 * e2 + b1 * e3 + b0 * e4 +
      c4 * d0 + c3 * d1 + c2 * d2 + c1 * d3 + c0 * d4 = 0) :
    6 * (P - 4) ^ 2 * (P - 3) * (P - 2) * (P - 1) * a4 * b0 ^ 2 * d0 +
      6 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        FiveToSixQZeroRowZeroLoadJetFour68 P
          a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
          d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 +
      P * (P - 3) * (P - 2) * (P - 1) * a0 * (6 * (P - 4) *
        FiveToSixQZeroBBDJetFour68 b0 b1 b2 b3 b4 d0 d1 d2 d3 d4) +
      (P - 4) * (P - 2) * (P - 1) ^ 2 * a1 * (6 * (P - 3) *
        FiveToSixQZeroBBDJetThree68 b0 b1 b2 b3 d0 d1 d2 d3) +
      (P - 4) * (P - 3) * (P - 2) * (P - 1) * a2 * (6 * (P - 2) *
        FiveToSixQZeroBBDJetTwo68 b0 b1 b2 d0 d1 d2) +
      (P - 4) * (P - 3) ^ 2 * (P - 2) * a3 * (6 * (P - 1) *
        FiveToSixQZeroBBDJetOne68 b0 b1 d0 d1) = 0 := by
  have hmul : b0 ^ 4 * (
      6 * (P - 4) ^ 2 * (P - 3) * (P - 2) * (P - 1) * a4 * b0 ^ 2 * d0 +
        6 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
          FiveToSixQZeroRowZeroLoadJetFour68 P
            a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
            d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 +
        P * (P - 3) * (P - 2) * (P - 1) * a0 * (6 * (P - 4) *
          FiveToSixQZeroBBDJetFour68 b0 b1 b2 b3 b4 d0 d1 d2 d3 d4) +
        (P - 4) * (P - 2) * (P - 1) ^ 2 * a1 * (6 * (P - 3) *
          FiveToSixQZeroBBDJetThree68 b0 b1 b2 b3 d0 d1 d2 d3) +
        (P - 4) * (P - 3) * (P - 2) * (P - 1) * a2 * (6 * (P - 2) *
          FiveToSixQZeroBBDJetTwo68 b0 b1 b2 d0 d1 d2) +
        (P - 4) * (P - 3) ^ 2 * (P - 2) * a3 * (6 * (P - 1) *
          FiveToSixQZeroBBDJetOne68 b0 b1 d0 d1)) = 0 := by
    dsimp only [FiveToSixQZeroRowZeroLoadJetFour68,
      FiveToSixQZeroBBDJetZero68, FiveToSixQZeroBBDJetOne68,
      FiveToSixQZeroBBDJetTwo68, FiveToSixQZeroBBDJetThree68,
      FiveToSixQZeroBBDJetFour68,
      FiveToSixQZeroBBDerivativeJetZero68,
      FiveToSixQZeroBBDerivativeJetOne68,
      FiveToSixQZeroBBDerivativeJetTwo68,
      FiveToSixQZeroBBDerivativeJetThree68,
      FiveToSixQZeroBBDerivativeJetFour68,
      FiveToSixQZeroBCEDerivativeJetFour68,
      FiveToSixQZeroCCDerivativeDJetFour68]
    linear_combination
      (3 / 7 : k) * b0 ^ 4 * d0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        (25 * P - 56) * hD4 +
      (3 / 7 : k) * b0 ^ 3 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 * d1 + 14 * b1 * d0) * hD3 +
      (3 / 7 : k) * b0 ^ 2 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 ^ 2 * d2 + 14 * b0 * b1 * d1 +
          28 * b0 * b2 * d0 - 14 * b1 ^ 2 * d0) * hD2 +
      (3 / 7 : k) * b0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 ^ 3 * d3 + 14 * b0 ^ 2 * b1 * d2 +
          28 * b0 ^ 2 * b2 * d1 + 42 * b0 ^ 2 * b3 * d0 -
          14 * b0 * b1 ^ 2 * d1 - 42 * b0 * b1 * b2 * d0 +
          14 * b1 ^ 3 * d0) * hD1 +
      (3 / 7 : k) * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 ^ 4 * d4 + 14 * b0 ^ 3 * b1 * d3 +
          28 * b0 ^ 3 * b2 * d2 + 42 * b0 ^ 3 * b3 * d1 +
          56 * b0 ^ 3 * b4 * d0 - 14 * b0 ^ 2 * b1 ^ 2 * d2 -
          42 * b0 ^ 2 * b1 * b2 * d1 - 56 * b0 ^ 2 * b1 * b3 * d0 -
          28 * b0 ^ 2 * b2 ^ 2 * d0 + 14 * b0 * b1 ^ 3 * d1 +
          56 * b0 * b1 ^ 2 * b2 * d0 - 14 * b1 ^ 4 * d0) * hD0 -
      (9 / 7 : k) * b0 ^ 4 * c0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        (15 * P - 56) * hI44 -
      (9 / 7 : k) * b0 ^ 3 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((15 * P - 42) * b0 * c1 + 14 * b1 * c0) * hI43 -
      (9 / 7 : k) * b0 ^ 2 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((15 * P - 28) * b0 ^ 2 * c2 + 14 * b0 * b1 * c1 +
          28 * b0 * b2 * c0 - 14 * b1 ^ 2 * c0) * hI42 -
      (9 / 7 : k) * b0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((15 * P - 14) * b0 ^ 3 * c3 + 14 * b0 ^ 2 * b1 * c2 +
          28 * b0 ^ 2 * b2 * c1 + 42 * b0 ^ 2 * b3 * c0 -
          14 * b0 * b1 ^ 2 * c1 - 42 * b0 * b1 * b2 * c0 +
          14 * b1 ^ 3 * c0) * hI41 -
      (9 / 7 : k) * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        (15 * P * b0 ^ 4 * c4 + 14 * b0 ^ 3 * b1 * c3 +
          28 * b0 ^ 3 * b2 * c2 + 42 * b0 ^ 3 * b3 * c1 +
          56 * b0 ^ 3 * b4 * c0 - 14 * b0 ^ 2 * b1 ^ 2 * c2 -
          42 * b0 ^ 2 * b1 * b2 * c1 - 56 * b0 ^ 2 * b1 * b3 * c0 -
          28 * b0 ^ 2 * b2 ^ 2 * c0 + 14 * b0 * b1 ^ 3 * c1 +
          56 * b0 * b1 ^ 2 * b2 * c0 - 14 * b1 ^ 4 * c0) * hI40
  have hb04 : b0 ^ 4 ≠ 0 := pow_ne_zero 4 hb0
  exact (mul_eq_zero.mp hmul).resolve_left hb04


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 12 of 26, so that no single
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

/-- Exact fourth-jet expansion of the row-two load. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_fourth68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    L2.coeff (p - 5) = (6 : k) * ((p - 4 : ℕ) : k) *
      FiveToSixQZeroBBDJetFour68
        (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
        (if 4 ≤ D then B.coeff (D - 4) else 0)
        (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
        (d.coeff (V - 4)) := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  change L2.coeff (p - 5) = _
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrest⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
  have hd' : d.natDegree ≤ V := by dsimp only [V]; rw [hGS] at hd; omega
  have hD3 : 3 ≤ D := by dsimp only [D]; omega
  have hV4 : 4 ≤ V := by dsimp only [V]; omega
  have h2D4 : 4 ≤ 2 * D := by omega
  have hpEq : p = 2 * D + V := by dsimp only [p, D, V]; omega
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by compute_degree; omega
  have hprod0 := coeff_mul_four_below_bounds68 (B ^ 2) d (2 * D) V
    h2D4 hV4 hB2deg hd'
  have hB20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
    have h := coeff_mul_at_bounds68 B B D D hB' hB'
    rw [← two_mul] at h
    simpa [pow_two] using h
  have hB21 : (B ^ 2).coeff (2 * D - 1) =
      (2 : k) * B.coeff D * B.coeff (D - 1) := by
    have h := coeff_mul_one_below_bounds68 B B D D (by omega) (by omega) hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢; linear_combination h
  have hB22 : (B ^ 2).coeff (2 * D - 2) =
      (2 : k) * B.coeff D * B.coeff (D - 2) + B.coeff (D - 1) ^ 2 := by
    have h := coeff_mul_two_below_bounds68 B B D D (by omega) (by omega) hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢; linear_combination h
  have hB23 : (B ^ 2).coeff (2 * D - 3) =
      (2 : k) * B.coeff D * B.coeff (D - 3) +
        (2 : k) * B.coeff (D - 1) * B.coeff (D - 2) := by
    have h := coeff_mul_three_below_bounds68 B B D D hD3 hD3 hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢; linear_combination h
  have hB24 := coeff_sq_sub_four68 B D hD3 hB'
  have hprod : (B ^ 2 * d).coeff (p - 4) =
      FiveToSixQZeroBBDJetFour68
        (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
        (if 4 ≤ D then B.coeff (D - 4) else 0)
        (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
        (d.coeff (V - 4)) := by
    rw [hpEq, show 2 * D + V - 4 = 2 * D + V - 4 by rfl, hprod0,
      hB20, hB21, hB22, hB23, hB24]
    dsimp only [FiveToSixQZeroBBDJetFour68]
    ring
  have hsq : derivative (B ^ 2) = (2 : k) • (B * derivative B) := by
    rw [show B ^ 2 = B * B by ring, derivative_mul]
    simp only [two_smul]; ring
  have hder : derivative (B ^ 2 * d) =
      (2 : k) • (B * derivative B * d) + B ^ 2 * derivative d := by
    rw [derivative_mul, hsq]; simp only [two_smul]; ring
  have hL2poly : L2 = (6 : k) • derivative (B ^ 2 * d) := by
    dsimp only [L2, FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68]
    rw [hder]; module
  have hidx : p - 5 + 1 = p - 4 := by dsimp only [p]; omega
  have hcast : (((p - 5 : ℕ) : k) + 1) = ((p - 4 : ℕ) : k) := by
    exact_mod_cast hidx
  rw [hL2poly, coeff_smul, coeff_derivative, hidx, hcast, hprod]
  ring

#print axioms coeff_mul_four_below_bounds68
#print axioms coeff_sq_sub_four68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_fourth68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_I4_fourth68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_fourth_cancel68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_fourth68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
