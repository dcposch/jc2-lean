import Grok68VanishingAOrder4CompanionSplitPart19Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 20 of 26, so that no single
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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    c.coeff Cc * (if 4 ≤ D then B.coeff (D - 4) else 0) -
      B.coeff D * c.coeff (Cc - 4) = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  change c.coeff Cc * (if 4 ≤ D then B.coeff (D - 4) else 0) -
    B.coeff D * c.coeff (Cc - 4) = 0
  have hsplit :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_companion_split68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hFne := fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hterminal hs hq
  dsimp only at hsplit
  have hAvan : A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧
      A.coeff (p - 3) = 0 ∧ A.coeff (p - 4) = 0 := by
    rcases hsplit with hf | hA
    · exact (hFne hf).elim
    · exact hA
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hBc
  rcases hBc with ⟨h1, h2, h3⟩
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
  rcases hpacket with ⟨hN, hgt, hle, hAdeg, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have ha0 : A.coeff p ≠ 0 := by simpa [p] using hatop
  have hb0 : B.coeff D ≠ 0 := by simpa [D, hGS] using hBtop
  have hD0 : A.coeff p * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 := by
    simpa [p, D, Cc, hGS] using hcuspEq
  have hD1raw :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD4raw :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_fourth68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hD1raw hD4raw
  have hD1 : (2 : k) * A.coeff p * B.coeff D * B.coeff (D - 1) +
      (6 : k) * c.coeff Cc * c.coeff (Cc - 1) = 0 := by
    rw [hAvan.1] at hD1raw
    linear_combination hD1raw
  have hD4 : A.coeff p *
        ((2 : k) * B.coeff D * (if 4 ≤ D then B.coeff (D - 4) else 0) +
          (2 : k) * B.coeff (D - 1) * B.coeff (D - 3) +
          B.coeff (D - 2) ^ 2) +
      (6 : k) * (c.coeff Cc * c.coeff (Cc - 4) +
        c.coeff (Cc - 1) * c.coeff (Cc - 3)) +
      (3 : k) * c.coeff (Cc - 2) ^ 2 = 0 := by
    rw [hAvan.1, hAvan.2.1, hAvan.2.2.1, hAvan.2.2.2] at hD4raw
    linear_combination hD4raw
  exact fiveToSix_qZero_vanishingA_Bc_jet_four_algebra68
    (A.coeff p) (B.coeff D) (c.coeff Cc)
    (B.coeff (D - 1)) (c.coeff (Cc - 1))
    (B.coeff (D - 2)) (c.coeff (Cc - 2))
    (B.coeff (D - 3)) (c.coeff (Cc - 3))
    (if 4 ≤ D then B.coeff (D - 4) else 0) (c.coeff (Cc - 4))
    ha0 hb0 hD0 hD1 hD4 h1 h2 h3


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
