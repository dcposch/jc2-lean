import Grok68VanishingAOrder4CompanionSplitPart20Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 21 of 26, so that no single
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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    B.coeff D * e.coeff (E - 4) + c.coeff Cc * d.coeff (V - 4) = 0 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  change B.coeff D * e.coeff (E - 4) + c.coeff Cc * d.coeff (V - 4) = 0
  have hBc4 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hEd :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hBc4 hBc hEd
  rcases hBc with ⟨h1, h2, h3⟩
  rcases hEd with ⟨hE1, hE2, hE3⟩
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
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hb0 : B.coeff D ≠ 0 := by simpa [D, hGS] using hBtop
  have hI40 :=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).1
  have hI44 := fiveToSix_zetaFirst_B3_equality_support_qZero_I4_fourth68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI44' :
      (if 4 ≤ D then B.coeff (D - 4) else 0) * e.coeff E +
        B.coeff (D - 3) * e.coeff (E - 1) + B.coeff (D - 2) * e.coeff (E - 2) +
        B.coeff (D - 1) * e.coeff (E - 3) + B.coeff D * e.coeff (E - 4) +
        c.coeff (Cc - 4) * d.coeff V + c.coeff (Cc - 3) * d.coeff (V - 1) +
        c.coeff (Cc - 2) * d.coeff (V - 2) + c.coeff (Cc - 1) * d.coeff (V - 3) +
        c.coeff Cc * d.coeff (V - 4) = 0 := by
    simpa [D, Cc, V, E, ite_mul, zero_mul] using hI44
  exact fiveToSix_qZero_vanishingA_ed_jet_four_algebra68
    (B.coeff D) (c.coeff Cc)
    (B.coeff (D - 1)) (c.coeff (Cc - 1))
    (B.coeff (D - 2)) (c.coeff (Cc - 2))
    (B.coeff (D - 3)) (c.coeff (Cc - 3))
    (if 4 ≤ D then B.coeff (D - 4) else 0) (c.coeff (Cc - 4))
    (e.coeff E) (e.coeff (E - 1)) (e.coeff (E - 2)) (e.coeff (E - 3))
    (e.coeff (E - 4))
    (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
    (d.coeff (V - 4))
    hb0 hI40 hI44' h1 h2 h3 hBc4 hE1 hE2 hE3


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
