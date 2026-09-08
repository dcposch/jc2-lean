import Grok68VanishingAOrder4CompanionSplitPart23Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 24 of 26, so that no single
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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree_four68
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
    (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d).natDegree ≤ E - 5 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let R := C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d
  change R.natDegree ≤ E - 5
  have hEd :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hE4 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hEd hE4
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, hedeg, hpacket, hrest⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hNV : N + V = E := by dsimp only [V, E]; omega
  have hprev : R.natDegree ≤ E - 4 := hEd
  have hcoeff4 : R.coeff (E - 4) = 0 := by
    dsimp only [R]
    have hidx : E - 4 = N + (V - 4) := by omega
    have hR : (C (c.coeff Cc) * X ^ N * d).coeff (E - 4) =
        c.coeff Cc * d.coeff (V - 4) := by
      rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
    simp only [coeff_add, coeff_C_mul, hR]
    linear_combination hE4
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  by_cases hgt : E - 4 < n
  · exact coeff_eq_zero_of_natDegree_lt (hprev.trans_lt hgt)
  · have : n = E - 4 := by omega
    simpa [this] using hcoeff4


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
