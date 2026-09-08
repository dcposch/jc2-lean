import Grok68VanishingAOrder4CompanionSplitPart22Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 23 of 26, so that no single
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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c).natDegree ≤ Cc - 5 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let R := C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c
  change R.natDegree ≤ Cc - 5
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have h4 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hBc
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
  rcases hpacket with ⟨hN, hgt, hle, hA, hBdeg, hcdeg, hd0, he0, hatop,
    hcusp, had⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hBdeg
  have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hcdeg
  have hND : N + D = Cc := by dsimp only [D, Cc]; omega
  have hleR : R.natDegree ≤ Cc := by
    dsimp only [R]; compute_degree; omega
  have hcoeff4 : R.coeff (Cc - 4) = 0 := by
    dsimp only [R]
    by_cases hD4 : 4 ≤ D
    · have hidx : Cc - 4 = N + (D - 4) := by omega
      have hL : (C (c.coeff Cc) * X ^ N * B).coeff (Cc - 4) =
          c.coeff Cc * B.coeff (D - 4) := by
        rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
      simp only [D] at h4 hD4 ⊢
      simp only [coeff_sub, hL, coeff_C_mul, hD4, ite_true] at h4 ⊢
      linear_combination h4
    · have hlt : Cc - 4 < N := by dsimp only [Cc]; omega
      have hL : (C (c.coeff Cc) * X ^ N * B).coeff (Cc - 4) = 0 :=
        fiveToSix_qZero_coeff_X_pow_mul_of_lt68 (c.coeff Cc) B hlt
      simp only [D] at h4 hD4 ⊢
      simp only [coeff_sub, hL, coeff_C_mul, hD4, ite_false, zero_sub] at h4 ⊢
      linear_combination h4
  have h5 : 5 ≤ Cc := by dsimp only [Cc]; omega
  have hprev : R.natDegree ≤ Cc - 4 := hBc
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  by_cases hgt : Cc - 4 < n
  · exact coeff_eq_zero_of_natDegree_lt (hprev.trans_lt hgt)
  · have : n = Cc - 4 := by omega
    simpa [this] using hcoeff4


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
