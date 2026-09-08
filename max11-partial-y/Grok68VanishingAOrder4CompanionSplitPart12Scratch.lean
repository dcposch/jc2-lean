import Grok68VanishingAOrder4CompanionSplitPart11Scratch

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
