import Grok68VanishingAOrder4CompanionSplitPart4Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 5 of 26, so that no single
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

/-- The exact fourth reflected-discriminant jet.  The `B` index `D-4` is
replaced by zero on the chart `D=3`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_fourth68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    A.coeff (p - 4) * B.coeff D ^ 2 +
      (2 : k) * A.coeff (p - 3) * B.coeff D * B.coeff (D - 1) +
      A.coeff (p - 2) * ((2 : k) * B.coeff D * B.coeff (D - 2) +
        B.coeff (D - 1) ^ 2) +
      A.coeff (p - 1) * ((2 : k) * B.coeff D * B.coeff (D - 3) +
        (2 : k) * B.coeff (D - 1) * B.coeff (D - 2)) +
      A.coeff p * ((2 : k) * B.coeff D *
          (if 4 ≤ D then B.coeff (D - 4) else 0) +
        (2 : k) * B.coeff (D - 1) * B.coeff (D - 3) + B.coeff (D - 2) ^ 2) +
      (6 : k) * (c.coeff Cc * c.coeff (Cc - 4) +
        c.coeff (Cc - 1) * c.coeff (Cc - 3)) +
      (3 : k) * c.coeff (Cc - 2) ^ 2 = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let U := 8 * N - 2 * G
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  change _ = 0
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
  rcases hrest with ⟨hless, hmu, hzeta, hzero, hDeltaDeg⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hA' : A.natDegree ≤ p := by simpa [p] using hA
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
  have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hc
  have hp4 : 4 ≤ p := by dsimp only [p]; omega
  have hD3 : 3 ≤ D := by dsimp only [D]; omega
  have hC4 : 4 ≤ Cc := by dsimp only [Cc]; omega
  have h2D4 : 4 ≤ 2 * D := by omega
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by compute_degree; omega
  have hFour : 4 ≤ min S (7 * N - 2 * G - S) := by omega
  have href : (Delta.reflect U).coeff 4 = 0 := by
    dsimp only [Delta, U]
    exact hzero 4 hFour
  have hDelta : Delta.coeff (U - 4) = 0 := by
    rw [coeff_reflect, revAt_le (by dsimp only [U]; omega)] at href
    exact href
  have hABB0 := coeff_mul_four_below_bounds68 A (B ^ 2) p (2 * D)
    hp4 h2D4 hA' hB2deg
  have hB20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
    have h := coeff_mul_at_bounds68 B B D D hB' hB'
    rw [← two_mul] at h
    simpa [pow_two] using h
  have hB21 : (B ^ 2).coeff (2 * D - 1) =
      (2 : k) * B.coeff D * B.coeff (D - 1) := by
    have h := coeff_mul_one_below_bounds68 B B D D (by omega) (by omega) hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢
    linear_combination h
  have hB22 : (B ^ 2).coeff (2 * D - 2) =
      (2 : k) * B.coeff D * B.coeff (D - 2) + B.coeff (D - 1) ^ 2 := by
    have h := coeff_mul_two_below_bounds68 B B D D (by omega) (by omega) hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢
    linear_combination h
  have hB23 : (B ^ 2).coeff (2 * D - 3) =
      (2 : k) * B.coeff D * B.coeff (D - 3) +
        (2 : k) * B.coeff (D - 1) * B.coeff (D - 2) := by
    have h := coeff_mul_three_below_bounds68 B B D D hD3 hD3 hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢
    linear_combination h
  have hB24 : (B ^ 2).coeff (2 * D - 4) =
      (2 : k) * B.coeff D * (if 4 ≤ D then B.coeff (D - 4) else 0) +
        (2 : k) * B.coeff (D - 1) * B.coeff (D - 3) + B.coeff (D - 2) ^ 2 :=
    coeff_sq_sub_four68 B D hD3 hB'
  have hABB : (A * B ^ 2).coeff (U - 4) =
      A.coeff (p - 4) * B.coeff D ^ 2 +
        (2 : k) * A.coeff (p - 3) * B.coeff D * B.coeff (D - 1) +
        A.coeff (p - 2) * ((2 : k) * B.coeff D * B.coeff (D - 2) +
          B.coeff (D - 1) ^ 2) +
        A.coeff (p - 1) * ((2 : k) * B.coeff D * B.coeff (D - 3) +
          (2 : k) * B.coeff (D - 1) * B.coeff (D - 2)) +
        A.coeff p * ((2 : k) * B.coeff D *
            (if 4 ≤ D then B.coeff (D - 4) else 0) +
          (2 : k) * B.coeff (D - 1) * B.coeff (D - 3) +
          B.coeff (D - 2) ^ 2) := by
    have hU : p + 2 * D = U := by dsimp only [p, D, U]; rw [hGS]; omega
    have hidx : p + 2 * D - 4 = U - 4 := by omega
    rw [← hidx, hABB0, show 2 * D - 1 = 2 * D - 1 by rfl,
      show p - 1 = p - 1 by rfl]
    rw [show p - 4 = p - 4 by rfl, hB20,
      show 2 * D - 1 = 2 * D - 1 by rfl, hB21, hB22, hB23, hB24]
    ring
  have hcc0 := coeff_mul_four_below_bounds68 c c Cc Cc hC4 hC4 hc' hc'
  have hcc : (c ^ 2).coeff (U - 4) =
      (2 : k) * (c.coeff Cc * c.coeff (Cc - 4) +
        c.coeff (Cc - 1) * c.coeff (Cc - 3)) + c.coeff (Cc - 2) ^ 2 := by
    have hU : Cc + Cc = U := by dsimp only [Cc, U]; rw [hGS]; omega
    rw [show Cc + Cc - 4 = U - 4 by omega] at hcc0
    simp only [pow_two] at hcc0 ⊢
    linear_combination hcc0
  dsimp only [Delta, fiveToSixCuspDiscriminantPolynomial68] at hDelta
  simp only [coeff_add, coeff_smul, smul_eq_mul, hABB, hcc] at hDelta
  linear_combination hDelta


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
