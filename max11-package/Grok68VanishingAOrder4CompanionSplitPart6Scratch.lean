import Grok68VanishingAOrder4CompanionSplitPart5Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 6 of 26, so that no single
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

/-- The exact fourth coefficient of the compensated `I4` product. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_I4_fourth68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    (if 4 ≤ D then B.coeff (D - 4) * e.coeff E else 0) +
      B.coeff (D - 3) * e.coeff (E - 1) + B.coeff (D - 2) * e.coeff (E - 2) +
      B.coeff (D - 1) * e.coeff (E - 3) + B.coeff D * e.coeff (E - 4) +
      c.coeff (Cc - 4) * d.coeff V + c.coeff (Cc - 3) * d.coeff (V - 1) +
      c.coeff (Cc - 2) * d.coeff (V - 2) + c.coeff (Cc - 1) * d.coeff (V - 3) +
      c.coeff Cc * d.coeff (V - 4) = 0 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let K := D + E
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d +
    (3 / 4 * epsilon : k) • B
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  rcases hnxt.2.1 with ⟨i4, i3, hFce, hRce, hRceDeg⟩
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, he, hpacket, hrest⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
  have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hc
  have hd' : d.natDegree ≤ V := by dsimp only [V]; rw [hGS] at hd; omega
  have he' : e.natDegree ≤ E := by dsimp only [E]; rw [hGS] at he; omega
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hD3 : 3 ≤ D := by dsimp only [D]; omega
  have hC4 : 4 ≤ Cc := by dsimp only [Cc]; omega
  have hV4 : 4 ≤ V := by dsimp only [V]; omega
  have hE4 : 4 ≤ E := by dsimp only [E]; omega
  have hB3low : (B ^ 3).natDegree < K - 4 := by
    have : (B ^ 3).natDegree ≤ 3 * D := by compute_degree; omega
    dsimp only [D, E, K] at *; omega
  have hdLow : d.natDegree < K - 4 := by dsimp only [D, E, K, V] at *; omega
  have hBLow : B.natDegree < K - 4 := by dsimp only [D, E, K] at *; omega
  have hBe := coeff_mul_sub_four_left_ge_three68 B e D E hD3 hE4 hB' he'
  have hcd0 := coeff_mul_four_below_bounds68 c d Cc V hC4 hV4 hc' hd'
  have hcd : (c * d).coeff (K - 4) =
      c.coeff (Cc - 4) * d.coeff V + c.coeff (Cc - 3) * d.coeff (V - 1) +
        c.coeff (Cc - 2) * d.coeff (V - 2) + c.coeff (Cc - 1) * d.coeff (V - 3) +
        c.coeff Cc * d.coeff (V - 4) := by
    rw [show Cc + V = K by dsimp only [D, Cc, V, E, K]; omega] at hcd0
    exact hcd0
  have hFK : Fce.coeff (K - 4) = 0 := by
    dsimp only [Fce]
    rw [hFce, coeff_smul, coeff_C]
    split_ifs with h
    · omega
    · simp only [smul_zero]
  dsimp only [Fce] at hFK
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hcd,
    coeff_eq_zero_of_natDegree_lt hB3low,
    coeff_eq_zero_of_natDegree_lt hdLow,
    coeff_eq_zero_of_natDegree_lt hBLow, mul_zero, sub_zero, add_zero] at hFK
  have hBe' : (B * e).coeff (K - 4) =
      (if 4 ≤ D then B.coeff (D - 4) * e.coeff E else 0) +
        B.coeff (D - 3) * e.coeff (E - 1) + B.coeff (D - 2) * e.coeff (E - 2) +
        B.coeff (D - 1) * e.coeff (E - 3) + B.coeff D * e.coeff (E - 4) := by
    simpa [K] using hBe
  rw [hBe'] at hFK
  convert hFK using 1
  ring


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
