import Grok68VanishingAOrder4CompanionSplitPart14Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 15 of 26, so that no single
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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_companion_split68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    Fce.coeff 0 = 0 ∨
      (A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧ A.coeff (p - 3) = 0 ∧
        A.coeff (p - 4) = 0) := by
  let p := 2 * N
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  change Fce.coeff 0 = 0 ∨
    (A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧ A.coeff (p - 3) = 0 ∧
      A.coeff (p - 4) = 0)
  by_cases hf : Fce.coeff 0 = 0
  · exact Or.inl hf
  · right
    have hprev :=
      fiveToSix_zetaFirst_B3_equality_support_qZero_third_companion_split68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
    have hfourth :=
      fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth_reduction68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
    dsimp only at hprev hfourth
    rcases hprev with hf0 | ⟨ha1, ha2, ha3⟩
    · exact (hf hf0).elim
    have hjet : (2 : k) * A.coeff p * A.coeff (p - 4) +
        (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
        A.coeff (p - 2) ^ 2 = 0 :=
      (mul_eq_zero.mp (by simpa only [p, Fce] using hfourth)).resolve_left hf
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
    have ha0 : A.coeff p ≠ 0 := by simpa [p] using hatop
    have htwoa0 : (2 : k) * A.coeff p ≠ 0 := mul_ne_zero (by norm_num) ha0
    have ha4 : A.coeff (p - 4) = 0 := by
      apply (mul_left_cancel₀ htwoa0)
      rw [ha1, ha2, ha3] at hjet
      linear_combination hjet
    exact ⟨ha1, ha2, ha3, ha4⟩


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
