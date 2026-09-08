import Grok68VanishingAOrder4CompanionSplitPart13Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 14 of 26, so that no single
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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth_reduction68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    Fce.coeff 0 * ((2 : k) * A.coeff p * A.coeff (p - 4) +
      (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
      A.coeff (p - 2) ^ 2) = 0 := by
  let p := 2 * N
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  change Fce.coeff 0 * ((2 : k) * A.coeff p * A.coeff (p - 4) +
    (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) + A.coeff (p - 2) ^ 2) = 0
  have hcomp := fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hrem :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_fourth_cancel68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hload :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_source68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only
    [FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionFourthScalar68]
    at hcomp
  dsimp only at hrem hload
  have hmain : (9 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) *
      ((p - 2 : ℕ) : k) ^ 2 * ((p - 1 : ℕ) : k) * Fce.coeff 0 *
      ((2 : k) * A.coeff p * A.coeff (p - 4) +
        (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
        A.coeff (p - 2) ^ 2) = 0 := by
    dsimp only [p, Fce, L0, W0, L2, W2]
    linear_combination hcomp - hrem - hload
  have hp4 : 4 < p := by
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
    dsimp only [p]; omega
  have hpm4 : ((p - 4 : ℕ) : k) ≠ 0 := by exact_mod_cast (show p - 4 ≠ 0 by omega)
  have hpm3 : ((p - 3 : ℕ) : k) ≠ 0 := by exact_mod_cast (show p - 3 ≠ 0 by omega)
  have hpm2 : ((p - 2 : ℕ) : k) ≠ 0 := by exact_mod_cast (show p - 2 ≠ 0 by omega)
  have hpm1 : ((p - 1 : ℕ) : k) ≠ 0 := by exact_mod_cast (show p - 1 ≠ 0 by omega)
  have hfac : (9 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) *
      ((p - 2 : ℕ) : k) ^ 2 * ((p - 1 : ℕ) : k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpm4) hpm3)
      (pow_ne_zero 2 hpm2)) hpm1
  have hmul : ((9 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) *
      ((p - 2 : ℕ) : k) ^ 2 * ((p - 1 : ℕ) : k)) *
      (Fce.coeff 0 * ((2 : k) * A.coeff p * A.coeff (p - 4) +
        (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
        A.coeff (p - 2) ^ 2)) = 0 := by
    linear_combination hmain
  exact (mul_eq_zero.mp hmul).resolve_left hfac


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
