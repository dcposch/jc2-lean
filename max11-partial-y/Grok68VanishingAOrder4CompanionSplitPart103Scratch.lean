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
/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 16 of 26, so that no single
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

theorem fiveToSix_qZero_vanishingA_Bc_weighted_algebra68
    (a b c bk ck : k) (hb : b ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hk : c * bk - b * ck = 0) :
    a * b * bk + (3 : k) * c * ck = 0 := by
  have hmul : b * (a * b * bk + (3 : k) * c * ck) = 0 := by
    linear_combination bk * hcusp - (3 : k) * c * hk
  exact (mul_eq_zero.mp hmul).resolve_left hb


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 17 of 26, so that no single
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

theorem fiveToSix_qZero_vanishingA_Bc_jet_four_algebra68
    (a b c b1 c1 b2 c2 b3 c3 b4 c4 : k)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hD1 : (2 : k) * a * b * b1 + (6 : k) * c * c1 = 0)
    (hD4 : a * ((2 : k) * b * b4 + (2 : k) * b1 * b3 + b2 ^ 2) +
      (6 : k) * (c * c4 + c1 * c3) + (3 : k) * c2 ^ 2 = 0)
    (h1 : c * b1 - b * c1 = 0)
    (h2 : c * b2 - b * c2 = 0)
    (h3 : c * b3 - b * c3 = 0) :
    c * b4 - b * c4 = 0 := by
  have hD1half : a * b * b1 + (3 : k) * c * c1 = 0 := by
    linear_combination (1 / 2 : k) * hD1
  have hsq2 : a * b2 ^ 2 + (3 : k) * c2 ^ 2 = 0 :=
    fiveToSix_qZero_vanishingA_Bc_sq_algebra68 a b c b2 c2 hb
      (fiveToSix_qZero_vanishingA_Bc_weighted_algebra68 a b c b2 c2 hb
        hcusp h2) h2
  have hcross13 : a * b1 * b3 + (3 : k) * c1 * c3 = 0 :=
    fiveToSix_qZero_vanishingA_Bc_cross_algebra68 a b c b1 c1 b3 c3 hb
      hD1half h3
  have hmul : (2 : k) * a * b * (c * b4 - b * c4) = 0 := by
    linear_combination c * hD4 - (2 : k) * c4 * hcusp -
      (2 : k) * c * hcross13 - c * hsq2
  have h2 : (2 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hmul).resolve_left
    (mul_ne_zero (mul_ne_zero h2 ha) hb)


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 18 of 26, so that no single
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

theorem fiveToSix_qZero_vanishingA_ed_jet_four_algebra68
    (b c b1 c1 b2 c2 b3 c3 b4 c4 e0 e1 e2 e3 e4 d0 d1 d2 d3 d4 : k)
    (hb : b ≠ 0)
    (hI40 : b * e0 + c * d0 = 0)
    (hI44 : b4 * e0 + b3 * e1 + b2 * e2 + b1 * e3 + b * e4 +
      c4 * d0 + c3 * d1 + c2 * d2 + c1 * d3 + c * d4 = 0)
    (h1 : c * b1 - b * c1 = 0)
    (h2 : c * b2 - b * c2 = 0)
    (h3 : c * b3 - b * c3 = 0)
    (h4 : c * b4 - b * c4 = 0)
    (hE1 : b * e1 + c * d1 = 0)
    (hE2 : b * e2 + c * d2 = 0)
    (hE3 : b * e3 + c * d3 = 0) :
    b * e4 + c * d4 = 0 := by
  have hcross31 : b3 * e1 + c3 * d1 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68 b c b3 c3 e1 d1 hb hE1 h3
  have hcross22 : b2 * e2 + c2 * d2 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68 b c b2 c2 e2 d2 hb hE2 h2
  have hcross13 : b1 * e3 + c1 * d3 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68 b c b1 c1 e3 d3 hb hE3 h1
  have hmul : b * (b * e4 + c * d4) = 0 := by
    linear_combination b * hI44 - b4 * hI40 + d0 * h4 -
      b * hcross31 - b * hcross22 - b * hcross13
  exact (mul_eq_zero.mp hmul).resolve_left hb


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 19 of 26, so that no single
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

theorem fiveToSix_qZero_coeff_X_pow_mul_of_lt68
    (r : k) (p : k[X]) {n i : ℕ} (h : i < n) :
    (C r * X ^ n * p).coeff i = 0 := by
  have hXp : (X ^ n * p).coeff i = 0 := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [coeff_X_pow]
    split_ifs with heq
    · have : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      omega
    · rw [zero_mul]
  simp only [mul_assoc, coeff_C_mul, hXp, mul_zero]


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
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
/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 22 of 26, so that no single
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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    A.natDegree = p ∧ A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧
      A.coeff (p - 3) = 0 ∧ A.coeff (p - 4) = 0 := by
  let p := 2 * N
  have hA :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hsplit :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_companion_split68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hFne := fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hterminal hs hq
  dsimp only at hA hsplit
  rcases hsplit with hf | hA4
  · exact (hFne hf).elim
  · exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, hA4.2.2.2⟩


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
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
/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 25 of 26, so that no single
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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_order4_companion68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAOrder4CompanionResidual68
      gamma epsilon A B c d e N S := by
  refine ⟨fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_charged_integral68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq, ?_, ?_, ?_, ?_, ?_⟩
  · exact (fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree_four68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        hterminal hs hq).2.2.2.2
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth_reduction68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_companion_split68
#print axioms fiveToSix_qZero_vanishingA_Bc_jet_four_algebra68
#print axioms fiveToSix_qZero_vanishingA_ed_jet_four_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet_four68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_order4_companion68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
