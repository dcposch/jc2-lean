import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalDivisorScratch

/-! # Quotient normal form after the nonzero terminal divisor -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalQuotient68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The divisor `B ∣ 2c+3γ` has an exact-degree quotient.  Substitution
puts `e`, `H`, and `Delta` in a source-honest quotient normal form. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_quotient68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let Cg := (2 : k) • c + C (3 * gamma)
    let H := FiveToSixQZeroFceZeroH68 B c d
    let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
    ∃ v : k[X],
      Cg = B * v ∧ v.natDegree = Cc - D ∧
      e = (1 / 9 : k) • B ^ 2 - (1 / 2 : k) • (v * d) -
        C (3 / 4 * epsilon) ∧
      H = (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
        (9 : k) • d ^ 2 ∧
      (4 : k) • Delta = (4 : k) • (A * B ^ 2) +
        (3 : k) • (B * v - C (3 * gamma)) ^ 2 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let Cg := (2 : k) • c + C (3 * gamma)
  let H := FiveToSixQZeroFceZeroH68 B c d
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  change ∃ v : k[X], Cg = B * v ∧ v.natDegree = Cc - D ∧
    e = (1 / 9 : k) • B ^ 2 - (1 / 2 : k) • (v * d) -
      C (3 / 4 * epsilon) ∧
    H = (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
      (9 : k) • d ^ 2 ∧
    (4 : k) • Delta = (4 : k) • (A * B ^ 2) +
      (3 : k) • (B * v - C (3 * gamma)) ^ 2
  have hdiv :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_divisor68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hterminal hs hq hf
  change B ∣ Cg at hdiv
  obtain ⟨v, hv⟩ := hdiv
  have hglobal :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_global68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  rcases hglobal with ⟨i3, hFzero, hRce, hK⟩
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
  rcases hpacket with
    ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hB' : B.natDegree ≤ D := by dsimp only [D]; omega
  have hc' : c.natDegree ≤ Cc := by dsimp only [Cc]; omega
  have hbidx : D = 3 * N - G := by dsimp only [D]; omega
  have hcidx : Cc = 4 * N - G := by dsimp only [Cc]; omega
  have hbcoeff : B.coeff D ≠ 0 := by rw [hbidx]; exact hBtop
  have hccoeff : c.coeff Cc ≠ 0 := by rw [hcidx]; exact hctop
  have hBdeg : B.natDegree = D :=
    natDegree_eq_of_le_of_coeff_ne_zero hB' hbcoeff
  have hCcpos : 0 < Cc := by dsimp only [Cc]; omega
  have hCg' : Cg.natDegree ≤ Cc := by
    dsimp only [Cg]
    compute_degree
    omega
  have hCgcoeff : Cg.coeff Cc = (2 : k) * c.coeff Cc := by
    dsimp only [Cg]
    simp only [coeff_add, coeff_smul, smul_eq_mul, coeff_C,
      if_neg (Nat.ne_of_gt hCcpos)]
    ring
  have hCgcoeffne : Cg.coeff Cc ≠ 0 := by
    rw [hCgcoeff]
    exact mul_ne_zero (by norm_num) hccoeff
  have hCgdeg : Cg.natDegree = Cc :=
    natDegree_eq_of_le_of_coeff_ne_zero hCg' hCgcoeffne
  have hBne : B ≠ 0 := by
    intro hz
    apply hbcoeff
    rw [hz, coeff_zero]
  have hCgne : Cg ≠ 0 := by
    intro hz
    apply hCgcoeffne
    rw [hz, coeff_zero]
  have hvne : v ≠ 0 := by
    intro hz
    apply hCgne
    rw [hv, hz, mul_zero]
  have hvdeg : v.natDegree = Cc - D := by
    have hdeg := natDegree_mul hBne hvne
    rw [← hv, hCgdeg, hBdeg] at hdeg
    omega
  let Ered := e - (1 / 9 : k) • B ^ 2 + (1 / 2 : k) • (v * d) +
    C (3 / 4 * epsilon)
  have hEfac : B * Ered = 0 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    have hF' := congrArg (algebraMap k[X] (RatFunc k)) hFzero
    have hv' := congrArg (algebraMap k[X] (RatFunc k)) hv
    dsimp only [Ered, Cg] at hv' ⊢
    simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, RatFunc.algebraMap_C] at hF' hv' ⊢
    simp only [map_div₀, map_ofNat, map_one] at hF' hv' ⊢
    ring_nf at hF' hv' ⊢
    linear_combination hF' - (1 / 2 : RatFunc k) * hv' *
      algebraMap k[X] (RatFunc k) d
  have hEzero : Ered = 0 :=
    (mul_eq_zero.mp hEfac).resolve_left hBne
  have heq : e = (1 / 9 : k) • B ^ 2 - (1 / 2 : k) • (v * d) -
      C (3 / 4 * epsilon) := by
    dsimp only [Ered] at hEzero
    simp only [Polynomial.smul_eq_C_mul] at hEzero ⊢
    linear_combination hEzero
  have hHnorm : H = (2 : k) • (B ^ 3 * v) -
      (6 * gamma : k) • B ^ 2 + (9 : k) • d ^ 2 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    have hv' := congrArg (algebraMap k[X] (RatFunc k)) hv
    dsimp only [H, FiveToSixQZeroFceZeroH68, Cg] at hv' ⊢
    simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, RatFunc.algebraMap_C] at hv' ⊢
    simp only [map_div₀, map_ofNat, map_one] at hv' ⊢
    ring_nf at hv' ⊢
    linear_combination (2 : RatFunc k) *
      (algebraMap k[X] (RatFunc k) B) ^ 2 * hv'
  have hDnorm : (4 : k) • Delta = (4 : k) • (A * B ^ 2) +
      (3 : k) • (B * v - C (3 * gamma)) ^ 2 := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    have hv' := congrArg (algebraMap k[X] (RatFunc k)) hv
    dsimp only [Delta, fiveToSixCuspDiscriminantPolynomial68, Cg] at hv' ⊢
    simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, RatFunc.algebraMap_C] at hv' ⊢
    simp only [map_div₀, map_ofNat, map_one] at hv' ⊢
    ring_nf at hv' ⊢
    linear_combination (3 : RatFunc k) * hv' *
      (algebraMap k[X] (RatFunc k) B * algebraMap k[X] (RatFunc k) v -
        3 * RatFunc.C gamma + 2 * algebraMap k[X] (RatFunc k) c)
  exact ⟨v, hv, hvdeg, heq, hHnorm, hDnorm⟩

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_quotient68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalQuotient68

end Max11DegreeRoutes
