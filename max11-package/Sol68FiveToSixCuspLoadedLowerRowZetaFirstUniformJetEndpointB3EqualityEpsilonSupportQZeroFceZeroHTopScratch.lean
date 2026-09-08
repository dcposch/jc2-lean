import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroRowTwoIntegralScratch

/-! # Exact leading coefficient of `H` on the zero-`Fce` branch -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroHTop68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Eliminating `J` between the bounded-Jacobian identity and the constant
row-two integral gives a direct relation among `Delta` and `H`. -/
theorem fiveToSix_qZero_Fce_zero_rowTwo_Delta_H_algebra68
    (gamma epsilon kappa : k) (A B c d e : k[X])
    (hF : ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
        (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B = 0)
    (hP : FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e =
      C kappa) :
    let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
    let H := FiveToSixQZeroFceZeroH68 B c d
    (2 : k) • (B ^ 2 * Delta) - (12 : k) • (B ^ 3 * d) +
        (9 * gamma : k) • (B ^ 2 * c) + (3 * kappa : k) • B -
      (6 : k) • (c * H) - (9 * gamma : k) • H = 0 := by
  dsimp only [FiveToSixQZeroFceZeroRowTwoIntegral68,
    fiveToSixCuspDiscriminantPolynomial68, FiveToSixQZeroFceZeroH68] at hP ⊢
  have hF' := congrArg (algebraMap k[X] (RatFunc k)) hF
  have hP' := congrArg (algebraMap k[X] (RatFunc k)) hP
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C] at hF' hP' ⊢
  simp only [map_div₀, map_ofNat, map_one] at hF' hP' ⊢
  ring_nf at hF' hP' ⊢
  linear_combination (-54 : RatFunc k) * hF' * algebraMap k[X] (RatFunc k) d +
    (-3 : RatFunc k) * algebraMap k[X] (RatFunc k) B * hP'

/-- The degree-`N` bound for `H` is sharp.  Its leading coefficient is
fixed division-free by the leading coefficients of `B`, `c`, and `d`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_H_top68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let Q := D + 2 * N - Cc
    let H := FiveToSixQZeroFceZeroH68 B c d
    c.coeff Cc * H.coeff Q = -(B.coeff D ^ 3 * d.coeff V) ∧
      H.natDegree = Q := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let p := 2 * N
  let Q := D + p - Cc
  let L := 3 * D + Cc - V
  let M := Cc + Q
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let H := FiveToSixQZeroFceZeroH68 B c d
  change c.coeff Cc * H.coeff Q = -(B.coeff D ^ 3 * d.coeff V) ∧
    H.natDegree = Q
  have hglobal :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_global68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  rcases hglobal with ⟨i3, hFzero, hRce, hK⟩
  obtain ⟨kappa, hP⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_rowTwo_integral68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  have halg := fiveToSix_qZero_Fce_zero_rowTwo_Delta_H_algebra68
    gamma epsilon kappa A B c d e hFzero hP
  change (2 : k) • (B ^ 2 * Delta) - (12 : k) • (B ^ 3 * d) +
      (9 * gamma : k) • (B ^ 2 * c) + (3 * kappa : k) • B -
    (6 : k) • (c * H) - (9 * gamma : k) • H = 0 at halg
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
  have hd' : d.natDegree ≤ V := by dsimp only [V]; omega
  have hbidx : D = 3 * N - G := by dsimp only [D]; omega
  have hcidx : Cc = 4 * N - G := by dsimp only [Cc]; omega
  have hdidx : V = 5 * N - G - S := by dsimp only [V]; omega
  have hbcoeff : B.coeff D ≠ 0 := by rw [hbidx]; exact hBtop
  have hccoeff : c.coeff Cc ≠ 0 := by rw [hcidx]; exact hctop
  have hdcoeff : d.coeff V ≠ 0 := by rw [hdidx]; exact hdtop
  have hH : H.natDegree ≤ Q := by
    exact fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_H_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  have hDeltaTop :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_Delta_top68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  change Delta.coeff L = (3 : k) * B.coeff D * d.coeff V ∧
    Delta.natDegree = L at hDeltaTop
  have hDelta : Delta.natDegree ≤ L := hDeltaTop.2.le
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by compute_degree; omega
  have hB2 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
    have h := coeff_pow_at_bound68 B D 2 hB'
    simpa only [Nat.mul_comm] using h
  have hB2Delta : (B ^ 2 * Delta).coeff M =
      B.coeff D ^ 2 * Delta.coeff L := by
    have h := coeff_mul_at_bounds68 (B ^ 2) Delta (2 * D) L
      hB2deg hDelta
    rw [show 2 * D + L = M by dsimp only [D, Cc, V, p, Q, L, M]; omega,
      hB2] at h
    exact h
  have hB3deg : (B ^ 3).natDegree ≤ 3 * D := by compute_degree; omega
  have hB3 : (B ^ 3).coeff (3 * D) = B.coeff D ^ 3 := by
    have h := coeff_pow_at_bound68 B D 3 hB'
    simpa only [Nat.mul_comm] using h
  have hB3d : (B ^ 3 * d).coeff M = B.coeff D ^ 3 * d.coeff V := by
    have h := coeff_mul_at_bounds68 (B ^ 3) d (3 * D) V hB3deg hd'
    rw [show 3 * D + V = M by dsimp only [D, Cc, V, p, Q, M]; omega,
      hB3] at h
    exact h
  have hcH : (c * H).coeff M = c.coeff Cc * H.coeff Q := by
    have h := coeff_mul_at_bounds68 c H Cc Q hc' hH
    simpa only [M] using h
  have hB2clow : (B ^ 2 * c).natDegree < M := by
    dsimp only [D, Cc, V, p, Q, M] at *
    compute_degree
    omega
  have hBlow : B.natDegree < M := by
    dsimp only [D, Cc, V, p, Q, M] at *
    omega
  have hHlow : H.natDegree < M := by
    dsimp only [D, Cc, V, p, Q, M] at *
    omega
  have hcoeff := congrArg (fun R : k[X] => R.coeff M) halg
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hB2Delta,
    hB3d, hcH, hDeltaTop.1,
    coeff_eq_zero_of_natDegree_lt hB2clow,
    coeff_eq_zero_of_natDegree_lt hBlow,
    coeff_eq_zero_of_natDegree_lt hHlow,
    mul_zero, add_zero, sub_zero, coeff_zero] at hcoeff
  have htop : c.coeff Cc * H.coeff Q =
      -(B.coeff D ^ 3 * d.coeff V) := by
    linear_combination (-1 / 6 : k) * hcoeff
  refine ⟨htop, ?_⟩
  apply natDegree_eq_of_le_of_coeff_ne_zero hH
  intro hz
  rw [hz, mul_zero] at htop
  have hrhs : B.coeff D ^ 3 * d.coeff V ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hbcoeff) hdcoeff
  exact hrhs (neg_eq_zero.mp htop.symm)

#print axioms fiveToSix_qZero_Fce_zero_rowTwo_Delta_H_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_H_top68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroHTop68

end Max11DegreeRoutes
