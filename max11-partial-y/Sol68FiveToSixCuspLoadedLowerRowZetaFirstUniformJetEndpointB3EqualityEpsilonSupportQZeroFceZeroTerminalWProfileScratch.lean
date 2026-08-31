import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalHDescentScratch

/-! # Exact profile of the second terminal quotient invariant -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalWProfile68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The discriminant normal form forces `W=4A+3v²` down from its naive
degree `2N` to exact degree `2N-S`, with a division-free leading relation. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_W_profile68
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
    let V := 5 * N - 3 * S
    let R := 2 * N - S
    let Cg := (2 : k) • c + C (3 * gamma)
    ∃ v W : k[X],
      Cg = B * v ∧ v.natDegree = N ∧
      W = (4 : k) • A + (3 : k) • v ^ 2 ∧
      W.natDegree = R ∧
      B.coeff D * W.coeff R = (12 : k) * d.coeff V := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let R := 2 * N - S
  let L := 3 * D + Cc - V
  let Cg := (2 : k) • c + C (3 * gamma)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  change ∃ v W : k[X], Cg = B * v ∧ v.natDegree = N ∧
    W = (4 : k) • A + (3 : k) • v ^ 2 ∧ W.natDegree = R ∧
    B.coeff D * W.coeff R = (12 : k) * d.coeff V
  obtain ⟨v, hv, hvdeg0, he, hHnorm, hDnorm⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_quotient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  let W := (4 : k) • A + (3 : k) • v ^ 2
  change (4 : k) • Delta = (4 : k) • (A * B ^ 2) +
    (3 : k) • (B * v - C (3 * gamma)) ^ 2 at hDnorm
  have hBW : B ^ 2 * W = (4 : k) • Delta +
      (18 * gamma : k) • (B * v) - C (27 * gamma ^ 2) := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    have hD' := congrArg (algebraMap k[X] (RatFunc k)) hDnorm
    dsimp only [W] at hD' ⊢
    simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, RatFunc.algebraMap_C] at hD' ⊢
    simp only [map_div₀, map_ofNat, map_one] at hD' ⊢
    ring_nf at hD' ⊢
    linear_combination (-1 : RatFunc k) * hD'
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
    ⟨hGS, hGamma, hsource⟩
  have hp := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, hedeg, hpacket, hrest⟩
  rcases hpacket with
    ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hvdeg : v.natDegree = N := by
    rw [hvdeg0]
    omega
  have hvne : v ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hvdeg
    omega
  have hB' : B.natDegree ≤ D := by dsimp only [D]; omega
  have hbidx : D = 3 * N - G := by dsimp only [D]; omega
  have hbcoeff : B.coeff D ≠ 0 := by rw [hbidx]; exact hBtop
  have hBdeg : B.natDegree = D :=
    natDegree_eq_of_le_of_coeff_ne_zero hB' hbcoeff
  have hBne : B ≠ 0 := by
    intro hz
    apply hbcoeff
    rw [hz, coeff_zero]
  have hDeltaTop :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_Delta_top68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  change Delta.coeff L = (3 : k) * B.coeff D * d.coeff V ∧
    Delta.natDegree = L at hDeltaTop
  have h4DeltaDeg : ((4 : k) • Delta).natDegree = L := by
    rw [natDegree_smul Delta (by norm_num : (4 : k) ≠ 0), hDeltaTop.2]
  let Low := (18 * gamma : k) • (B * v) - C (27 * gamma ^ 2)
  have hLowlt : Low.natDegree < L := by
    dsimp only [Low, D, Cc, V, L] at *
    compute_degree
    omega
  have hLowlt4 : Low.natDegree < ((4 : k) • Delta).natDegree := by
    rw [h4DeltaDeg]
    exact hLowlt
  let P := (4 : k) • Delta + Low
  have hPdeg : P.natDegree = L := by
    dsimp only [P]
    rw [natDegree_add_eq_left_of_natDegree_lt hLowlt4, h4DeltaDeg]
  have hBWP : B ^ 2 * W = P := by
    dsimp only [P, Low]
    simpa only [sub_eq_add_neg, add_assoc] using hBW
  have hPne : P ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hPdeg
    dsimp only [D, Cc, V, L] at hPdeg
    omega
  have hWne : W ≠ 0 := by
    intro hz
    apply hPne
    rw [← hBWP, hz, mul_zero]
  have hmuldeg := natDegree_mul (pow_ne_zero 2 hBne) hWne
  have hWdeg : W.natDegree = R := by
    rw [hBWP, hPdeg, natDegree_pow, hBdeg] at hmuldeg
    dsimp only [D, Cc, V, R, L] at *
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by
    compute_degree
    omega
  have hB2coeff : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
    have h := coeff_pow_at_bound68 B D 2 hB'
    simpa only [Nat.mul_comm] using h
  have hprodcoeff : (B ^ 2 * W).coeff L =
      B.coeff D ^ 2 * W.coeff R := by
    have h := coeff_mul_at_bounds68 (B ^ 2) W (2 * D) R
      hB2deg hWdeg.le
    rw [show 2 * D + R = L by dsimp only [D, Cc, V, R, L]; omega,
      hB2coeff] at h
    exact h
  have hLowcoeff : Low.coeff L = 0 :=
    coeff_eq_zero_of_natDegree_lt hLowlt
  have hPcoeff : P.coeff L = (4 : k) * Delta.coeff L := by
    dsimp only [P]
    simp only [coeff_add, coeff_smul, smul_eq_mul, hLowcoeff, add_zero]
  have hcoeff := congrArg (fun Q : k[X] => Q.coeff L) hBWP
  rw [hprodcoeff, hPcoeff, hDeltaTop.1] at hcoeff
  have hfac : B.coeff D *
      (B.coeff D * W.coeff R - (12 : k) * d.coeff V) = 0 := by
    linear_combination hcoeff
  have htop := (mul_eq_zero.mp hfac).resolve_left hbcoeff
  refine ⟨v, W, hv, hvdeg, rfl, hWdeg, ?_⟩
  linear_combination htop

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_W_profile68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalWProfile68

end Max11DegreeRoutes
