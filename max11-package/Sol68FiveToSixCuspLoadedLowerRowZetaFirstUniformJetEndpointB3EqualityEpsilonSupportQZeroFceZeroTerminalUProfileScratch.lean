import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalWProfileScratch

/-! # The forced high-degree cancellation in the terminal quotient -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalUProfile68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Although both summands of `U=3Wd+8B²v` have degree `7N-4S`, the
terminal `H` quotient forces their sum to have exact degree `N-D`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_U_profile68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    let R := 2 * N - S
    let K := R + V
    let Cg := (2 : k) • c + C (3 * gamma)
    ∃ v W U : k[X],
      Cg = B * v ∧ v.natDegree = N ∧
      W = (4 : k) • A + (3 : k) • v ^ 2 ∧ W.natDegree = R ∧
      U = (3 : k) • (W * d) + (8 : k) • (B ^ 2 * v) ∧
      U.natDegree = N - D ∧
      (W * d).natDegree = K ∧ (B ^ 2 * v).natDegree = K ∧
      (3 : k) * W.coeff R * d.coeff V +
        (8 : k) * B.coeff D ^ 2 * v.coeff N = 0 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let R := 2 * N - S
  let K := R + V
  let Cg := (2 : k) • c + C (3 * gamma)
  change ∃ v W U : k[X], Cg = B * v ∧ v.natDegree = N ∧
    W = (4 : k) • A + (3 : k) • v ^ 2 ∧ W.natDegree = R ∧
    U = (3 : k) • (W * d) + (8 : k) • (B ^ 2 * v) ∧
    U.natDegree = N - D ∧ (W * d).natDegree = K ∧
    (B ^ 2 * v).natDegree = K ∧
    (3 : k) * W.coeff R * d.coeff V +
      (8 : k) * B.coeff D ^ 2 * v.coeff N = 0
  obtain ⟨vw, W, hvw, hvwdeg, hWdef, hWdeg, hWtop⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_W_profile68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  obtain ⟨i3, v, T, hv, hvdeg0, hTdef, hBT, hTdeg⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_H_quotient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
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
  have hB' : B.natDegree ≤ D := by dsimp only [D]; omega
  have hbidx : D = 3 * N - G := by dsimp only [D]; omega
  have hbcoeff : B.coeff D ≠ 0 := by rw [hbidx]; exact hBtop
  have hBdeg : B.natDegree = D :=
    natDegree_eq_of_le_of_coeff_ne_zero hB' hbcoeff
  have hBne : B ≠ 0 := by
    intro hz
    apply hbcoeff
    rw [hz, coeff_zero]
  have hvuniq : v = vw := by
    apply mul_left_cancel₀ hBne
    rw [← hv, ← hvw]
  subst vw
  have hvdeg : v.natDegree = N := hvwdeg
  have hvne : v ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hvdeg
    omega
  have hd' : d.natDegree ≤ V := by dsimp only [V]; omega
  have hdidx : V = 5 * N - G - S := by dsimp only [V]; omega
  have hdcoeff : d.coeff V ≠ 0 := by rw [hdidx]; exact hdtop
  have hddeg : d.natDegree = V :=
    natDegree_eq_of_le_of_coeff_ne_zero hd' hdcoeff
  have hdne : d ≠ 0 := by
    intro hz
    apply hdcoeff
    rw [hz, coeff_zero]
  have hWne : W ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hWdeg
    omega
  let U := (3 : k) • (W * d) + (8 : k) • (B ^ 2 * v)
  have hTform : T = (2 : k) • (U - (21 * gamma : k) • B) := by
    dsimp only [U]
    rw [hTdef, hWdef]
  have hZdeg : (U - (21 * gamma : k) • B).natDegree = N - D := by
    have h := congrArg natDegree hTform
    rw [natDegree_smul _ (by norm_num : (2 : k) ≠ 0), hTdeg] at h
    exact h.symm
  have hBlow : ((21 * gamma : k) • B).natDegree < N - D := by
    compute_degree
    rw [hBdeg]
    dsimp only [D]
    omega
  have hBlowZ : ((21 * gamma : k) • B).natDegree <
      (U - (21 * gamma : k) • B).natDegree := by
    rw [hZdeg]
    exact hBlow
  have hUdecomp : U = (U - (21 * gamma : k) • B) +
      (21 * gamma : k) • B := by
    module
  have hUdeg : U.natDegree = N - D := by
    rw [hUdecomp, natDegree_add_eq_left_of_natDegree_lt hBlowZ, hZdeg]
  have hWddeg : (W * d).natDegree = K := by
    rw [natDegree_mul hWne hdne, hWdeg, hddeg]
  have hB2vdeg : (B ^ 2 * v).natDegree = K := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hvne, natDegree_pow,
      hBdeg, hvdeg]
    dsimp only [D, R, V, K]
    omega
  have hUlow : U.natDegree < K := by
    rw [hUdeg]
    dsimp only [D, R, V, K]
    omega
  have hWdcoeff : (W * d).coeff K = W.coeff R * d.coeff V := by
    have h := coeff_mul_at_bounds68 W d R V hWdeg.le hddeg.le
    simpa only [K] using h
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by
    compute_degree
    omega
  have hB2coeff : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
    have h := coeff_pow_at_bound68 B D 2 hB'
    simpa only [Nat.mul_comm] using h
  have hB2vcoeff : (B ^ 2 * v).coeff K =
      B.coeff D ^ 2 * v.coeff N := by
    have h := coeff_mul_at_bounds68 (B ^ 2) v (2 * D) N
      hB2deg hvdeg.le
    rw [show 2 * D + N = K by dsimp only [D, R, V, K]; omega,
      hB2coeff] at h
    exact h
  have hUcoeff : U.coeff K = 0 := coeff_eq_zero_of_natDegree_lt hUlow
  have hcancel : (3 : k) * W.coeff R * d.coeff V +
      (8 : k) * B.coeff D ^ 2 * v.coeff N = 0 := by
    dsimp only [U] at hUcoeff
    simp only [coeff_add, coeff_smul, smul_eq_mul, hWdcoeff, hB2vcoeff]
      at hUcoeff
    simpa only [mul_assoc] using hUcoeff
  exact ⟨v, W, U, hv, hvdeg, hWdef, hWdeg, rfl, hUdeg,
    hWddeg, hB2vdeg, hcancel⟩

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_U_profile68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalUProfile68

end Max11DegreeRoutes
