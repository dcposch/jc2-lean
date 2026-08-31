import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalSquarefreeScratch

/-! # The terminal square fiber -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalSquareFiber68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The compensated `H` fiber is an exact square congruence modulo `B`.
Its quotient has the degree of the dominant `B²v` term. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_square_fiber68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    let D := 3 * N - 2 * S
    ∃ i3 kappa : k, ∃ v W T q s : k[X],
      81 * epsilon * gamma + 27 * i3 ≠ 0 ∧
      v.natDegree = N ∧
      FiveToSixQZeroFceZeroH68 B c d =
        (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
          (9 : k) • d ^ 2 ∧
      (4 : k) • FiveToSixQZeroFceZeroH68 B c d -
        C (81 * epsilon * gamma + 27 * i3) = B * T ∧
      s = T - (8 : k) • (B ^ 2 * v) + (24 * gamma : k) • B ∧
      (36 : k) • d ^ 2 - C (81 * epsilon * gamma + 27 * i3) = B * s ∧
      s.natDegree = 2 * D + N := by
  let D := 3 * N - 2 * S
  change ∃ i3 kappa : k, ∃ v W T q s : k[X],
    81 * epsilon * gamma + 27 * i3 ≠ 0 ∧ v.natDegree = N ∧
    FiveToSixQZeroFceZeroH68 B c d =
      (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
        (9 : k) • d ^ 2 ∧
    (4 : k) • FiveToSixQZeroFceZeroH68 B c d -
      C (81 * epsilon * gamma + 27 * i3) = B * T ∧
    s = T - (8 : k) • (B ^ 2 * v) + (24 * gamma : k) • B ∧
    (36 : k) • d ^ 2 - C (81 * epsilon * gamma + 27 * i3) = B * s ∧
    s.natDegree = 2 * D + N
  obtain ⟨i3, kappa, v, W, T, q, hv, hvdeg, hW, hc0,
      he, hH, hBT, hqdef, hBq, hqdeg⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_v_descent68
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
  have hvne : v ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hvdeg
    omega
  have hHtop :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_H_top68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  change _ ∧ (FiveToSixQZeroFceZeroH68 B c d).natDegree =
      D + 2 * N - (4 * N - 2 * S) at hHtop
  have hHdeg : (FiveToSixQZeroFceZeroH68 B c d).natDegree = N := by
    rw [hHtop.2]
    dsimp only [D]
    omega
  have h4Hdeg : ((4 : k) • FiveToSixQZeroFceZeroH68 B c d).natDegree = N := by
    rw [natDegree_smul _ (by norm_num : (4 : k) ≠ 0), hHdeg]
  have hconstlt : (C (81 * epsilon * gamma + 27 * i3) : k[X]).natDegree <
      ((4 : k) • FiveToSixQZeroFceZeroH68 B c d).natDegree := by
    rw [h4Hdeg]
    compute_degree
    omega
  have hPdeg : ((4 : k) • FiveToSixQZeroFceZeroH68 B c d -
      C (81 * epsilon * gamma + 27 * i3)).natDegree = N := by
    rw [natDegree_sub_eq_left_of_natDegree_lt hconstlt, h4Hdeg]
  have hPne : (4 : k) • FiveToSixQZeroFceZeroH68 B c d -
      C (81 * epsilon * gamma + 27 * i3) ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hPdeg
    omega
  have hTne : T ≠ 0 := by
    intro hz
    apply hPne
    rw [hBT, hz, mul_zero]
  have hTdeg : T.natDegree = N - D := by
    have hmuldeg := natDegree_mul hBne hTne
    rw [← hBT, hPdeg, hBdeg] at hmuldeg
    omega
  have hB2vne : B ^ 2 * v ≠ 0 := mul_ne_zero (pow_ne_zero 2 hBne) hvne
  have hB2vdeg : (B ^ 2 * v).natDegree = 2 * D + N := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hvne, natDegree_pow,
      hBdeg, hvdeg]
  let s := T - (8 : k) • (B ^ 2 * v) + (24 * gamma : k) • B
  have hlow : (T + (24 * gamma : k) • B).natDegree < 2 * D + N := by
    have hTle : T.natDegree ≤ N - D := hTdeg.le
    have hgamle : ((24 * gamma : k) • B).natDegree ≤ D := by
      compute_degree
      omega
    have hadd : (T + (24 * gamma : k) • B).natDegree ≤ max (N - D) D := by
      calc
        (T + (24 * gamma : k) • B).natDegree ≤
            max T.natDegree ((24 * gamma : k) • B).natDegree :=
          natDegree_add_le _ _
        _ ≤ max (N - D) D := max_le_max hTle hgamle
    dsimp only [D] at hTle hgamle hadd ⊢
    omega
  have hdomdeg : ((-(8 : k)) • (B ^ 2 * v)).natDegree = 2 * D + N := by
    rw [natDegree_smul _ (by norm_num : (-(8 : k)) ≠ 0), hB2vdeg]
  have hsdecomp : s = (-(8 : k)) • (B ^ 2 * v) +
      (T + (24 * gamma : k) • B) := by
    dsimp only [s]
    module
  have hsdeg : s.natDegree = 2 * D + N := by
    rw [hsdecomp, natDegree_add_eq_left_of_natDegree_lt]
    · exact hdomdeg
    · rw [hdomdeg]
      exact hlow
  have hsq : (36 : k) • d ^ 2 -
      C (81 * epsilon * gamma + 27 * i3) = B * s := by
    calc
      (36 : k) • d ^ 2 - C (81 * epsilon * gamma + 27 * i3) =
          ((4 : k) • FiveToSixQZeroFceZeroH68 B c d -
            C (81 * epsilon * gamma + 27 * i3)) -
            (8 : k) • (B ^ 3 * v) + (24 * gamma : k) • B ^ 2 := by
          rw [hH]
          module
      _ = B * T - (8 : k) • (B ^ 3 * v) +
          (24 * gamma : k) • B ^ 2 := by rw [hBT]
      _ = B * s := by
          dsimp only [s]
          simp only [mul_add, mul_sub, mul_smul_comm, pow_succ]
          ring
  exact ⟨i3, kappa, v, W, T, q, s, hc0, hvdeg, hH, hBT, rfl, hsq,
    hsdeg⟩

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_square_fiber68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalSquareFiber68

end Max11DegreeRoutes
