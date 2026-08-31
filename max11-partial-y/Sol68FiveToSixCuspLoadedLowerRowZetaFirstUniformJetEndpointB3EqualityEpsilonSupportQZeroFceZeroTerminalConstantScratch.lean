import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalUProfileScratch

/-! # Nonvanishing of the terminal `H`-fiber constant -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalConstant68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A nonunit `B` coprime to `d` cannot divide a zero-constant `H` fiber. -/
theorem fiveToSix_qZero_terminal_H_fiber_constant_ne_zero_algebra68
    (gamma c0 : k) (B d v H T : k[X])
    (hcop : IsCoprime B d) (hBnonunit : ¬ IsUnit B)
    (hH : H = (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
      (9 : k) • d ^ 2)
    (hBT : (4 : k) • H - C c0 = B * T) :
    c0 ≠ 0 := by
  intro hc0
  have hBT0 := hBT
  rw [hc0, C_0, sub_zero] at hBT0
  have hBH : B ∣ H := by
    refine ⟨(1 / 4 : k) • T, ?_⟩
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    have hBT' := congrArg (algebraMap k[X] (RatFunc k)) hBT0
    simp only [Polynomial.smul_eq_C_mul, map_mul, RatFunc.algebraMap_C]
      at hBT' ⊢
    simp only [map_div₀, map_ofNat, map_one] at hBT' ⊢
    ring_nf at hBT' ⊢
    linear_combination (1 / 4 : RatFunc k) * hBT'
  obtain ⟨qH, hqH⟩ := hBH
  have hBd2 : B ∣ d ^ 2 := by
    refine ⟨(1 / 9 : k) • qH - (2 / 9 : k) • (B ^ 2 * v) +
      (2 / 3 * gamma : k) • B, ?_⟩
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    have hH' := congrArg (algebraMap k[X] (RatFunc k)) hH
    have hqH' := congrArg (algebraMap k[X] (RatFunc k)) hqH
    simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      RatFunc.algebraMap_C] at hH' hqH' ⊢
    simp only [map_div₀, map_ofNat, map_one] at hH' hqH' ⊢
    ring_nf at hH' hqH' ⊢
    linear_combination (-1 / 9 : RatFunc k) * hH' +
      (1 / 9 : RatFunc k) * hqH'
  exact hBnonunit (hcop.pow_right.isUnit_of_dvd hBd2)

/-- In the actual nonzero-terminal branch, the constant defining the
`H`-fiber is nonzero. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_constant68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    ∃ i3 : k, ∃ v T : k[X],
      (4 : k) • FiveToSixQZeroFceZeroH68 B c d -
          C (81 * epsilon * gamma + 27 * i3) = B * T ∧
      T.natDegree = N - (3 * N - 2 * S) ∧
      81 * epsilon * gamma + 27 * i3 ≠ 0 := by
  obtain ⟨i3, v, T, hv, hvdeg, hTdef, hBT, hTdeg⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_H_quotient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  obtain ⟨vq, hvq, hvqdeg, he, hH, hDelta⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_quotient68
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
  have hBpos : 0 < B.natDegree := by
    have hB' : B.natDegree ≤ 3 * N - 2 * S := by omega
    have hbidx : 3 * N - 2 * S = 3 * N - G := by omega
    have hbcoeff : B.coeff (3 * N - 2 * S) ≠ 0 := by
      rw [hbidx]
      exact hBtop
    have hBdeg := natDegree_eq_of_le_of_coeff_ne_zero hB' hbcoeff
    rw [hBdeg]
    omega
  have hBnonunit : ¬ IsUnit B := not_isUnit_of_natDegree_pos B hBpos
  have hz : zeta = 0 := hrest.2.2.1
  rcases had with ⟨j4, j3, hj4, hj3, hrow0, hrow1, hrow2, hpos, hiff⟩
  rw [hz] at hrow0
  have hcop := fiveToSix_pinned_terminal_row_forces_isCoprime_B_d68
    alpha gamma epsilon eta terminal A B c d e hterminal hrow0
  have hvuniq : v = vq := by
    have hBne : B ≠ 0 := by
      intro hzB
      rw [hzB, natDegree_zero] at hBpos
      omega
    apply mul_left_cancel₀ hBne
    rw [← hv, ← hvq]
  subst vq
  have hc0 := fiveToSix_qZero_terminal_H_fiber_constant_ne_zero_algebra68
    gamma (81 * epsilon * gamma + 27 * i3) B d v
      (FiveToSixQZeroFceZeroH68 B c d) T hcop hBnonunit hH hBT
  exact ⟨i3, v, T, hBT, hTdeg, hc0⟩

#print axioms fiveToSix_qZero_terminal_H_fiber_constant_ne_zero_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_constant68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalConstant68

end Max11DegreeRoutes
