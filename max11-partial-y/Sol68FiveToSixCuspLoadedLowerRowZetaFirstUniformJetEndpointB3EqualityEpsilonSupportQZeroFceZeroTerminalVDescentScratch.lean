import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalConstantScratch

/-! # A constant remainder for `v` modulo `B` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalVDescent68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Quotient-coordinate form of the constant row-two first integral. -/
theorem fiveToSix_qZero_terminal_rowTwo_normal_algebra68
    (gamma epsilon kappa : k) (A B c d e v W H : k[X])
    (hv : (2 : k) • c + C (3 * gamma) = B * v)
    (he : e = (1 / 9 : k) • B ^ 2 - (1 / 2 : k) • (v * d) -
      C (3 / 4 * epsilon))
    (hW : W = (4 : k) • A + (3 : k) • v ^ 2)
    (hH : H = (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
      (9 : k) • d ^ 2)
    (hP : FiveToSixQZeroFceZeroRowTwoIntegral68 gamma epsilon A B c d e =
      C kappa) :
    -(B ^ 3 * W) + (24 : k) • (B ^ 2 * d) +
        (9 * gamma : k) • (B ^ 2 * v) + (6 : k) • (v * H) =
      C (6 * kappa) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hv' := congrArg (algebraMap k[X] (RatFunc k)) hv
  have he' := congrArg (algebraMap k[X] (RatFunc k)) he
  have hW' := congrArg (algebraMap k[X] (RatFunc k)) hW
  have hH' := congrArg (algebraMap k[X] (RatFunc k)) hH
  have hP' := congrArg (algebraMap k[X] (RatFunc k)) hP
  dsimp only [FiveToSixQZeroFceZeroRowTwoIntegral68] at hP'
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, RatFunc.algebraMap_C] at hv' he' hW' hH' hP' ⊢
  simp only [map_div₀, map_ofNat, map_one] at hv' he' hW' hH' hP' ⊢
  ring_nf at hv' he' hW' hH' hP' ⊢
  linear_combination (6 : RatFunc k) * hP' -
    (algebraMap k[X] (RatFunc k) B) ^ 3 * hW' +
    (108 : RatFunc k) * algebraMap k[X] (RatFunc k) d * he' -
    (9 : RatFunc k) * algebraMap k[X] (RatFunc k) B *
      (algebraMap k[X] (RatFunc k) B *
        algebraMap k[X] (RatFunc k) v +
        2 * algebraMap k[X] (RatFunc k) c) * hv' +
    (6 : RatFunc k) * algebraMap k[X] (RatFunc k) v * hH'

/-- The two constant first-integral fibers force `v` itself to have a
constant remainder modulo `B`; the complementary quotient again has exact
degree `N-D`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_v_descent68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    let D := 3 * N - 2 * S
    let Cg := (2 : k) • c + C (3 * gamma)
    ∃ i3 kappa : k, ∃ v W T q : k[X],
      Cg = B * v ∧ v.natDegree = N ∧
      W = (4 : k) • A + (3 : k) • v ^ 2 ∧
      81 * epsilon * gamma + 27 * i3 ≠ 0 ∧
      e = (1 / 9 : k) • B ^ 2 - (1 / 2 : k) • (v * d) -
        C (3 / 4 * epsilon) ∧
      FiveToSixQZeroFceZeroH68 B c d =
        (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
          (9 : k) • d ^ 2 ∧
      (4 : k) • FiveToSixQZeroFceZeroH68 B c d -
        C (81 * epsilon * gamma + 27 * i3) = B * T ∧
      q = (2 / 3 : k) • (B ^ 2 * W - (24 : k) • (B * d) -
          (9 * gamma : k) • (B * v)) - v * T ∧
      (81 * epsilon * gamma + 27 * i3 : k) • v - C (4 * kappa) =
        B * q ∧ q.natDegree = N - D := by
  let D := 3 * N - 2 * S
  let Cg := (2 : k) • c + C (3 * gamma)
  change ∃ i3 kappa : k, ∃ v W T q : k[X], Cg = B * v ∧
    v.natDegree = N ∧ W = (4 : k) • A + (3 : k) • v ^ 2 ∧
    81 * epsilon * gamma + 27 * i3 ≠ 0 ∧
    e = (1 / 9 : k) • B ^ 2 - (1 / 2 : k) • (v * d) -
      C (3 / 4 * epsilon) ∧
    FiveToSixQZeroFceZeroH68 B c d =
      (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
        (9 : k) • d ^ 2 ∧
    (4 : k) • FiveToSixQZeroFceZeroH68 B c d -
      C (81 * epsilon * gamma + 27 * i3) = B * T ∧
    q = (2 / 3 : k) • (B ^ 2 * W - (24 : k) • (B * d) -
        (9 * gamma : k) • (B * v)) - v * T ∧
    (81 * epsilon * gamma + 27 * i3 : k) • v - C (4 * kappa) =
      B * q ∧ q.natDegree = N - D
  obtain ⟨i3, v, T, hv, hvdeg0, hTdef, hBT, hTdeg⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_H_quotient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  obtain ⟨vq, hvq, hvqdeg, he, hH, hDelta⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_quotient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  obtain ⟨kappa, hP⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_rowTwo_integral68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
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
  have hB' : B.natDegree ≤ D := by dsimp only [D]; omega
  have hbidx : D = 3 * N - G := by dsimp only [D]; omega
  have hbcoeff : B.coeff D ≠ 0 := by rw [hbidx]; exact hBtop
  have hBdeg : B.natDegree = D :=
    natDegree_eq_of_le_of_coeff_ne_zero hB' hbcoeff
  have hBne : B ≠ 0 := by
    intro hzB
    apply hbcoeff
    rw [hzB, coeff_zero]
  have hBpos : 0 < B.natDegree := by rw [hBdeg]; dsimp only [D]; omega
  have hBnonunit : ¬ IsUnit B := not_isUnit_of_natDegree_pos B hBpos
  have hvuniq : v = vq := by
    apply mul_left_cancel₀ hBne
    rw [← hv, ← hvq]
  subst vq
  have hvdeg : v.natDegree = N := by
    rw [hvdeg0]
    omega
  have hz : zeta = 0 := hrest.2.2.1
  rcases had with ⟨j4, j3, hj4, hj3, hrow0, hrow1, hrow2, hpos, hiff⟩
  rw [hz] at hrow0
  have hcop := fiveToSix_pinned_terminal_row_forces_isCoprime_B_d68
    alpha gamma epsilon eta terminal A B c d e hterminal hrow0
  let c0 := 81 * epsilon * gamma + 27 * i3
  have hc0 : c0 ≠ 0 :=
    fiveToSix_qZero_terminal_H_fiber_constant_ne_zero_algebra68
      gamma c0 B d v (FiveToSixQZeroFceZeroH68 B c d) T
        hcop hBnonunit hH hBT
  let W := (4 : k) • A + (3 : k) • v ^ 2
  have hQ := fiveToSix_qZero_terminal_rowTwo_normal_algebra68
    gamma epsilon kappa A B c d e v W
      (FiveToSixQZeroFceZeroH68 B c d) hv he rfl hH hP
  let Rq := B ^ 2 * W - (24 : k) • (B * d) -
    (9 * gamma : k) • (B * v)
  let q := (2 / 3 : k) • Rq - v * T
  have hBq : (c0 : k) • v - C (4 * kappa) = B * q := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    have hQ' := congrArg (algebraMap k[X] (RatFunc k)) hQ
    have hBT' := congrArg (algebraMap k[X] (RatFunc k)) hBT
    dsimp only [q, Rq, c0] at hQ' hBT' ⊢
    simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, RatFunc.algebraMap_C] at hQ' hBT' ⊢
    simp only [map_div₀, map_ofNat, map_one] at hQ' hBT' ⊢
    ring_nf at hQ' hBT' ⊢
    linear_combination (2 / 3 : RatFunc k) * hQ' -
      algebraMap k[X] (RatFunc k) v * hBT'
  let Pv := (c0 : k) • v - C (4 * kappa)
  have hcvdeg : ((c0 : k) • v).natDegree = N := by
    rw [natDegree_smul v hc0, hvdeg]
  have hconstlt : (C (4 * kappa) : k[X]).natDegree <
      ((c0 : k) • v).natDegree := by
    rw [hcvdeg]
    compute_degree
    omega
  have hPvdeg : Pv.natDegree = N := by
    dsimp only [Pv]
    rw [natDegree_sub_eq_left_of_natDegree_lt hconstlt, hcvdeg]
  have hPvne : Pv ≠ 0 := by
    intro hzP
    rw [hzP, natDegree_zero] at hPvdeg
    omega
  have hqne : q ≠ 0 := by
    intro hzq
    apply hPvne
    change Pv = 0
    rw [show Pv = B * q by exact hBq, hzq, mul_zero]
  have hmuldeg := natDegree_mul hBne hqne
  have hqdeg : q.natDegree = N - D := by
    rw [← hBq, hPvdeg, hBdeg] at hmuldeg
    omega
  refine ⟨i3, kappa, v, W, T, q, hv, hvdeg, rfl, hc0,
    he, hH, hBT, ?_, hBq, hqdeg⟩
  rfl

#print axioms fiveToSix_qZero_terminal_rowTwo_normal_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_v_descent68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalVDescent68

end Max11DegreeRoutes
