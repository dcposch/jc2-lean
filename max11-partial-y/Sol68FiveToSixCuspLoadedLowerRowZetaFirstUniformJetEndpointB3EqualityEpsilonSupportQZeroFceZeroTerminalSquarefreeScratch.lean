import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalVDescentScratch

/-! # Squarefreeness of the terminal divisor -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalSquarefree68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A common zero of `B` and `B'` would force successively
`d'=v'=c'=e'=A'=0`; the pinned row zero would then kill the nonzero
terminal constant. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_B_squarefree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    IsCoprime B (derivative B) := by
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
  have hz : zeta = 0 := hrest.2.2.1
  rcases had with ⟨j4, j3, hj4, hj3, hrow0, hrow1, hrow2, hpos, hiff⟩
  rw [hz] at hrow0 hrow1
  have hcop := fiveToSix_pinned_terminal_row_forces_isCoprime_B_d68
    alpha gamma epsilon eta terminal A B c d e hterminal hrow0
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := k) k]
  intro x
  rw [aeval_def, aeval_def]
  by_contra hboth
  push Not at hboth
  have hBx : B.eval x = 0 := by simpa [aeval_def] using hboth.1
  have hBpx : (derivative B).eval x = 0 := by
    simpa [aeval_def] using hboth.2
  have hcopx :=
    (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := k) k B d).mp
      hcop x
  rw [aeval_def, aeval_def] at hcopx
  have hdx : d.eval x ≠ 0 := by
    rcases hcopx with hBxn | hdxn
    · exact (hBxn hBx).elim
    · exact hdxn
  have hHpx : (derivative (FiveToSixQZeroFceZeroH68 B c d)).eval x = 0 := by
    have h := congrArg (fun R : k[X] => (derivative R).eval x) hBT
    simp only [derivative_sub, derivative_smul, derivative_C,
      derivative_mul, eval_add, eval_sub, eval_smul, eval_zero, eval_mul] at h
    rw [hBx, hBpx] at h
    norm_num at h ⊢
    exact h
  have hdpx : (derivative d).eval x = 0 := by
    have h := congrArg (fun R : k[X] => (derivative R).eval x) hH
    simp only [derivative_add, derivative_sub, derivative_smul,
      derivative_mul, derivative_pow, eval_add, eval_sub, eval_smul,
      eval_mul, eval_pow] at h
    rw [hBx, hBpx, hHpx] at h
    norm_num at h
    exact h.resolve_left hdx
  have hvpx : (derivative v).eval x = 0 := by
    have h := congrArg (fun R : k[X] => (derivative R).eval x) hBq
    simp only [derivative_sub, derivative_smul, derivative_C,
      derivative_mul, eval_add, eval_sub, eval_smul, eval_zero, eval_mul] at h
    rw [hBx, hBpx] at h
    have hc0' : (81 * epsilon * gamma + 27 * i3) ≠ 0 := hc0
    have h' : (81 * epsilon * gamma + 27 * i3) *
        (derivative v).eval x = 0 := by
      simpa only [smul_eq_mul, sub_zero, zero_mul, add_zero] using h
    exact (mul_eq_zero.mp h').resolve_left hc0'
  have hcpx : (derivative c).eval x = 0 := by
    have h := congrArg (fun R : k[X] => (derivative R).eval x) hv
    simp only [derivative_add, derivative_smul, derivative_C,
      derivative_mul, eval_add, eval_smul, eval_zero, eval_mul] at h
    rw [hBx, hBpx] at h
    norm_num at h ⊢
    exact h
  have hepx : (derivative e).eval x = 0 := by
    have h := congrArg (fun R : k[X] => (derivative R).eval x) he
    simp only [derivative_sub, derivative_smul, derivative_C,
      derivative_mul, derivative_pow, eval_sub, eval_smul, eval_zero,
      eval_add, eval_mul, eval_pow] at h
    rw [hBx, hBpx, hdpx, hvpx] at h
    norm_num at h ⊢
    exact h
  have hApx : (derivative A).eval x = 0 := by
    have h := congrArg (fun R : k[X] => R.eval x) hrow1
    simp only [secondaryResidualRowOnePolynomial68,
      cubicLoadRowOnePolynomial68, cubicLoadTPolynomial68,
      cubicLoadUPolynomial68, cubicLoadVPolynomial68,
      derivative_add, derivative_sub, derivative_smul, derivative_mul,
      derivative_pow, derivative_C, eval_add, eval_sub, eval_smul, eval_mul,
      eval_pow, eval_neg, eval_C] at h
    rw [hBx, hBpx, hcpx, hdpx, hepx] at h
    norm_num at h
    ring_nf at h
    have hd2 : d.eval x ^ 2 ≠ 0 := pow_ne_zero 2 hdx
    have hcoef : (-4 / 9 : k) ≠ 0 := by norm_num
    have hprod : (derivative A).eval x * d.eval x ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_right hcoef
    exact (mul_eq_zero.mp hprod).resolve_right hd2
  have hterminalZero : terminal = 0 := by
    have h := congrArg (fun R : k[X] => R.eval x) hrow0
    simp only [secondaryResidualRowZeroPolynomial68,
      cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
      cubicLoadVPolynomial68, derivative_add, derivative_sub,
      derivative_smul, derivative_mul, derivative_pow, derivative_C,
      eval_add, eval_sub, eval_smul, eval_mul, eval_pow, eval_neg, eval_C]
      at h
    rw [hBx, hBpx, hcpx, hdpx, hepx, hApx] at h
    norm_num at h
    ring_nf at h
    exact h.symm
  exact hterminal hterminalZero

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_B_squarefree68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalSquarefree68

end Max11DegreeRoutes
