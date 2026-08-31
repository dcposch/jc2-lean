import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalSquareFiberScratch

/-! # Source data on every simple terminal root -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalRootPacket68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- At a zero of `B`, the pinned terminal row reduces to one scalar
relation between `A'`, `B'`, `v`, and the nonzero square fiber. -/
theorem fiveToSix_qZero_terminal_rowZero_root_algebra68
    (alpha gamma epsilon eta terminal : k)
    (A B c d e v : k[X]) (x : k)
    (hBx : B.eval x = 0)
    (hv : (2 : k) • c + C (3 * gamma) = B * v)
    (he : e = (1 / 9 : k) • B ^ 2 - (1 / 2 : k) • (v * d) -
      C (3 / 4 * epsilon))
    (hrow : secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e = C terminal) :
    (2 / 9 : k) * d.eval x ^ 2 *
        ((derivative A).eval x * v.eval x -
          2 * (derivative B).eval x) = terminal := by
  have hv0 := congrArg (fun R : k[X] => R.eval x) hv
  have hv1 := congrArg (fun R : k[X] => (derivative R).eval x) hv
  have he0 := congrArg (fun R : k[X] => R.eval x) he
  have he1 := congrArg (fun R : k[X] => (derivative R).eval x) he
  simp only [derivative_add, derivative_sub, derivative_smul, derivative_C,
    derivative_mul, derivative_pow, eval_add, eval_sub, eval_smul, eval_mul,
    eval_pow, eval_C, eval_zero] at hv0 hv1 he0 he1
  rw [hBx] at hv0 hv1 he0 he1
  norm_num at hv0 hv1 he0 he1
  have hcval : c.eval x = -(3 / 2 : k) * gamma := by
    linear_combination (1 / 2 : k) * hv0
  have hcpval : (derivative c).eval x =
      (1 / 2 : k) * (derivative B).eval x * v.eval x := by
    linear_combination (1 / 2 : k) * hv1
  have heval : e.eval x =
      -(1 / 2 : k) * v.eval x * d.eval x - (3 / 4 : k) * epsilon := by
    linear_combination he0
  have hepval : (derivative e).eval x =
      -(1 / 2 : k) * ((derivative v).eval x * d.eval x +
        v.eval x * (derivative d).eval x) := by
    linear_combination he1
  have hr := congrArg (fun R : k[X] => R.eval x) hrow
  simp only [secondaryResidualRowZeroPolynomial68,
    cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68, derivative_add, derivative_sub,
    derivative_smul, derivative_mul, derivative_pow, derivative_C,
    eval_add, eval_sub, eval_smul, eval_mul, eval_pow, eval_neg, eval_C,
    eval_zero] at hr
  rw [hBx, hcval, hcpval, heval, hepval] at hr
  norm_num at hr
  ring_nf at hr ⊢
  exact hr

/-- Every root of the terminal divisor is simple, lies on the same
nonzero square fiber of `d`, and obeys the normalized row-zero slope
identity. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_root_packet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    ∃ i3 kappa : k, ∃ v : k[X],
      81 * epsilon * gamma + 27 * i3 ≠ 0 ∧
      IsCoprime B (derivative B) ∧
      ∀ x : k, B.eval x = 0 →
        (derivative B).eval x ≠ 0 ∧ d.eval x ≠ 0 ∧
        (36 : k) * d.eval x ^ 2 = 81 * epsilon * gamma + 27 * i3 ∧
        (81 * epsilon * gamma + 27 * i3) *
          ((derivative A).eval x * v.eval x -
            2 * (derivative B).eval x) = 162 * terminal := by
  obtain ⟨i3, kappa, v, W, T, q, hv, hvdeg, hW, hc0,
      he, hH, hBT, hqdef, hBq, hqdeg⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_v_descent68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  have hsf :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_B_squarefree68
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
  rw [hz] at hrow0
  have hcop := fiveToSix_pinned_terminal_row_forces_isCoprime_B_d68
    alpha gamma epsilon eta terminal A B c d e hterminal hrow0
  refine ⟨i3, kappa, v, hc0, hsf, ?_⟩
  intro x hBx
  have hBpx : (derivative B).eval x ≠ 0 := by
    have hx :=
      (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
        (k := k) k B (derivative B)).mp hsf x
    rw [aeval_def, aeval_def] at hx
    exact hx.resolve_left (not_ne_iff.mpr hBx)
  have hdx : d.eval x ≠ 0 := by
    have hx :=
      (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
        (k := k) k B d).mp hcop x
    rw [aeval_def, aeval_def] at hx
    exact hx.resolve_left (not_ne_iff.mpr hBx)
  have hHeval := congrArg (fun R : k[X] => R.eval x) hH
  have hBTeval := congrArg (fun R : k[X] => R.eval x) hBT
  simp only [eval_add, eval_sub, eval_smul, eval_mul, eval_pow, eval_C]
    at hHeval hBTeval
  rw [hBx] at hHeval hBTeval
  norm_num at hHeval hBTeval
  have hsq : (36 : k) * d.eval x ^ 2 =
      81 * epsilon * gamma + 27 * i3 := by
    linear_combination hBTeval - 4 * hHeval
  have hr := fiveToSix_qZero_terminal_rowZero_root_algebra68
    alpha gamma epsilon eta terminal A B c d e v x hBx hv he hrow0
  have hslope : (81 * epsilon * gamma + 27 * i3) *
      ((derivative A).eval x * v.eval x -
        2 * (derivative B).eval x) = 162 * terminal := by
    linear_combination
      (2 * (derivative B).eval x -
        (derivative A).eval x * v.eval x) * hsq + 162 * hr
  exact ⟨hBpx, hdx, hsq, hslope⟩

#print axioms fiveToSix_qZero_terminal_rowZero_root_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_root_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalRootPacket68

end Max11DegreeRoutes
