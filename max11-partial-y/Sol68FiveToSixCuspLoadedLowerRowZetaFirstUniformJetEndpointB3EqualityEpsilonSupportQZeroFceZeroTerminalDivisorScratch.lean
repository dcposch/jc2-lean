import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroDivisibilitySourceScratch

/-! # The nonzero terminal row fixes the zero-`Fce` divisor branch -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalDivisor68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- At a common root of `B` and `d`, every term in the pinned terminal row
vanishes.  A nonzero terminal constant therefore makes `B` and `d`
coprime. -/
theorem fiveToSix_pinned_terminal_row_forces_isCoprime_B_d68
    (alpha gamma epsilon eta terminal : k) (A B c d e : k[X])
    (hterminal : terminal ≠ 0)
    (hrow0 : secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e = C terminal) :
    IsCoprime B d := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := k) k]
  intro x
  rw [aeval_def, aeval_def]
  by_contra hboth
  push Not at hboth
  have hBx : B.eval x = 0 := by simpa [aeval_def] using hboth.1
  have hdx : d.eval x = 0 := by simpa [aeval_def] using hboth.2
  have heval := congrArg (fun R : k[X] => R.eval x) hrow0
  rw [cubicLoadRowZeroPolynomial68_uniform_pinned_eq68] at heval
  simp only [secondaryResidualRowZeroPolynomial68, eval_add, eval_sub,
    eval_mul, eval_pow, eval_smul, eval_neg, eval_C, hBx, hdx,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub, smul_zero]
    at heval
  norm_num at heval
  exact hterminal heval.symm

/-- In the nonzero-terminal problem, the earlier common-factor/coprime
split collapses: `B` is coprime to `d`, so `B ∣ (2c+3γ)d` forces the
global divisor `B ∣ 2c+3γ`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_divisor68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    B ∣ (2 : k) • c + C (3 * gamma) := by
  let Cg := (2 : k) • c + C (3 * gamma)
  have hglobal :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_global68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  rcases hglobal with ⟨i3, hFzero, hRce, hK⟩
  obtain ⟨kappa, hP⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_rowTwo_integral68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  have hdiv := fiveToSix_qZero_Fce_zero_basic_divisibilities68
    gamma epsilon kappa A B c d e hFzero hP
  change B ∣ Cg * d ∧ _ at hdiv
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
  have hz : zeta = 0 := hrest.2.2.1
  rcases had with ⟨j4, j3, hj4, hj3, hrow0, hrow1, hrow2, hpos, hiff⟩
  rw [hz] at hrow0
  have hcop := fiveToSix_pinned_terminal_row_forces_isCoprime_B_d68
    alpha gamma epsilon eta terminal A B c d e hterminal hrow0
  exact hcop.dvd_of_dvd_mul_right hdiv.1

#print axioms fiveToSix_pinned_terminal_row_forces_isCoprime_B_d68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_divisor68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalDivisor68

end Max11DegreeRoutes
