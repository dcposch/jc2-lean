import Grok68VanishingAInductionStepPart14Scratch

/-! # Uniform producing induction on the `q=0` vanishing-A chamber

Committed green through `k=4` produces vanishing `A_(2N-j)=0` for
`j≤4`, and matching from a granted vanishing depth is already uniform
(`Grok68VanishingAUniformCompanionScratch.lean`).

The order-`k` producing companion, under vanishing through `k-1`, does
not take per-`k` input:

* only the `A_p` slot of `A'` reaches the companion remainder index
  (the `A_(p-k)` slot overshoots `deg(Bc)`);
* remainder cancel reduces to the pair `W0_(2p-k-1)` and `A_p W2_(p-k-1)`,
  which cancel by the companion weights against `(B c)_(p-k)`;
* load cancel is the two-generator combination of the order-`k` disc
  and I4 jets with cofactors `(25P-14k)` and `(15P-14k)` (CAS leftover
  `0` on `k=2..7`, and the same closed form for general `k`).

This file lands remainder cancel, the load identity, and the producing
step uniformly on `1≤k≤D`.  Induction from the committed `k≤4` base
gives vanishing of `A` through `k=D` for every `m`.  Matching through
`k=D` is then a theorem of granted vanishing, so the comparison
polynomials drop to degree at most `N-1` and `E-D-1`.  Those degree
bounds are not the identities `r_c=r_e=0`, so the committed
`vanishingA_zero_remainder_impossible68` does not fire.

This is not a closure.  Named gap: the comparison remainders after
matching through `D`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Two-endpoint Cauchy products -/

/-! ## Remainder transport at an arbitrary positive index -/

/-! ## `A'` against a shorter right factor, after vanishing through `r-1` -/

/-! ## Remainder cancel under vanishing through `r-1` -/

/-! ## Row-two load as a derivative -/

/-! ## Derivative Cauchy products and the row-zero load splitting -/

/-! ## Source: order-`r` disc with vanishing through `r-1` -/

/-! ## Companion reduction under vanishing through `r-1` -/

/-! ## Matching algebra at the unmatched last slot -/

/-! ## Row-two load coefficient, uniformly -/

/-! ## Row-zero load under vanishing through `r-1` -/

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_L0_coeff_of_vanishing68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j < r → A.coeff (2 * N - j) = 0) :
    let p := 2 * N
    let T := B ^ 2 * derivative d + B * derivative B * d
    let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
    L0.coeff (2 * p - r - 1) =
      A.coeff p * T.coeff (p - 1 - r) +
        A.coeff (p - r) * T.coeff (p - 1) -
        (3 : k) * (B * c * derivative e).coeff (2 * p - r - 1) +
        (3 : k) * (c * derivative c * d).coeff (2 * p - r - 1) := by
  let p := 2 * N
  let T := B ^ 2 * derivative d + B * derivative B * d
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  change L0.coeff (2 * p - r - 1) =
    A.coeff p * T.coeff (p - 1 - r) +
      A.coeff (p - r) * T.coeff (p - 1) -
      (3 : k) * (B * c * derivative e).coeff (2 * p - r - 1) +
      (3 : k) * (c * derivative c * d).coeff (2 * p - r - 1)
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hL0poly : L0 = A * T -
      (3 : k) • (B * c * derivative e) +
      (3 : k) • (c * derivative c * d) := by
    dsimp only [L0, T, FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68]
    ring
  have hTdeg : T.natDegree ≤ p - 1 := by
    have hdd := natDegree_derivative_le d
    have hdB := natDegree_derivative_le B
    dsimp only [T]
    compute_degree
    omega
  have hvanA : ∀ j, 1 ≤ j → j < r → A.coeff (p - j) = 0 := by
    intro j hj1 hj2
    simpa [p] using hAvan j hj1 hj2
  have hrA : r ≤ p - 1 := by dsimp only [p]; omega
  have hAT := coeff_mul_sub_bounds_vanishing_left68
    A T p (p - 1) r hr (by dsimp only [p]; omega) hrA hA' hTdeg hvanA
  have hidx : p + (p - 1) - r = 2 * p - r - 1 := by dsimp only [p]; omega
  rw [hidx] at hAT
  rw [hL0poly]
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hAT]
  try ring

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
