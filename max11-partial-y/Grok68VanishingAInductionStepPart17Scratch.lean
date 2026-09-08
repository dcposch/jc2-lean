import Grok68VanishingAInductionStepPart16Scratch

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

/-! ## Load identity under vanishing through `r-1` -/

/-! ## Producing step and induction through `D` -/

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_companion_of_vanishing68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j < r → A.coeff (2 * N - j) = 0) :
    A.coeff (2 * N - r) = 0 :=
  fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_companion_step68
    alpha gamma epsilon zeta eta terminal A B c d e N G S r
    hterminal hs hq hr hrD hAvan
    (fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_load_of_vanishing68
      alpha gamma epsilon zeta eta terminal A B c d e N G S r
      hterminal hs hq hr hrD hAvan)

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_through_D68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    ∀ j, 1 ≤ j → j ≤ 3 * N - 2 * S → A.coeff (2 * N - j) = 0 := by
  intro j hj1 hj2
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  have hDpos : 0 < 3 * N - 2 * S := hwall.2.1
  have hfour :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_through_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hgoal : ∀ n, n ≤ 3 * N - 2 * S → ∀ m, 1 ≤ m → m ≤ n →
      A.coeff (2 * N - m) = 0 := by
    intro n hn
    induction n with
    | zero =>
      intro m hm1 hm2
      omega
    | succ n ih =>
      intro m hm1 hm2
      have hsplit : m ≤ n ∨ m = n + 1 := by omega
      rcases hsplit with hle | heq
      · exact ih (by omega) m hm1 hle
      · have hm4 : m ≤ 4 ∨ 4 < m := by omega
        rcases hm4 with hm4 | hm4
        · exact hfour m hm1 hm4
        · have hrpos : 0 < n + 1 := Nat.succ_pos n
          have hrD : n + 1 ≤ 3 * N - 2 * S := by omega
          have hprev : ∀ t, 1 ≤ t → t < n + 1 → A.coeff (2 * N - t) = 0 := by
            intro t ht1 ht2
            exact ih (by omega) t ht1 (Nat.lt_succ_iff.mp ht2)
          have hstep :=
            fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_companion_of_vanishing68
              alpha gamma epsilon zeta eta terminal A B c d e N G S (n + 1)
              hterminal hs hq hrpos hrD hprev
          simpa [heq] using hstep
  exact hgoal (3 * N - 2 * S) le_rfl j hj1 hj2

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
