import Grok68VanishingAInductionStepPart17Scratch

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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_proportionality_through_D68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let E := 6 * N - 3 * S
    (∀ j, 1 ≤ j → j ≤ D → A.coeff (2 * N - j) = 0) ∧
      (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c).natDegree ≤ N - 1 ∧
      (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d).natDegree ≤
        E - D - 1 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let E := 6 * N - 3 * S
  have hAvan :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_through_D68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hprop :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_proportionality_of_vanishing_through_D68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hAvan
  dsimp only at hprop
  exact ⟨hAvan, hprop⟩

/-! ## Residual packet

Vanishing of `A` is now through `k=D` for every `m`, and matching
through `D` is the committed theorem of that granted vanishing.  The
comparison polynomials therefore drop to degree at most `N-1` and
`E-D-1`.  Those bounds are not the identities `r_c=r_e=0`, so
`vanishingA_zero_remainder_impossible68` does not fire.  Not a closure.
Named gap: the comparison remainders after matching through `D`. -/
def FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAInductionStepResidual68
    (gamma epsilon : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  (C (c.coeff (4 * N - 2 * S)) * X ^ N * B -
      C (B.coeff (3 * N - 2 * S)) * c).natDegree ≤ N - 1 ∧
    (C (B.coeff (3 * N - 2 * S)) * e +
        C (c.coeff (4 * N - 2 * S)) * X ^ N * d).natDegree ≤
      (6 * N - 3 * S) - (3 * N - 2 * S) - 1

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_induction_step68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAInductionStepResidual68
      gamma epsilon A B c d e N S :=
  (fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_proportionality_through_D68
    alpha gamma epsilon zeta eta terminal A B c d e N G S
    hterminal hs hq).2

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
