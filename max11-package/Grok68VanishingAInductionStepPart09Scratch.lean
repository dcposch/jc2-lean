import Grok68VanishingAInductionStepPart08Scratch

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

theorem fiveToSix_qZero_disc_reduced_of_ih68
    (a0 ar b0 : k) (bj cj : ℕ → k) (lam cGap : k) (r : ℕ)
    (hr : 0 < r)
    (ha0 : a0 + (3 : k) * lam ^ 2 = 0)
    (h0b : bj 0 = b0)
    (h0c : cj 0 = lam * b0)
    (hrc : cj r = lam * bj r + cGap)
    (hmatch : ∀ j, 0 < j → j < r → cj j = lam * bj j) :
    a0 * (∑ i ∈ Finset.range (r + 1), bj i * bj (r - i)) + ar * b0 ^ 2 +
      (3 : k) * (∑ i ∈ Finset.range (r + 1), cj i * cj (r - i)) =
      ar * b0 ^ 2 + (6 : k) * lam * b0 * cGap := by
  have hBsplit := fiveToSix_qZero_sum_pair_ends68 bj r hr
  have hCsplit := fiveToSix_qZero_sum_pair_ends68 cj r hr
  rw [h0b] at hBsplit
  rw [h0c, hrc] at hCsplit
  have hmidc :
      ∑ i ∈ (Finset.range r).erase 0, cj i * cj (r - i) =
        lam ^ 2 * ∑ i ∈ (Finset.range r).erase 0, bj i * bj (r - i) := by
    have h :
        ∑ i ∈ (Finset.range r).erase 0, cj i * cj (r - i) =
          ∑ i ∈ (Finset.range r).erase 0, (lam * bj i) * (lam * bj (r - i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi0 := Finset.mem_erase.mp hi
      have hir : i < r := Finset.mem_range.mp hi0.2
      have hi1 : 0 < i := Nat.pos_of_ne_zero hi0.1
      have hir1 : 0 < r - i := by omega
      have hir2 : r - i < r := by omega
      rw [hmatch i hi1 hir, hmatch (r - i) hir1 hir2]
    rw [h]
    simp only [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    ring
  rw [hBsplit, hCsplit, hmidc]
  linear_combination (2 * b0 * bj r +
      ∑ i ∈ (Finset.range r).erase 0, bj i * bj (r - i)) * ha0

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
