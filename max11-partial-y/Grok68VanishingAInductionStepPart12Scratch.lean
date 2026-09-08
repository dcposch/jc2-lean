import Grok68VanishingAInductionStepPart11Scratch

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

theorem fiveToSix_qZero_Bc_of_matching_last68
    (B c : k[X]) (D Cc : ℕ) (lam cGap : k) (r : ℕ)
    (hr : 0 < r) (hrD : r ≤ D) (hrC : r ≤ Cc)
    (hB : B.natDegree ≤ D) (hc : c.natDegree ≤ Cc)
    (hmatch : ∀ t, t < r → c.coeff (Cc - t) = lam * B.coeff (D - t))
    (hgap : c.coeff (Cc - r) = lam * B.coeff (D - r) + cGap) :
    (B * c).coeff (D + Cc - r) =
      lam * (B ^ 2).coeff (2 * D - r) + B.coeff D * cGap := by
  have hBc := coeff_mul_sub_bounds68 B c D Cc r hrD hrC hB hc
  have hBB := coeff_mul_sub_bounds68 B B D D r hrD hrD hB hB
  have hends := fiveToSix_qZero_sum_ends68
    (fun i => B.coeff (D - i) * c.coeff (Cc - (r - i))) r hr
  have hBends := fiveToSix_qZero_sum_ends68
    (fun i => B.coeff (D - i) * B.coeff (D - (r - i))) r hr
  have hmid :
      ∑ i ∈ (Finset.range r).erase 0,
        B.coeff (D - i) * c.coeff (Cc - (r - i)) =
        lam * ∑ i ∈ (Finset.range r).erase 0,
          B.coeff (D - i) * B.coeff (D - (r - i)) := by
    have h' :
        ∑ i ∈ (Finset.range r).erase 0,
            B.coeff (D - i) * c.coeff (Cc - (r - i)) =
          ∑ i ∈ (Finset.range r).erase 0,
            B.coeff (D - i) * (lam * B.coeff (D - (r - i))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi0 := Finset.mem_erase.mp hi
      have hir : r - i < r := by
        have : i < r := Finset.mem_range.mp hi0.2
        omega
      rw [hmatch (r - i) hir]
    rw [h']
    simp only [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    try ring
  have hc0 : c.coeff Cc = lam * B.coeff D := hmatch 0 hr
  have hBB' : (B ^ 2).coeff (2 * D - r) =
      ∑ i ∈ Finset.range (r + 1),
        B.coeff (D - i) * B.coeff (D - (r - i)) := by
    simpa [pow_two, two_mul] using hBB
  rw [hBc, hends]
  simp only [Nat.sub_zero, Nat.sub_self]
  rw [hmid, hgap, hc0, hBB', hBends]
  simp only [Nat.sub_zero, Nat.sub_self, pow_two]
  ring

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
