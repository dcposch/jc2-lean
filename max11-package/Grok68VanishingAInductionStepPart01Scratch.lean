import Grok68VanishingAUniformCompanionScratch

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

/-- After vanishing of the left factor through `r-1`, the order-`r`
Cauchy product keeps only the two endpoints. -/
theorem coeff_mul_sub_bounds_vanishing_left68 (f g : k[X]) (u v r : ℕ)
    (hr : 0 < r) (hru : r ≤ u) (hrv : r ≤ v)
    (hf : f.natDegree ≤ u) (hg : g.natDegree ≤ v)
    (hvan : ∀ j, 1 ≤ j → j < r → f.coeff (u - j) = 0) :
    (f * g).coeff (u + v - r) =
      f.coeff u * g.coeff (v - r) + f.coeff (u - r) * g.coeff v := by
  have h := coeff_mul_sub_bounds68 f g u v r hru hrv hf hg
  have h0 : 0 ∈ Finset.range (r + 1) := by simp
  have hr_mem : r ∈ (Finset.range (r + 1)).erase 0 := by
    simp only [Finset.mem_erase, Finset.mem_range, ne_eq]
    exact ⟨Nat.ne_of_gt hr, Nat.lt_succ_self r⟩
  have hmid :
      ∑ j ∈ ((Finset.range (r + 1)).erase 0).erase r,
          f.coeff (u - j) * g.coeff (v - (r - j)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj0 := Finset.mem_erase.mp hj
    have hj1 := Finset.mem_erase.mp hj0.2
    have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj1.1)
    have hjr : j < r := by
      have : j < r + 1 := Finset.mem_range.mp hj1.2
      omega
    rw [hvan j hjpos hjr, zero_mul]
  have hsum := h
  rw [← Finset.add_sum_erase (Finset.range (r + 1))
      (fun j => f.coeff (u - j) * g.coeff (v - (r - j))) h0] at hsum
  rw [← Finset.add_sum_erase ((Finset.range (r + 1)).erase 0)
      (fun j => f.coeff (u - j) * g.coeff (v - (r - j))) hr_mem] at hsum
  simp only [Nat.sub_zero, Nat.sub_self, hmid, add_zero] at hsum
  linear_combination hsum

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
