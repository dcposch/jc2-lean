import Grok68VanishingAInductionStepPart02Scratch

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

theorem fiveToSix_qZero_derivA_mul_of_vanishing68
    (A g : k[X]) (p r n : ℕ)
    (hp : 0 < p) (hr : 0 < r) (hrp : r < p)
    (hA : A.natDegree ≤ p)
    (hn : p - 1 ≤ n)
    (hvan : ∀ j, 1 ≤ j → j < r → A.coeff (p - j) = 0)
    (hgap : g.natDegree < n - (p - r - 1)) :
    (derivative A * g).coeff n =
      ((p : ℕ) : k) * A.coeff p * g.coeff (n - (p - 1)) := by
  have hsum : (derivative A * g).coeff n =
      ∑ t ∈ Finset.range (n + 1),
        (derivative A).coeff t * g.coeff (n - t) := by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have hp1mem : p - 1 ∈ Finset.range (n + 1) := by
    simp only [Finset.mem_range]
    omega
  rw [hsum, ← Finset.add_sum_erase (Finset.range (n + 1))
      (fun t => (derivative A).coeff t * g.coeff (n - t)) hp1mem]
  have hdAp : (derivative A).coeff (p - 1) =
      A.coeff p * ((p : ℕ) : k) := by
    rw [coeff_derivative, show p - 1 + 1 = p by omega]
    congr 1
    exact_mod_cast (show p - 1 + 1 = p by omega)
  have hrest :
      ∑ t ∈ (Finset.range (n + 1)).erase (p - 1),
          (derivative A).coeff t * g.coeff (n - t) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    have ht0 := Finset.mem_erase.mp ht
    have htne : t ≠ p - 1 := ht0.1
    have htlt : t < n + 1 := Finset.mem_range.mp ht0.2
    rw [coeff_derivative]
    by_cases htp : p < t + 1
    · have : A.coeff (t + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (hA.trans_lt htp)
      rw [this, zero_mul, zero_mul]
    · have htple : t + 1 ≤ p := Nat.not_lt.mp htp
      by_cases htr : p - r ≤ t
      · have hj : 1 ≤ p - (t + 1) := by omega
        have hj2 : p - (t + 1) < r := by omega
        have hAvan : A.coeff (t + 1) = 0 := by
          have : t + 1 = p - (p - (t + 1)) := by omega
          rw [this]
          exact hvan (p - (t + 1)) hj hj2
        rw [hAvan, zero_mul, zero_mul]
      · have : n - t > g.natDegree := by omega
        rw [coeff_eq_zero_of_natDegree_lt this, mul_zero]
  rw [hrest, add_zero, hdAp]
  ring

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
