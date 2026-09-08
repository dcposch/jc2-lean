import Grok68VanishingAInductionStepPart06Scratch

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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_jet_vanishing_pred68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j < r → A.coeff (2 * N - j) = 0) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    A.coeff p * (B ^ 2).coeff (2 * D - r) +
      A.coeff (p - r) * B.coeff D ^ 2 +
      (3 : k) * (c ^ 2).coeff (2 * Cc - r) = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  have hjet :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S r hs hq hr hrD
  dsimp only at hjet
  rcases hjet with ⟨hfull, hB2⟩
  have hArest :
      ∑ j ∈ Finset.range (r + 1),
          A.coeff (p - j) * (B ^ 2).coeff (2 * D - (r - j)) =
        A.coeff p * (B ^ 2).coeff (2 * D - r) +
          A.coeff (p - r) * (B ^ 2).coeff (2 * D) := by
    have h0 : 0 ∈ Finset.range (r + 1) := by simp
    rw [← Finset.add_sum_erase (Finset.range (r + 1))
      (fun j => A.coeff (p - j) * (B ^ 2).coeff (2 * D - (r - j))) h0]
    have hr_mem : r ∈ (Finset.range (r + 1)).erase 0 := by
      simp only [Finset.mem_erase, Finset.mem_range, ne_eq]
      exact ⟨Nat.ne_of_gt hr, Nat.lt_succ_self r⟩
    rw [← Finset.add_sum_erase ((Finset.range (r + 1)).erase 0)
      (fun j => A.coeff (p - j) * (B ^ 2).coeff (2 * D - (r - j))) hr_mem]
    have hmid :
        ∑ j ∈ ((Finset.range (r + 1)).erase 0).erase r,
            A.coeff (p - j) * (B ^ 2).coeff (2 * D - (r - j)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hj0 := Finset.mem_erase.mp hj
      have hj1 := Finset.mem_erase.mp hj0.2
      have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj1.1)
      have hjr : j < r := by
        have : j < r + 1 := Finset.mem_range.mp hj1.2
        omega
      have hAj : A.coeff (p - j) = 0 := by
        simpa [p] using hAvan j hjpos hjr
      rw [hAj, zero_mul]
    simp only [Nat.sub_zero, Nat.sub_self, hmid, add_zero]
  have hB20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
    have hwall :=
      fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
    dsimp only at hwall
    rcases hwall with ⟨_, _, _, _, _, _, _, _, _, _, hB', hc', _, _, _, _, _⟩
    have h := coeff_mul_at_bounds68 B B D D hB' hB'
    rw [← two_mul] at h
    simpa [pow_two] using h
  have hcc : (c ^ 2).coeff (2 * Cc - r) =
      ∑ j ∈ Finset.range (r + 1),
        c.coeff (Cc - j) * c.coeff (Cc - (r - j)) := by
    have hwall :=
      fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
    dsimp only at hwall
    rcases hwall with ⟨_, _, _, _, _, _, _, _, _, _, _, hc', _, _, _, _, _⟩
    have hrC : r ≤ Cc := by dsimp only [Cc]; omega
    have h := coeff_mul_sub_bounds68 c c Cc Cc r hrC hrC hc' hc'
    have h2 : Cc + Cc = 2 * Cc := by ring
    simpa [pow_two, h2] using h
  rw [hArest, hB20] at hfull
  have hcc' : (3 : k) *
      ∑ j ∈ Finset.range (r + 1),
        c.coeff (Cc - j) * c.coeff (Cc - (r - j)) =
      (3 : k) * (c ^ 2).coeff (2 * Cc - r) := by
    rw [hcc]
  -- `hfull` still has the unfolded `4*N-2*S` in the sum; rewrite to `Cc`.
  dsimp only [p, D, Cc] at hfull hcc' ⊢
  linear_combination hfull - hcc'

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
