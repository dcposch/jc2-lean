import Grok68VanishingAInductionStepPart04Scratch

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

theorem fiveToSix_qZero_rowTwo_load_derivative68 (B d : k[X]) :
    FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d =
      (6 : k) • derivative (B ^ 2 * d) := by
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68]
  have hsq : derivative (B ^ 2) = (2 : k) • (B * derivative B) := by
    rw [show B ^ 2 = B * B by ring, derivative_mul]
    simp only [two_smul]
    ring
  have hder : derivative (B ^ 2 * d) =
      (2 : k) • (B * derivative B * d) + B ^ 2 * derivative d := by
    rw [derivative_mul, hsq]
    simp only [two_smul]
    ring
  rw [hder]
  module

theorem fiveToSix_qZero_two_mul_self_derivative68 (p : k[X]) :
    derivative (p ^ 2) = (2 : k) • (p * derivative p) := by
  rw [show p ^ 2 = p * p by ring, derivative_mul]
  simp only [two_smul]
  ring

theorem fiveToSix_qZero_T_half_QR68 (B d : k[X]) :
    let Q := B ^ 2 * d
    let R := B ^ 2 * derivative d
    B ^ 2 * derivative d + B * derivative B * d =
      (1 / 2 : k) • (derivative Q + R) := by
  intro Q R
  have hder : derivative (B ^ 2 * d) =
      derivative (B ^ 2) * d + B ^ 2 * derivative d := by
    rw [derivative_mul]
  have hsq := fiveToSix_qZero_two_mul_self_derivative68 B
  dsimp only [Q, R]
  rw [hder, hsq, smul_mul_assoc, add_assoc]
  have htwice : B ^ 2 * derivative d + B ^ 2 * derivative d =
      (2 : k) • (B ^ 2 * derivative d) := by
    simp only [two_smul]
  rw [htwice, ← smul_add, smul_smul]
  norm_num
  ring

theorem fiveToSix_qZero_coeff_mul_derivative_sub68
    (f g : k[X]) (u v r : ℕ)
    (hv : 0 < v) (hru : r ≤ u) (hrv : r < v)
    (hf : f.natDegree ≤ u) (hg : g.natDegree ≤ v) :
    (f * derivative g).coeff (u + v - r - 1) =
      ∑ j ∈ Finset.range (r + 1),
        f.coeff (u - j) * ((v - (r - j) : ℕ) : k) *
          g.coeff (v - (r - j)) := by
  have hg' : (derivative g).natDegree ≤ v - 1 :=
    (natDegree_derivative_le g).trans (Nat.sub_le_sub_right hg 1)
  have hr' : r ≤ v - 1 := by omega
  have h := coeff_mul_sub_bounds68 f (derivative g) u (v - 1) r
    hru hr' hf hg'
  have hidx : u + (v - 1) - r = u + v - r - 1 := by omega
  rw [hidx] at h
  rw [h]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjle : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpos : 0 < v - (r - j) := by omega
  have hidx2 : (v - 1) - (r - j) = (v - (r - j)) - 1 := by omega
  have hder := coeff_derivative_at_bound68 g (v - (r - j)) hpos
  rw [hidx2, hder]
  ring

theorem fiveToSix_qZero_weight_split68 (f : ℕ → k) (α : k) (r : ℕ) :
    ∑ j ∈ Finset.range (r + 1), (α - (j : k)) * f j =
      α * ∑ j ∈ Finset.range (r + 1), f j -
        ∑ j ∈ Finset.range (r + 1), (j : k) * f j := by
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
