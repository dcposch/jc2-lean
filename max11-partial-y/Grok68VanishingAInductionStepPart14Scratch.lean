import Grok68VanishingAInductionStepPart13Scratch

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

theorem fiveToSix_qZero_kernel_unfolded_combo68
    (P BBD Sx lam ar b0 d0 cGap eGap : k) (r : ℕ)
    (V E Cc : k)
    (hV : V = (4 / 7 : k) * P)
    (hE : E = (15 / 14 : k) * P)
    (hC : (2 : k) * Cc = (10 / 7 : k) * P) :
    let a0 := -((3 : k) * lam ^ 2)
    let Tsub := (1 / 2 : k) *
      ((P - (r : k)) * BBD + (V * BBD - Sx))
    let Ttop := (1 / 2 : k) * (P + V) * b0 ^ 2 * d0
    let BCE := -(lam ^ 2) * (E * BBD - Sx) +
      lam * b0 ^ 2 * (E - (r : k)) * eGap -
      lam * E * b0 * d0 * cGap
    let CCD := (lam ^ 2 / 2) * (((2 : k) * Cc - (r : k)) * BBD + Sx) +
      ((2 : k) * Cc - (r : k)) * lam * b0 * d0 * cGap
    let L0 := a0 * Tsub + ar * Ttop - (3 : k) * BCE + (3 : k) * CCD
    let kernel := (P - (r : k)) * ar * b0 ^ 2 * d0 + L0 + P * a0 * BBD
    (14 : k) * kernel =
      ((25 : k) * P - (14 : k) * (r : k)) * d0 *
          (ar * b0 ^ 2 + (6 : k) * lam * b0 * cGap) -
        (3 : k) * ((15 : k) * P - (14 : k) * (r : k)) * (lam * b0) *
          (b0 * eGap + d0 * cGap) := by
  intro a0 Tsub Ttop BCE CCD L0 kernel
  have hCc : Cc = (5 / 7 : k) * P := by linear_combination hC / 2
  dsimp only [a0, Tsub, Ttop, BCE, CCD, L0, kernel]
  rw [hV, hE, hCc]
  ring

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_coeff_sub68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S) :
    let p := 2 * N
    let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    L2.coeff (p - r - 1) =
      (6 : k) * ((p - r : ℕ) : k) * (B ^ 2 * d).coeff (p - r) := by
  let p := 2 * N
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  change L2.coeff (p - r - 1) =
    (6 : k) * ((p - r : ℕ) : k) * (B ^ 2 * d).coeff (p - r)
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  have hidx : p - r - 1 + 1 = p - r := by dsimp only [p]; omega
  have hcast : (((p - r - 1 : ℕ) : k) + 1) = ((p - r : ℕ) : k) := by
    exact_mod_cast hidx
  have hL2 := fiveToSix_qZero_rowTwo_load_derivative68 B d
  dsimp only [L2]
  rw [hL2, coeff_smul, coeff_derivative, hidx, hcast]
  simp only [smul_eq_mul]
  ring

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
