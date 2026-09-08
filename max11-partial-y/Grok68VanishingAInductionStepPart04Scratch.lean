import Grok68VanishingAInductionStepPart03Scratch

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

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_remainder_step68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j < r → A.coeff (2 * N - j) = 0) :
    let p := 2 * N
    let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
      alpha gamma epsilon zeta eta A B c d e
    let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
      alpha gamma epsilon zeta eta A B c d e
    (6 : k) * ((p - r : ℕ) : k) * W0.coeff (2 * p - r - 1) +
      ((p : ℕ) : k) * A.coeff p * W2.coeff (p - r - 1) = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let i0 := 2 * p - r - 1
  let i2 := p - r - 1
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let C0 := FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
    gamma epsilon A B c d e
  let C2 := FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
    gamma epsilon B c d
  change (6 : k) * ((p - r : ℕ) : k) * W0.coeff i0 +
      ((p : ℕ) : k) * A.coeff p * W2.coeff i2 = 0
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hi0pos : 0 < i0 := by dsimp only [i0, p]; omega
  have hi2pos : 0 < i2 := by dsimp only [i2, p]; omega
  have htr :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_transport_at68
      alpha gamma epsilon zeta eta terminal A B c d e N G S i0 i2
      hs hq hi0pos hi2pos
  dsimp only at htr
  have hW0 : W0.coeff i0 = C0.coeff i0 := htr.1
  have hW2 : W2.coeff i2 = C2.coeff i2 := htr.2
  have hBdd : (B * d * derivative d).natDegree < i0 := by
    dsimp only [i0, p, D, V]; compute_degree; omega
  have hB'd2 : (derivative B * d ^ 2).natDegree < i0 := by
    dsimp only [i0, p, D, V]; compute_degree; omega
  have hd2B' : (d ^ 2 * derivative B).natDegree < i0 := by
    dsimp only [i0, p, D, V]; compute_degree; omega
  have hBe' : (B * derivative e).natDegree < i0 := by
    dsimp only [i0, p, D, E]; compute_degree; omega
  have hdc' : (d * derivative c).natDegree < i0 := by
    dsimp only [i0, p, Cc, V]; compute_degree; omega
  have hdAshort : (d * derivative A).natDegree < i0 := by
    dsimp only [i0, p, V]; compute_degree; omega
  have hdecomp0 :
      C0 = -(3 / 2 * gamma : k) • (B * derivative A * c) +
        ((3 : k) • (B * d * derivative d) + (3 : k) • (derivative B * d ^ 2) -
          (9 / 2 * gamma : k) • (B * derivative e) +
          (9 / 2 * gamma : k) • (d * derivative c) +
          (9 / 4 * epsilon : k) • (d * derivative A)) := by
    dsimp only [C0, FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68]
    module
  have hC0 : C0.coeff i0 =
      -((3 / 2 : k) * gamma) * (B * derivative A * c).coeff i0 := by
    rw [hdecomp0]
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
    rw [coeff_eq_zero_of_natDegree_lt hBdd,
      coeff_eq_zero_of_natDegree_lt hB'd2,
      coeff_eq_zero_of_natDegree_lt hBe',
      coeff_eq_zero_of_natDegree_lt hdc',
      coeff_eq_zero_of_natDegree_lt hdAshort]
    ring
  have hd'low : (derivative d).natDegree < i2 := by
    dsimp only [i2, p, V]; compute_degree; omega
  have hC2 : C2.coeff i2 =
      (9 : k) * gamma * (derivative (B * c)).coeff i2 := by
    dsimp only [C2, FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68]
    have hder : (derivative (B * c)).coeff i2 =
        (B * derivative c).coeff i2 + (c * derivative B).coeff i2 := by
      rw [derivative_mul, coeff_add]
      ac_rfl
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul,
      coeff_eq_zero_of_natDegree_lt hd'low, mul_zero, sub_zero]
    rw [hder]
    ring
  have hBcdeg : (B * c).natDegree ≤ D + Cc := by compute_degree; omega
  have hppos : 0 < p := by dsimp only [p]; omega
  have hrp : r < p := by dsimp only [p]; omega
  have hn : p - 1 ≤ i0 := by dsimp only [i0, p]; omega
  have hgap : (B * c).natDegree < i0 - (p - r - 1) := by
    have : i0 - (p - r - 1) = p := by dsimp only [i0, p]; omega
    rw [this]
    dsimp only [p, D, Cc] at hBcdeg ⊢
    omega
  have hvanp : ∀ j, 1 ≤ j → j < r → A.coeff (p - j) = 0 := by
    intro j hj1 hj2
    simpa [p] using hAvan j hj1 hj2
  have hBAc :
      (B * derivative A * c).coeff i0 =
        ((p : ℕ) : k) * A.coeff p * (B * c).coeff (p - r) := by
    have hring : B * derivative A * c = derivative A * (B * c) := by ring
    rw [hring]
    have h := fiveToSix_qZero_derivA_mul_of_vanishing68 A (B * c) p r i0
      hppos hr hrp hA' hn hvanp hgap
    have hidx : i0 - (p - 1) = p - r := by dsimp only [i0, p]; omega
    rw [hidx] at h
    exact h
  have hi2succ : i2 + 1 = p - r := by dsimp only [i2, p]; omega
  have hBc' : (derivative (B * c)).coeff i2 =
      ((p - r : ℕ) : k) * (B * c).coeff (p - r) := by
    rw [coeff_derivative, hi2succ]
    have hcast : ((i2 : k) + 1) = ((p - r : ℕ) : k) := by exact_mod_cast hi2succ
    rw [hcast, mul_comm]
  rw [hW0, hW2, hC0, hC2, hBAc, hBc']
  ring

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
