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

/-! ## Remainder transport at an arbitrary positive index -/

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_transport_at68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S i0 i2 : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hi0 : 0 < i0) (hi2 : 0 < i2) :
    let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
      alpha gamma epsilon zeta eta A B c d e
    let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
      alpha gamma epsilon zeta eta A B c d e
    W0.coeff i0 =
        (FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
          gamma epsilon A B c d e).coeff i0 ∧
      W2.coeff i2 =
        (FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
          gamma epsilon B c d).coeff i2 := by
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, he, hp, hrest⟩
  rcases hp with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hz : zeta = 0 := hrest.2.2.1
  rcases had with ⟨j4, j3, hj4, hj3, hrow0, hrow1, hrow2, hpos, hiff⟩
  have hfull0 := hpos i0 hi0
  change (FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
    alpha gamma epsilon zeta eta A B c d e).coeff i0 = 0 at hfull0
  rw [hz] at hfull0 ⊢
  have hfull2 :
      (FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
        alpha gamma epsilon 0 eta A B c d e).coeff i2 = 0 := by
    rw [hz] at hrow2
    rw [show FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
      alpha gamma epsilon 0 eta A B c d e =
      secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e by rfl, hrow2]
    simp
  have hexp0 := fiveToSix_zetaFirst_B3_equality_support_clean_rowZero_expansion68
    (k := k) alpha gamma epsilon eta A B c d e
  have hexp2 := fiveToSix_zetaFirst_B3_equality_support_clean_rowTwo_expansion68
    (k := k) alpha gamma epsilon eta A B c d e
  have hc0 := congrArg (fun Q : k[X] => Q.coeff i0) hexp0
  have hc2 := congrArg (fun Q : k[X] => Q.coeff i2) hexp2
  simp only [coeff_smul, coeff_add, smul_eq_mul, hfull0, mul_zero] at hc0
  simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul, hfull2, mul_zero]
    at hc2
  constructor
  · rw [show FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
        alpha gamma epsilon 0 eta A B c d e =
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
          alpha gamma epsilon 0 eta A B c d e -
        (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e +
          (3 / 2 * gamma : k) • (A * derivative A * d) +
          (3 / 4 * epsilon : k) • (A * B * derivative A) +
          FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68
            A B c d e) by rfl]
    simp only [coeff_sub, hfull0, zero_sub, coeff_add, coeff_smul, smul_eq_mul]
    linear_combination hc0
  · rw [show FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
        alpha gamma epsilon 0 eta A B c d e =
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
          alpha gamma epsilon 0 eta A B c d e -
        (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e -
          (9 * gamma : k) • (A * derivative d) +
          (9 / 2 * gamma : k) • (d * derivative A) +
          (9 / 4 * epsilon : k) • (derivative A * B) -
          (9 / 2 * epsilon : k) • (A * derivative B) +
          FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d) by rfl]
    simp only [coeff_sub, hfull2, zero_sub, coeff_add, coeff_smul, smul_eq_mul]
    linear_combination hc2

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

/-! ## Derivative Cauchy products and the row-zero load splitting -/

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

theorem fiveToSix_qZero_matched_weights_cancel68
    (P V E Cc BBD Sx lam : k) (r : ℕ)
    (hV : V = (4 / 7 : k) * P)
    (hE : E = (15 / 14 : k) * P)
    (hC : (2 : k) * Cc = (10 / 7 : k) * P) :
    let a0 := -((3 : k) * lam ^ 2)
    a0 * (((3 : k) * P - (r : k)) / 2 * BBD +
        (1 / 2 : k) * (V * BBD - Sx)) -
      (3 : k) * (-(lam ^ 2) * (E * BBD - Sx)) +
      (3 : k) * (lam ^ 2 / 2) * (((2 : k) * Cc - (r : k)) * BBD + Sx) =
      0 := by
  intro a0
  have hCc : Cc = (5 / 7 : k) * P := by linear_combination hC / 2
  dsimp only [a0]
  rw [hV, hE, hCc]
  ring

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

/-! ## Companion reduction under vanishing through `r-1` -/

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_companion_step68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j < r → A.coeff (2 * N - j) = 0)
    (hload :
      let p := 2 * N
      let D := 3 * N - 2 * S
      let V := 5 * N - 3 * S
      let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
      let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
      (6 : k) * ((p - r : ℕ) : k) * L0.coeff (2 * p - r - 1) +
        ((p : ℕ) : k) * A.coeff p * L2.coeff (p - r - 1) +
        (6 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) *
          B.coeff D ^ 2 * d.coeff V = 0) :
    A.coeff (2 * N - r) = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let i0 := 2 * p - r - 1
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hFne := fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hterminal hs hq
  have hFconst :
      Fce = C (Fce.coeff 0) :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hrem :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_remainder_step68
      alpha gamma epsilon zeta eta terminal A B c d e N G S r
      hs hq hr hrD hAvan
  dsimp only at hrem hload
  have hr2 : r < 2 * N := by omega
  have hrow2 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S r hs hq hr2
  dsimp only at hrow2
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrest⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases had with ⟨j4, j3, hj4, hj3, hrow0, hrow1, hrowTwo, hpos, hiff⟩
  have hi0pos : 0 < i0 := by dsimp only [i0, p]; omega
  have hfull0 := hpos i0 hi0pos
  have hfactor := fiveToSix_zetaFirst_B3_equality_support_load_factor68
    (k := k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  have hdecomp0 :
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
          alpha gamma epsilon zeta eta A B c d e =
        (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e +
          (3 / 2 * gamma : k) • (A * derivative A * d) +
          (3 / 4 * epsilon : k) • (A * B * derivative A) + L0) + W0 := by
    dsimp only [W0, L0,
      FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68]
    module
  change (FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
    alpha gamma epsilon zeta eta A B c d e).coeff i0 = 0 at hfull0
  rw [hdecomp0, hfactor.1] at hfull0
  change (A * derivative A * Fce - derivative A * J + L0 + W0).coeff i0 = 0
    at hfull0
  have hdA : (derivative A).natDegree ≤ p - 1 :=
    (natDegree_derivative_le A).trans (by dsimp only [p]; omega)
  have hJdeg : J.natDegree ≤ p := by
    have hloaded' := hs.1
    rcases hloaded' with ⟨hsupport, hrows⟩
    rcases hsupport with ⟨hstop, hTD⟩
    rcases hstop with ⟨hcur, ht, hstate, hclass, hraw0, hraw2⟩
    let T := S - 2 * D
    let t := min D T
    have htT : t = T := by dsimp only [t]; exact Nat.min_eq_right hTD
    have hstate' := hstate
    dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68] at hstate'
    have hjidx : 5 * N - 2 * S - (t - 1) - 1 = p := by
      dsimp only [D, T] at htT
      dsimp only [p]; omega
    rw [hjidx] at hstate'
    exact hstate'.2
  have hvanA : ∀ j, 1 ≤ j → j < r → A.coeff (p - j) = 0 := by
    intro j hj1 hj2
    simpa [p] using hAvan j hj1 hj2
  have hvanA' : ∀ j, 1 ≤ j → j < r →
      (derivative A).coeff ((p - 1) - j) = 0 := by
    intro j hj1 hj2
    have hidx : p - 1 - j + 1 = p - j := by omega
    rw [coeff_derivative, hidx]
    have hAj : A.coeff (p - j) = 0 := hvanA j hj1 hj2
    rw [hAj, zero_mul]
  have hrA : r ≤ p - 1 := by dsimp only [p]; omega
  have hrJ : r ≤ p := by dsimp only [p]; omega
  have hAJ := coeff_mul_sub_bounds_vanishing_left68
    (derivative A) J (p - 1) p r hr hrA hrJ hdA hJdeg hvanA'
  have hidxAJ : p - 1 + p - r = i0 := by dsimp only [i0, p]; omega
  rw [hidxAJ] at hAJ
  have hdAp : (derivative A).coeff (p - 1) =
      A.coeff p * ((p : ℕ) : k) := by
    rw [coeff_derivative, show p - 1 + 1 = p by omega]
    congr 1
    exact_mod_cast (show p - 1 + 1 = p by omega)
  have hdApr : (derivative A).coeff ((p - 1) - r) =
      A.coeff (p - r) * ((p - r : ℕ) : k) := by
    have hidx : p - 1 - r + 1 = p - r := by omega
    rw [coeff_derivative, hidx]
    congr 1
    exact_mod_cast hidx
  rw [hdAp, hdApr] at hAJ
  have hAA := coeff_mul_sub_bounds_vanishing_left68
    A (derivative A) p (p - 1) r hr (by dsimp only [p]; omega) hrA hA' hdA
    hvanA
  have hidxAA : p + (p - 1) - r = i0 := by dsimp only [i0, p]; omega
  rw [hidxAA, hdAp, hdApr] at hAA
  have hAAF : (A * derivative A * Fce).coeff i0 =
      Fce.coeff 0 * (A * derivative A).coeff i0 := by
    have heq : A * derivative A * Fce = Fce.coeff 0 • (A * derivative A) := by
      calc
        A * derivative A * Fce = (A * derivative A) * C (Fce.coeff 0) := by
          conv_lhs => rw [hFconst]
        _ = Fce.coeff 0 • (A * derivative A) := by
          simp only [smul_eq_C_mul]
          ring
    rw [heq, coeff_smul]
    rfl
  simp only [coeff_add, coeff_sub, hAAF, hAJ] at hfull0
  have hrow0 :
      Fce.coeff 0 *
          (A.coeff p * (A.coeff (p - r) * ((p - r : ℕ) : k)) +
            A.coeff (p - r) * (A.coeff p * ((p : ℕ) : k))) -
        (A.coeff p * ((p : ℕ) : k) * J.coeff (p - r) +
          A.coeff (p - r) * ((p - r : ℕ) : k) * J.coeff p) +
        L0.coeff i0 + W0.coeff i0 = 0 := by
    rw [hAA] at hfull0
    linear_combination hfull0
  have hcontract := fiveToSix_zetaFirst_B3_equality_supportLoaded_contracted68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68]
    at hcontract
  have htop := hcontract.2.1
  have hpOld : 11 * N - 7 * S = p := by dsimp only [p]; omega
  rw [hq, hpOld] at htop
  simp only [Nat.cast_zero, sub_zero] at htop
  have hNk : ((N : ℕ) : k) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hpcast : ((p : ℕ) : k) = (2 : k) * ((N : ℕ) : k) := by
    dsimp only [p]; push_cast; rfl
  have htopReduced :
      A.coeff p * Fce.coeff 0 +
        (2 : k) * (J.coeff p + B.coeff D ^ 2 * d.coeff V) = 0 := by
    have hprod : ((N : ℕ) : k) * (A.coeff p * Fce.coeff 0 +
        (2 : k) * (J.coeff p + B.coeff D ^ 2 * d.coeff V)) = 0 := by
      dsimp only [p, D, V, Fce, J] at htop ⊢
      rw [hpcast] at htop
      linear_combination htop
    exact (mul_eq_zero.mp hprod).resolve_left hNk
  have hpr : ((p - r : ℕ) : k) ≠ 0 := by
    exact_mod_cast (show p - r ≠ 0 by dsimp only [p]; omega)
  -- Clear denominators: multiply the row-zero identity by `6(p-r)`.
  have hcleared :
      (6 : k) * ((p - r : ℕ) : k) * Fce.coeff 0 *
          (A.coeff p * A.coeff (p - r) * ((p - r : ℕ) : k) +
            A.coeff (p - r) * A.coeff p * ((p : ℕ) : k)) -
        (6 : k) * ((p - r : ℕ) : k) *
          (A.coeff p * ((p : ℕ) : k) * J.coeff (p - r) +
            A.coeff (p - r) * ((p - r : ℕ) : k) * J.coeff p) +
        (6 : k) * ((p - r : ℕ) : k) * (L0.coeff i0 + W0.coeff i0) = 0 := by
    linear_combination (6 : k) * ((p - r : ℕ) : k) * hrow0
  -- Row-two supplies `6(p-r) J_(p-r)`.
  have hJpr :
      (6 : k) * ((p - r : ℕ) : k) * J.coeff (p - r) =
        -((3 : k) * ((p - r : ℕ) : k) * A.coeff (p - r) * Fce.coeff 0) -
          (L2.coeff (p - r - 1) + W2.coeff (p - r - 1)) := by
    have : (((p - r : ℕ) : k)) *
        ((3 : k) * A.coeff (p - r) * Fce.coeff 0 +
          (6 : k) * J.coeff (p - r)) +
        L2.coeff (p - r - 1) + W2.coeff (p - r - 1) = 0 := hrow2
    linear_combination this
  have hmain :
      (9 : k) * ((p - r : ℕ) : k) * ((2 : k) * ((p : ℕ) : k) - (r : k)) *
          Fce.coeff 0 * A.coeff p * A.coeff (p - r) +
        (6 : k) * ((p - r : ℕ) : k) * L0.coeff i0 +
        ((p : ℕ) : k) * A.coeff p * L2.coeff (p - r - 1) +
        (6 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) *
          B.coeff D ^ 2 * d.coeff V +
        (6 : k) * ((p - r : ℕ) : k) * W0.coeff i0 +
        ((p : ℕ) : k) * A.coeff p * W2.coeff (p - r - 1) = 0 := by
    have hrC : ((r : ℕ) : k) = ((p : ℕ) : k) - ((p - r : ℕ) : k) := by
      have hle : p - r ≤ p := Nat.sub_le p r
      have h : ((p - (p - r) : ℕ) : k) = ((p : ℕ) : k) - ((p - r : ℕ) : k) :=
        Nat.cast_sub hle
      have heq : p - (p - r) = r := by omega
      rw [heq] at h
      exact h
    have hJp : J.coeff p +
        (1 / 2 : k) * A.coeff p * Fce.coeff 0 + B.coeff D ^ 2 * d.coeff V = 0 := by
      linear_combination (1 / 2 : k) * htopReduced
    have h2pr_sum :
        (2 : k) * ((p : ℕ) : k) - (r : k) =
          ((p : ℕ) : k) + ((p - r : ℕ) : k) := by
      linear_combination -hrC
    have hmain' :
        (9 : k) * ((p - r : ℕ) : k) *
            (((p : ℕ) : k) + ((p - r : ℕ) : k)) *
            Fce.coeff 0 * A.coeff p * A.coeff (p - r) +
          (6 : k) * ((p - r : ℕ) : k) * L0.coeff i0 +
          ((p : ℕ) : k) * A.coeff p * L2.coeff (p - r - 1) +
          (6 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) *
            B.coeff D ^ 2 * d.coeff V +
          (6 : k) * ((p - r : ℕ) : k) * W0.coeff i0 +
          ((p : ℕ) : k) * A.coeff p * W2.coeff (p - r - 1) = 0 := by
      linear_combination hcleared +
        ((p : ℕ) : k) * A.coeff p * hJpr -
        (12 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) * hJp +
        (9 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) * htopReduced
    rw [h2pr_sum]
    exact hmain'
  have hFceA :
      (9 : k) * ((p - r : ℕ) : k) *
          ((2 : k) * ((p : ℕ) : k) - (r : k)) *
          Fce.coeff 0 * A.coeff p * A.coeff (p - r) = 0 := by
    linear_combination hmain - hload - hrem
  have h9 : (9 : k) ≠ 0 := by norm_num
  have h2pr : (2 : k) * ((p : ℕ) : k) - (r : k) ≠ 0 := by
    have h2p : (2 : ℕ) * p - r ≠ 0 := by dsimp only [p]; omega
    have : (2 : k) * ((p : ℕ) : k) - (r : k) = ((2 * p - r : ℕ) : k) := by
      have hle : r ≤ 2 * p := by dsimp only [p]; omega
      have h : ((2 * p - r : ℕ) : k) = ((2 * p : ℕ) : k) - (r : k) :=
        Nat.cast_sub hle
      push_cast at h
      exact h.symm
    rw [this]
    exact_mod_cast h2p
  have hfac : (9 : k) * ((p - r : ℕ) : k) *
      ((2 : k) * ((p : ℕ) : k) - (r : k)) * Fce.coeff 0 *
      A.coeff p ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h9 hpr) h2pr) hFne) ha0
  have hmul : ((9 : k) * ((p - r : ℕ) : k) *
      ((2 : k) * ((p : ℕ) : k) - (r : k)) * Fce.coeff 0 *
      A.coeff p) * A.coeff (p - r) = 0 := by
    linear_combination hFceA
  have hAr : A.coeff (p - r) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hfac
  simpa [p] using hAr

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

theorem fiveToSix_qZero_i4_reduced_of_ih68
    (b0 d0 : k) (bj cj ej dj : ℕ → k) (lam eGap cGap : k) (r : ℕ)
    (hr : 0 < r)
    (h0b : bj 0 = b0)
    (h0c : cj 0 = lam * b0)
    (h0e : ej 0 = -lam * d0)
    (h0d : dj 0 = d0)
    (hre : ej r = -lam * dj r + eGap)
    (hrc : cj r = lam * bj r + cGap)
    (hBc : ∀ j, 0 < j → j < r → cj j = lam * bj j)
    (hEd : ∀ j, 0 < j → j < r → ej j = -lam * dj j) :
    (∑ i ∈ Finset.range (r + 1), bj i * ej (r - i)) +
      (∑ i ∈ Finset.range (r + 1), cj i * dj (r - i)) =
      b0 * eGap + d0 * cGap := by
  have hBe := fiveToSix_qZero_sum_ends68 (fun i => bj i * ej (r - i)) r hr
  have hCd := fiveToSix_qZero_sum_ends68 (fun i => cj i * dj (r - i)) r hr
  have hmid :
      ∑ i ∈ (Finset.range r).erase 0,
        (bj i * ej (r - i) + cj i * dj (r - i)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi0 := Finset.mem_erase.mp hi
    have hir : i < r := Finset.mem_range.mp hi0.2
    have hi1 : 0 < i := Nat.pos_of_ne_zero hi0.1
    have hir1 : 0 < r - i := by omega
    have hir2 : r - i < r := by omega
    rw [hEd (r - i) hir1 hir2, hBc i hi1 hir]
    ring
  have hmid' :
      (∑ i ∈ (Finset.range r).erase 0, bj i * ej (r - i)) +
        ∑ i ∈ (Finset.range r).erase 0, cj i * dj (r - i) = 0 := by
    have hdistrib := Finset.sum_add_distrib
      (s := (Finset.range r).erase 0)
      (f := fun i => bj i * ej (r - i))
      (g := fun i => cj i * dj (r - i))
    exact hdistrib.symm.trans hmid
  rw [hBe, hCd]
  simp only [Nat.sub_zero, Nat.sub_self]
  rw [h0b, h0c, h0e, h0d, hre, hrc]
  linear_combination hmid'

theorem fiveToSix_qZero_weight_rev_split68 (f : ℕ → k) (α : k) (r : ℕ) :
    ∑ j ∈ Finset.range (r + 1), (α - ((r - j : ℕ) : k)) * f j =
      α * ∑ j ∈ Finset.range (r + 1), f j -
        ∑ j ∈ Finset.range (r + 1), ((r - j : ℕ) : k) * f j := by
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

theorem fiveToSix_qZero_Bc_of_matching_lt68
    (B c : k[X]) (D Cc : ℕ) (lam : k) (j : ℕ)
    (hjD : j ≤ D) (hjC : j ≤ Cc)
    (hB : B.natDegree ≤ D) (hc : c.natDegree ≤ Cc)
    (hmatch : ∀ t, t ≤ j → c.coeff (Cc - t) = lam * B.coeff (D - t)) :
    (B * c).coeff (D + Cc - j) = lam * (B ^ 2).coeff (2 * D - j) := by
  have hBc := coeff_mul_sub_bounds68 B c D Cc j hjD hjC hB hc
  have hBB := coeff_mul_sub_bounds68 B B D D j hjD hjD hB hB
  have hsum :
      ∑ i ∈ Finset.range (j + 1),
          B.coeff (D - i) * c.coeff (Cc - (j - i)) =
        lam * ∑ i ∈ Finset.range (j + 1),
          B.coeff (D - i) * B.coeff (D - (j - i)) := by
    have h' :
        ∑ i ∈ Finset.range (j + 1),
            B.coeff (D - i) * c.coeff (Cc - (j - i)) =
          ∑ i ∈ Finset.range (j + 1),
            B.coeff (D - i) * (lam * B.coeff (D - (j - i))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have : j - i ≤ j := by
        simp only [Finset.mem_range] at hi; omega
      rw [hmatch (j - i) this]
    rw [h']
    simp only [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    try ring
  have hBB' : (B ^ 2).coeff (2 * D - j) =
      ∑ i ∈ Finset.range (j + 1),
        B.coeff (D - i) * B.coeff (D - (j - i)) := by
    simpa [pow_two, two_mul] using hBB
  rw [hBc, hsum, hBB']

theorem fiveToSix_qZero_c2_of_matching_lt68
    (B c : k[X]) (D Cc : ℕ) (lam : k) (j : ℕ)
    (hjD : j ≤ D) (hjC : j ≤ Cc)
    (hB : B.natDegree ≤ D) (hc : c.natDegree ≤ Cc)
    (hmatch : ∀ t, t ≤ j → c.coeff (Cc - t) = lam * B.coeff (D - t)) :
    (c ^ 2).coeff (2 * Cc - j) = lam ^ 2 * (B ^ 2).coeff (2 * D - j) := by
  have hcc := coeff_mul_sub_bounds68 c c Cc Cc j hjC hjC hc hc
  have hBB := coeff_mul_sub_bounds68 B B D D j hjD hjD hB hB
  have hsum :
      ∑ i ∈ Finset.range (j + 1),
          c.coeff (Cc - i) * c.coeff (Cc - (j - i)) =
        lam ^ 2 * ∑ i ∈ Finset.range (j + 1),
          B.coeff (D - i) * B.coeff (D - (j - i)) := by
    have h' :
        ∑ i ∈ Finset.range (j + 1),
            c.coeff (Cc - i) * c.coeff (Cc - (j - i)) =
          ∑ i ∈ Finset.range (j + 1),
            (lam * B.coeff (D - i)) * (lam * B.coeff (D - (j - i))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi' : i ≤ j := by
        simp only [Finset.mem_range] at hi; omega
      have hj' : j - i ≤ j := by
        simp only [Finset.mem_range] at hi; omega
      rw [hmatch i hi', hmatch (j - i) hj']
    rw [h']
    simp only [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    try ring
  have hBB' : (B ^ 2).coeff (2 * D - j) =
      ∑ i ∈ Finset.range (j + 1),
        B.coeff (D - i) * B.coeff (D - (j - i)) := by
    simpa [pow_two, two_mul] using hBB
  have hcc' : (c ^ 2).coeff (2 * Cc - j) =
      ∑ i ∈ Finset.range (j + 1),
        c.coeff (Cc - i) * c.coeff (Cc - (j - i)) := by
    simpa [pow_two, two_mul] using hcc
  rw [hcc', hsum, hBB']

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

theorem fiveToSix_qZero_c2_of_matching_last68
    (B c : k[X]) (D Cc : ℕ) (lam cGap : k) (r : ℕ)
    (hr : 0 < r) (hrD : r ≤ D) (hrC : r ≤ Cc)
    (hB : B.natDegree ≤ D) (hc : c.natDegree ≤ Cc)
    (hmatch : ∀ t, t < r → c.coeff (Cc - t) = lam * B.coeff (D - t))
    (hgap : c.coeff (Cc - r) = lam * B.coeff (D - r) + cGap) :
    (c ^ 2).coeff (2 * Cc - r) =
      lam ^ 2 * (B ^ 2).coeff (2 * D - r) +
        (2 : k) * lam * B.coeff D * cGap := by
  have hcc := coeff_mul_sub_bounds68 c c Cc Cc r hrC hrC hc hc
  have hBB := coeff_mul_sub_bounds68 B B D D r hrD hrD hB hB
  have hCsplit := fiveToSix_qZero_sum_pair_ends68
    (fun i => c.coeff (Cc - i)) r hr
  have hBsplit := fiveToSix_qZero_sum_pair_ends68
    (fun i => B.coeff (D - i)) r hr
  have hmid :
      ∑ i ∈ (Finset.range r).erase 0,
        c.coeff (Cc - i) * c.coeff (Cc - (r - i)) =
        lam ^ 2 * ∑ i ∈ (Finset.range r).erase 0,
          B.coeff (D - i) * B.coeff (D - (r - i)) := by
    have h' :
        ∑ i ∈ (Finset.range r).erase 0,
            c.coeff (Cc - i) * c.coeff (Cc - (r - i)) =
          ∑ i ∈ (Finset.range r).erase 0,
            (lam * B.coeff (D - i)) * (lam * B.coeff (D - (r - i))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi0 := Finset.mem_erase.mp hi
      have hir : i < r := Finset.mem_range.mp hi0.2
      have hir2 : r - i < r := by omega
      rw [hmatch i hir, hmatch (r - i) hir2]
    rw [h']
    simp only [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    try ring
  have hc0 : c.coeff Cc = lam * B.coeff D := hmatch 0 hr
  have hBB' : (B ^ 2).coeff (2 * D - r) =
      ∑ i ∈ Finset.range (r + 1),
        B.coeff (D - i) * B.coeff (D - (r - i)) := by
    simpa [pow_two, two_mul] using hBB
  have hcc' : (c ^ 2).coeff (2 * Cc - r) =
      ∑ i ∈ Finset.range (r + 1),
        c.coeff (Cc - i) * c.coeff (Cc - (r - i)) := by
    simpa [pow_two, two_mul] using hcc
  rw [hcc', hCsplit]
  simp only [Nat.sub_zero, Nat.sub_self]
  rw [hmid, hgap, hc0, hBB', hBsplit]
  simp only [Nat.sub_zero, Nat.sub_self, pow_two]
  ring

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

/-! ## Row-two load coefficient, uniformly -/

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

/-! ## Row-zero load under vanishing through `r-1` -/

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_L0_coeff_of_vanishing68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j < r → A.coeff (2 * N - j) = 0) :
    let p := 2 * N
    let T := B ^ 2 * derivative d + B * derivative B * d
    let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
    L0.coeff (2 * p - r - 1) =
      A.coeff p * T.coeff (p - 1 - r) +
        A.coeff (p - r) * T.coeff (p - 1) -
        (3 : k) * (B * c * derivative e).coeff (2 * p - r - 1) +
        (3 : k) * (c * derivative c * d).coeff (2 * p - r - 1) := by
  let p := 2 * N
  let T := B ^ 2 * derivative d + B * derivative B * d
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  change L0.coeff (2 * p - r - 1) =
    A.coeff p * T.coeff (p - 1 - r) +
      A.coeff (p - r) * T.coeff (p - 1) -
      (3 : k) * (B * c * derivative e).coeff (2 * p - r - 1) +
      (3 : k) * (c * derivative c * d).coeff (2 * p - r - 1)
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hL0poly : L0 = A * T -
      (3 : k) • (B * c * derivative e) +
      (3 : k) • (c * derivative c * d) := by
    dsimp only [L0, T, FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68]
    ring
  have hTdeg : T.natDegree ≤ p - 1 := by
    have hdd := natDegree_derivative_le d
    have hdB := natDegree_derivative_le B
    dsimp only [T]
    compute_degree
    omega
  have hvanA : ∀ j, 1 ≤ j → j < r → A.coeff (p - j) = 0 := by
    intro j hj1 hj2
    simpa [p] using hAvan j hj1 hj2
  have hrA : r ≤ p - 1 := by dsimp only [p]; omega
  have hAT := coeff_mul_sub_bounds_vanishing_left68
    A T p (p - 1) r hr (by dsimp only [p]; omega) hrA hA' hTdeg hvanA
  have hidx : p + (p - 1) - r = 2 * p - r - 1 := by dsimp only [p]; omega
  rw [hidx] at hAT
  rw [hL0poly]
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hAT]
  try ring

/-! ## Load identity under vanishing through `r-1` -/

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_load_of_vanishing68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j < r → A.coeff (2 * N - j) = 0) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
    let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    (6 : k) * ((p - r : ℕ) : k) * L0.coeff (2 * p - r - 1) +
      ((p : ℕ) : k) * A.coeff p * L2.coeff (p - r - 1) +
      (6 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) *
        B.coeff D ^ 2 * d.coeff V = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let Q := B ^ 2 * d
  let R := B ^ 2 * derivative d
  let T := B ^ 2 * derivative d + B * derivative B * d
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let i0 := 2 * p - r - 1
  change (6 : k) * ((p - r : ℕ) : k) * L0.coeff i0 +
      ((p : ℕ) : k) * A.coeff p * L2.coeff (p - r - 1) +
      (6 : k) * ((p - r : ℕ) : k) ^ 2 * A.coeff (p - r) *
        B.coeff D ^ 2 * d.coeff V = 0
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hppos : 0 < p := by dsimp only [p]; omega
  have hrV : r < V := by dsimp only [D, V]; omega
  have hrE : r < E := by dsimp only [D, E]; omega
  have hVpos : 0 < V := by dsimp only [V]; omega
  have hEpos : 0 < E := by dsimp only [E]; omega
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by compute_degree; omega
  have hc2deg : (c ^ 2).natDegree ≤ 2 * Cc := by compute_degree; omega
  have hBcdeg : (B * c).natDegree ≤ D + Cc := by compute_degree; omega
  have hVcast : ((V : ℕ) : k) = (4 / 7 : k) * ((p : ℕ) : k) := by
    have hnat : 7 * V = 4 * p := by dsimp only [p, V]; omega
    have h := congrArg (fun n : ℕ => (n : k)) hnat
    push_cast at h; linear_combination h / 7
  have hEcast : ((E : ℕ) : k) = (15 / 14 : k) * ((p : ℕ) : k) := by
    have hnat : 14 * E = 15 * p := by dsimp only [p, E]; omega
    have h := congrArg (fun n : ℕ => (n : k)) hnat
    push_cast at h; linear_combination h / 14
  have hCcast : ((Cc : ℕ) : k) = (5 / 7 : k) * ((p : ℕ) : k) := by
    have hnat : 7 * Cc = 5 * p := by dsimp only [p, Cc]; omega
    have h := congrArg (fun n : ℕ => (n : k)) hnat
    push_cast at h; linear_combination h / 7
  have h2Ccast : (2 : k) * ((Cc : ℕ) : k) = (10 / 7 : k) * ((p : ℕ) : k) := by
    rw [hCcast]; ring
  have hprcast : ((p - r : ℕ) : k) = ((p : ℕ) : k) - (r : k) :=
    Nat.cast_sub (by omega)
  have hL2 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_coeff_sub68
      alpha gamma epsilon zeta eta terminal A B c d e N G S r hs hq hr hrD
  dsimp only at hL2
  have hQ : Q.coeff (p - r) =
      ∑ j ∈ Finset.range (r + 1),
        (B ^ 2).coeff (2 * D - j) * d.coeff (V - (r - j)) := by
    have h := coeff_mul_sub_bounds68 (B ^ 2) d (2 * D) V r
      (by omega) (by dsimp only [D, V]; omega) hB2deg hd'
    have hidx : 2 * D + V - r = p - r := by omega
    simpa [Q, hidx] using h
  have hR : R.coeff (p - 1 - r) =
      ∑ j ∈ Finset.range (r + 1),
        (B ^ 2).coeff (2 * D - j) * ((V - (r - j) : ℕ) : k) *
          d.coeff (V - (r - j)) := by
    have h := fiveToSix_qZero_coeff_mul_derivative_sub68 (B ^ 2) d
      (2 * D) V r hVpos (by omega) hrV hB2deg hd'
    have hidx : 2 * D + V - r - 1 = p - r - 1 := by omega
    have hRidx : p - 1 - r = p - r - 1 := by omega
    simpa [R, hidx, hRidx] using h
  let fQ : ℕ → k := fun j =>
    (B ^ 2).coeff (2 * D - j) * d.coeff (V - (r - j))
  let BBD : k := Q.coeff (p - r)
  have hBBDsum : BBD = ∑ j ∈ Finset.range (r + 1), fQ j := by
    dsimp only [BBD, fQ]
    exact hQ
  have hcastVr : ∀ j ∈ Finset.range (r + 1),
      ((V - (r - j) : ℕ) : k) = ((V : ℕ) : k) - ((r - j : ℕ) : k) := by
    intro j hj
    have : r - j ≤ V := by simp only [Finset.mem_range] at hj; omega
    exact Nat.cast_sub this
  have hRwt : R.coeff (p - 1 - r) =
      ((V : ℕ) : k) * BBD -
        ∑ j ∈ Finset.range (r + 1), ((r - j : ℕ) : k) * fQ j := by
    have h' :
        ∑ j ∈ Finset.range (r + 1),
            (B ^ 2).coeff (2 * D - j) * ((V - (r - j) : ℕ) : k) *
              d.coeff (V - (r - j)) =
          ∑ j ∈ Finset.range (r + 1),
            (((V : ℕ) : k) - ((r - j : ℕ) : k)) * fQ j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [hcastVr j hj]
      dsimp only [fQ]
      ring_nf
    rw [hR, h', fiveToSix_qZero_weight_rev_split68 fQ ((V : ℕ) : k) r,
      hBBDsum]
  let Sx : k := ((V : ℕ) : k) * BBD - R.coeff (p - 1 - r)
  have hSx : Sx = ∑ j ∈ Finset.range (r + 1), ((r - j : ℕ) : k) * fQ j := by
    dsimp only [Sx]
    rw [hRwt]
    ring
  have hTpoly := fiveToSix_qZero_T_half_QR68 B d
  dsimp only at hTpoly
  have hT : T = (1 / 2 : k) • (derivative Q + R) := by
    dsimp only [T, Q, R]; exact hTpoly
  have hTsub : T.coeff (p - 1 - r) =
      (1 / 2 : k) * ((((p : ℕ) : k) - (r : k)) * BBD +
        (((V : ℕ) : k) * BBD - Sx)) := by
    have hidx : p - 1 - r + 1 = p - r := by omega
    have hcast : (((p - 1 - r : ℕ) : k) + 1) = ((p - r : ℕ) : k) := by
      exact_mod_cast hidx
    rw [hT, coeff_smul, coeff_add, coeff_derivative, hidx, hcast, hprcast]
    simp only [smul_eq_mul]
    dsimp only [BBD, Sx]
    ring
  have hQtop : Q.coeff p = B.coeff D ^ 2 * d.coeff V := by
    have h := coeff_mul_at_bounds68 (B ^ 2) d (2 * D) V hB2deg hd'
    have hB20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
      have h' := coeff_mul_at_bounds68 B B D D hB' hB'
      rw [← two_mul] at h'
      simpa [pow_two] using h'
    have hidx : 2 * D + V = p := by omega
    rw [hidx] at h
    dsimp only [Q]
    rw [h, hB20]
  have hTtop : T.coeff (p - 1) =
      (1 / 2 : k) * (((p : ℕ) : k) + ((V : ℕ) : k)) *
        B.coeff D ^ 2 * d.coeff V := by
    have hQ' : (derivative Q).coeff (p - 1) =
        ((p : ℕ) : k) * Q.coeff p := by
      rw [coeff_derivative_at_bound68 Q p hppos, mul_comm]
    have hRtop : R.coeff (p - 1) =
        B.coeff D ^ 2 * ((V : ℕ) : k) * d.coeff V := by
      have hdd' : (derivative d).natDegree ≤ V - 1 :=
        (natDegree_derivative_le d).trans (Nat.sub_le_sub_right hd' 1)
      have h := coeff_mul_at_bounds68 (B ^ 2) (derivative d)
        (2 * D) (V - 1) hB2deg hdd'
      have hB20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
        have h' := coeff_mul_at_bounds68 B B D D hB' hB'
        rw [← two_mul] at h'
        simpa [pow_two] using h'
      have hidx : 2 * D + (V - 1) = p - 1 := by omega
      have hdtop := coeff_derivative_at_bound68 d V hVpos
      rw [hidx, hB20, hdtop] at h
      dsimp only [R]
      linear_combination h
    rw [hT, coeff_smul, coeff_add, hQ', hRtop, hQtop]
    simp only [smul_eq_mul]
    ring
  have hL0 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_L0_coeff_of_vanishing68
      alpha gamma epsilon zeta eta terminal A B c d e N G S r
      hs hq hr hrD hAvan
  dsimp only at hL0
  have hBCE :
      (B * c * derivative e).coeff i0 =
        ∑ j ∈ Finset.range (r + 1),
          (B * c).coeff (D + Cc - j) * ((E - (r - j) : ℕ) : k) *
            e.coeff (E - (r - j)) := by
    have h := fiveToSix_qZero_coeff_mul_derivative_sub68 (B * c) e
      (D + Cc) E r hEpos (by omega) hrE hBcdeg he'
    have hidx : D + Cc + E - r - 1 = i0 := by dsimp only [i0, p]; omega
    rw [hidx] at h
    simpa [mul_assoc] using h
  have hsqc := fiveToSix_qZero_two_mul_self_derivative68 c
  have hccdpoly : c * derivative c * d =
      (1 / 2 : k) • (derivative (c ^ 2) * d) := by
    have h : derivative (c ^ 2) * d =
        ((2 : k) • (c * derivative c)) * d := by rw [hsqc]
    have h2 : ((2 : k) • (c * derivative c)) * d =
        (2 : k) • (c * derivative c * d) := by
      simp only [smul_mul_assoc]
      try ring
    rw [h, h2, smul_smul]
    norm_num
    try ring
  have hCCD :
      (c * derivative c * d).coeff i0 =
        (1 / 2 : k) *
          ∑ j ∈ Finset.range (r + 1),
            ((2 * Cc - j : ℕ) : k) * (c ^ 2).coeff (2 * Cc - j) *
              d.coeff (V - (r - j)) := by
    have hc2' : (derivative (c ^ 2)).natDegree ≤ 2 * Cc - 1 :=
      (natDegree_derivative_le (c ^ 2)).trans
        (Nat.sub_le_sub_right hc2deg 1)
    have hrC : r ≤ 2 * Cc - 1 := by omega
    have h := coeff_mul_sub_bounds68 (derivative (c ^ 2)) d
      (2 * Cc - 1) V r hrC (by dsimp only [D, V]; omega) hc2' hd'
    have hidx : 2 * Cc - 1 + V - r = i0 := by dsimp only [i0, p]; omega
    rw [hidx] at h
    rw [hccdpoly, coeff_smul, h]
    simp only [smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hpos : 0 < 2 * Cc - j := by
      simp only [Finset.mem_range] at hj; omega
    have hidx2 : (2 * Cc - 1) - j = (2 * Cc - j) - 1 := by omega
    have hder := coeff_derivative_at_bound68 (c ^ 2) (2 * Cc - j) hpos
    rw [hidx2, hder, mul_comm]
    ring
  obtain ⟨lam, hlam⟩ : ∃ lam : k, lam * B.coeff D = c.coeff Cc := by
    refine ⟨c.coeff Cc * (B.coeff D)⁻¹, ?_⟩
    rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  obtain ⟨cGap, hgapc⟩ : ∃ cGap : k,
      c.coeff (Cc - r) = lam * B.coeff (D - r) + cGap :=
    ⟨c.coeff (Cc - r) - lam * B.coeff (D - r), by ring⟩
  obtain ⟨eGap, hgage⟩ : ∃ eGap : k,
      e.coeff (E - r) = -lam * d.coeff (V - r) + eGap :=
    ⟨e.coeff (E - r) + lam * d.coeff (V - r), by ring⟩
  have hI40 :=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).1
  have hmatchc : ∀ j, j < r →
      c.coeff (Cc - j) = lam * B.coeff (D - j) := by
    intro j hj
    have hbmul : B.coeff D * c.coeff (Cc - j) =
        c.coeff Cc * B.coeff (D - j) := by
      by_cases hj0 : j = 0
      · subst j
        simp only [Nat.sub_zero]
        ring
      · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
        have hK : r - 1 ≤ 3 * N - 2 * S := by omega
        have hAprev : ∀ t, 1 ≤ t → t ≤ r - 1 → A.coeff (2 * N - t) = 0 := by
          intro t ht1 ht2
          exact hAvan t ht1 (lt_of_le_of_lt ht2 (Nat.sub_lt hr (by omega)))
        have hBc :=
          fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_matching_through68
            alpha gamma epsilon zeta eta terminal A B c d e N G S (r - 1)
            hterminal hs hq (by omega) hK hAprev
        have hm := hBc j hj1 (by omega)
        dsimp only [D, Cc]
        exact (sub_eq_zero.mp hm).symm
    apply mul_left_cancel₀ hb0
    calc
      B.coeff D * c.coeff (Cc - j) = c.coeff Cc * B.coeff (D - j) := hbmul
      _ = (lam * B.coeff D) * B.coeff (D - j) := by rw [hlam]
      _ = B.coeff D * (lam * B.coeff (D - j)) := by ring
  have hmatche : ∀ j, j < r →
      e.coeff (E - j) = -lam * d.coeff (V - j) := by
    intro j hj
    have hbmul : B.coeff D * e.coeff (E - j) +
        c.coeff Cc * d.coeff (V - j) = 0 := by
      by_cases hj0 : j = 0
      · subst j
        simpa [Nat.sub_zero] using hI40
      · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
        have hK : r - 1 ≤ 3 * N - 2 * S := by omega
        have hAprev : ∀ t, 1 ≤ t → t ≤ r - 1 → A.coeff (2 * N - t) = 0 := by
          intro t ht1 ht2
          exact hAvan t ht1 (lt_of_le_of_lt ht2 (Nat.sub_lt hr (by omega)))
        have hEd :=
          fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_matching_through68
            alpha gamma epsilon zeta eta terminal A B c d e N G S (r - 1)
            hterminal hs hq (by omega) hK hAprev
        have hm := hEd j hj1 (by omega)
        exact hm
    apply mul_left_cancel₀ hb0
    have : B.coeff D * e.coeff (E - j) =
        -c.coeff Cc * d.coeff (V - j) := by linear_combination hbmul
    calc
      B.coeff D * e.coeff (E - j) = -c.coeff Cc * d.coeff (V - j) := this
      _ = -(lam * B.coeff D) * d.coeff (V - j) := by rw [hlam]
      _ = B.coeff D * (-lam * d.coeff (V - j)) := by ring
  have ha0lam : A.coeff p = -((3 : k) * lam ^ 2) := by
    have hc0 : c.coeff Cc = lam * B.coeff D := hlam.symm
    have : A.coeff p * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 := hD0
    rw [hc0] at this
    have hmul : B.coeff D ^ 2 * (A.coeff p + (3 : k) * lam ^ 2) = 0 := by
      linear_combination this
    have hsum : A.coeff p + (3 : k) * lam ^ 2 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hb0)
    linear_combination hsum
  have hBc_lt : ∀ j, j < r →
      (B * c).coeff (D + Cc - j) = lam * (B ^ 2).coeff (2 * D - j) := by
    intro j hj
    exact fiveToSix_qZero_Bc_of_matching_lt68 B c D Cc lam j
      (by omega) (by omega) hB' hc'
      (fun t ht => hmatchc t (lt_of_le_of_lt ht hj))
  have hc2_lt : ∀ j, j < r →
      (c ^ 2).coeff (2 * Cc - j) = lam ^ 2 * (B ^ 2).coeff (2 * D - j) := by
    intro j hj
    exact fiveToSix_qZero_c2_of_matching_lt68 B c D Cc lam j
      (by omega) (by omega) hB' hc'
      (fun t ht => hmatchc t (lt_of_le_of_lt ht hj))
  have hBc_last :=
    fiveToSix_qZero_Bc_of_matching_last68 B c D Cc lam cGap r hr
      hrD (by omega) hB' hc' hmatchc hgapc
  have hc2_last :=
    fiveToSix_qZero_c2_of_matching_last68 B c D Cc lam cGap r hr
      hrD (by omega) hB' hc' hmatchc hgapc
  have hcastEr : ∀ j ∈ Finset.range (r + 1),
      ((E - (r - j) : ℕ) : k) = ((E : ℕ) : k) - ((r - j : ℕ) : k) := by
    intro j hj
    have : r - j ≤ E := by simp only [Finset.mem_range] at hj; omega
    exact Nat.cast_sub this
  have hBCE_closed : (B * c * derivative e).coeff i0 =
      -(lam ^ 2) * (((E : ℕ) : k) * BBD - Sx) +
        lam * B.coeff D ^ 2 * (((E : ℕ) : k) - (r : k)) * eGap -
        lam * ((E : ℕ) : k) * B.coeff D * d.coeff V * cGap := by
    have hsplit := fiveToSix_qZero_sum_ends68
      (fun j => (B * c).coeff (D + Cc - j) * ((E - (r - j) : ℕ) : k) *
        e.coeff (E - (r - j))) r hr
    have hmid :
        ∑ j ∈ (Finset.range r).erase 0,
          (B * c).coeff (D + Cc - j) * ((E - (r - j) : ℕ) : k) *
            e.coeff (E - (r - j)) =
          ∑ j ∈ (Finset.range r).erase 0,
            (lam * (B ^ 2).coeff (2 * D - j)) * ((E - (r - j) : ℕ) : k) *
              (-lam * d.coeff (V - (r - j))) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj0 := Finset.mem_erase.mp hj
      have hjr : j < r := Finset.mem_range.mp hj0.2
      have hrj : r - j < r := by omega
      rw [hBc_lt j hjr, hmatche (r - j) hrj]
    have hf0 :
        (B * c).coeff (D + Cc) * ((E - r : ℕ) : k) * e.coeff (E - r) =
          lam * B.coeff D ^ 2 * ((E - r : ℕ) : k) *
            (-lam * d.coeff (V - r) + eGap) := by
      have htop := hBc_lt 0 hr
      have hb20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
        have h' := coeff_mul_at_bounds68 B B D D hB' hB'
        rw [← two_mul] at h'
        simpa [pow_two] using h'
      simp only [Nat.sub_zero] at htop ⊢
      rw [htop, hb20, hgage]
    have hfr :
        (B * c).coeff (D + Cc - r) * ((E : ℕ) : k) * e.coeff E =
          (lam * (B ^ 2).coeff (2 * D - r) + B.coeff D * cGap) *
            ((E : ℕ) : k) * (-lam * d.coeff V) := by
      rw [hBc_last]
      have he0 := hmatche 0 hr
      simp only [Nat.sub_zero] at he0
      rw [he0]
    have hmatch_all :
        ∑ j ∈ Finset.range (r + 1),
            (lam * (B ^ 2).coeff (2 * D - j)) * ((E - (r - j) : ℕ) : k) *
              (-lam * d.coeff (V - (r - j))) =
          -lam ^ 2 * (((E : ℕ) : k) * BBD - Sx) := by
      have h' :
          ∑ j ∈ Finset.range (r + 1),
              (lam * (B ^ 2).coeff (2 * D - j)) * ((E - (r - j) : ℕ) : k) *
                (-lam * d.coeff (V - (r - j))) =
            -lam ^ 2 * ∑ j ∈ Finset.range (r + 1),
              (((E : ℕ) : k) - ((r - j : ℕ) : k)) * fQ j := by
        have hcast : ∀ j ∈ Finset.range (r + 1),
            (lam * (B ^ 2).coeff (2 * D - j)) * ((E - (r - j) : ℕ) : k) *
              (-lam * d.coeff (V - (r - j))) =
              -lam ^ 2 * (((E : ℕ) : k) - ((r - j : ℕ) : k)) * fQ j := by
          intro j hj
          rw [hcastEr j hj]
          dsimp only [fQ]
          ring
        refine (Finset.sum_congr rfl hcast).trans ?_
        simp only [Finset.mul_sum] <;> ring
      have hEwt := fiveToSix_qZero_weight_rev_split68 fQ ((E : ℕ) : k) r
      rw [h', hEwt, hBBDsum, hSx] <;> ring
    have hpeelM := fiveToSix_qZero_sum_ends68
      (fun j => (lam * (B ^ 2).coeff (2 * D - j)) * ((E - (r - j) : ℕ) : k) *
        (-lam * d.coeff (V - (r - j)))) r hr
    have hb20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
      have h' := coeff_mul_at_bounds68 B B D D hB' hB'
      rw [← two_mul] at h'
      simpa [pow_two] using h'
    have hEr : ((E - r : ℕ) : k) = ((E : ℕ) : k) - (r : k) :=
      Nat.cast_sub (by omega)
    rw [hBCE, hsplit, hmid]
    simp only [Nat.sub_zero, Nat.sub_self]
    rw [hf0, hfr]
    simp only [Nat.sub_zero, Nat.sub_self] at hpeelM
    rw [hb20] at hpeelM
    -- LHS = matched endpoints with extras + middle;
    -- `hpeelM` identifies the matched bulk with `hmatch_all`.
    rw [hEr]
    linear_combination hmatch_all - hpeelM +
      (lam ^ 2 * B.coeff D ^ 2 * d.coeff (V - r)) * hEr
  have hcastCj : ∀ j ∈ Finset.range (r + 1),
      ((2 * Cc - j : ℕ) : k) = (2 : k) * ((Cc : ℕ) : k) - (j : k) := by
    intro j hj
    have : j ≤ 2 * Cc := by simp only [Finset.mem_range] at hj; omega
    have h2 : ((2 * Cc : ℕ) : k) = (2 : k) * ((Cc : ℕ) : k) := by
      push_cast; rfl
    rw [← h2, Nat.cast_sub this]
  have hCCD_closed : (c * derivative c * d).coeff i0 =
      (lam ^ 2 / 2) *
          (((2 : k) * ((Cc : ℕ) : k) - (r : k)) * BBD + Sx) +
        ((2 : k) * ((Cc : ℕ) : k) - (r : k)) *
          lam * B.coeff D * cGap * d.coeff V := by
    have hsplit := fiveToSix_qZero_sum_ends68
      (fun j => ((2 * Cc - j : ℕ) : k) * (c ^ 2).coeff (2 * Cc - j) *
        d.coeff (V - (r - j))) r hr
    have hmid :
        ∑ j ∈ (Finset.range r).erase 0,
          ((2 * Cc - j : ℕ) : k) * (c ^ 2).coeff (2 * Cc - j) *
            d.coeff (V - (r - j)) =
          ∑ j ∈ (Finset.range r).erase 0,
            ((2 * Cc - j : ℕ) : k) * (lam ^ 2 * (B ^ 2).coeff (2 * D - j)) *
              d.coeff (V - (r - j)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hjr : j < r := by
        have hj0 := Finset.mem_erase.mp hj
        exact Finset.mem_range.mp hj0.2
      rw [hc2_lt j hjr]
    have hc2top : (c ^ 2).coeff (2 * Cc) = (lam * B.coeff D) ^ 2 := by
      have h := coeff_mul_at_bounds68 c c Cc Cc hc' hc'
      have hc0 : c.coeff Cc = lam * B.coeff D := hmatchc 0 hr
      have h2 : Cc + Cc = 2 * Cc := by ring
      rw [← h2]
      simpa [pow_two, hc0] using h
    have hf0 :
        ((2 * Cc : ℕ) : k) * (c ^ 2).coeff (2 * Cc) * d.coeff (V - r) =
          ((2 : k) * ((Cc : ℕ) : k)) * (lam ^ 2 * B.coeff D ^ 2) *
            d.coeff (V - r) := by
      have h2 : ((2 * Cc : ℕ) : k) = (2 : k) * ((Cc : ℕ) : k) := by
        push_cast; rfl
      rw [h2, hc2top]
      ring
    have hfr :
        ((2 * Cc - r : ℕ) : k) * (c ^ 2).coeff (2 * Cc - r) * d.coeff V =
          ((2 : k) * ((Cc : ℕ) : k) - (r : k)) *
            (lam ^ 2 * (B ^ 2).coeff (2 * D - r) +
              (2 : k) * lam * B.coeff D * cGap) * d.coeff V := by
      have h2r : ((2 * Cc - r : ℕ) : k) =
          (2 : k) * ((Cc : ℕ) : k) - (r : k) := by
        have : r ≤ 2 * Cc := by omega
        have h2 : ((2 * Cc : ℕ) : k) = (2 : k) * ((Cc : ℕ) : k) := by
          push_cast; rfl
        rw [← h2, Nat.cast_sub this]
      rw [h2r, hc2_last]
    have hmatch_all :
        ∑ j ∈ Finset.range (r + 1),
            ((2 * Cc - j : ℕ) : k) * (lam ^ 2 * (B ^ 2).coeff (2 * D - j)) *
              d.coeff (V - (r - j)) =
          lam ^ 2 * (((2 : k) * ((Cc : ℕ) : k) - (r : k)) * BBD + Sx) := by
      have h' :
          ∑ j ∈ Finset.range (r + 1),
              ((2 * Cc - j : ℕ) : k) * (lam ^ 2 * (B ^ 2).coeff (2 * D - j)) *
                d.coeff (V - (r - j)) =
            lam ^ 2 * ∑ j ∈ Finset.range (r + 1),
              ((2 : k) * ((Cc : ℕ) : k) - (j : k)) * fQ j := by
        have hcast : ∀ j ∈ Finset.range (r + 1),
            ((2 * Cc - j : ℕ) : k) * (lam ^ 2 * (B ^ 2).coeff (2 * D - j)) *
              d.coeff (V - (r - j)) =
              lam ^ 2 * (((2 : k) * ((Cc : ℕ) : k) - (j : k)) * fQ j) := by
          intro j hj
          rw [hcastCj j hj]
          dsimp only [fQ]
          ring
        refine (Finset.sum_congr rfl hcast).trans ?_
        simp only [Finset.mul_sum]
      have hidx : ∀ j ∈ Finset.range (r + 1),
          (j : k) = (r : k) - ((r - j : ℕ) : k) := by
        intro j hj
        have hjle : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have : ((r - j : ℕ) : k) = (r : k) - (j : k) := Nat.cast_sub hjle
        linear_combination this
      have hwt :
          ∑ j ∈ Finset.range (r + 1),
              ((2 : k) * ((Cc : ℕ) : k) - (j : k)) * fQ j =
            ((2 : k) * ((Cc : ℕ) : k) - (r : k)) * BBD + Sx := by
        have h' :
            ∑ j ∈ Finset.range (r + 1),
                ((2 : k) * ((Cc : ℕ) : k) - (j : k)) * fQ j =
              ∑ j ∈ Finset.range (r + 1),
                (((2 : k) * ((Cc : ℕ) : k) - (r : k)) + ((r - j : ℕ) : k)) *
                  fQ j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have := hidx j hj
          rw [this]
          ring
        rw [h']
        simp only [add_mul, Finset.sum_add_distrib]
        rw [← Finset.mul_sum, hBBDsum, hSx] <;> ring
      rw [h', hwt] <;> ring
    have hpeelM := fiveToSix_qZero_sum_ends68
      (fun j => ((2 * Cc - j : ℕ) : k) * (lam ^ 2 * (B ^ 2).coeff (2 * D - j)) *
        d.coeff (V - (r - j))) r hr
    have hb20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
      have h' := coeff_mul_at_bounds68 B B D D hB' hB'
      rw [← two_mul] at h'
      simpa [pow_two] using h'
    have h2Cc : ((2 * Cc : ℕ) : k) = (2 : k) * ((Cc : ℕ) : k) := by
      push_cast; rfl
    have h2Ccr : ((2 * Cc - r : ℕ) : k) =
        (2 : k) * ((Cc : ℕ) : k) - (r : k) := by
      have : r ≤ 2 * Cc := by omega
      rw [← h2Cc, Nat.cast_sub this]
    rw [hCCD, hsplit, hmid]
    simp only [Nat.sub_zero, Nat.sub_self]
    rw [hf0, hfr]
    simp only [Nat.sub_zero, Nat.sub_self] at hpeelM
    rw [h2Cc, h2Ccr, hb20] at hpeelM
    linear_combination (1 / 2 : k) * (hmatch_all - hpeelM)
  -- Disc / I4 reduced forms vanish.
  have hDjet :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_jet_vanishing_pred68
      alpha gamma epsilon zeta eta terminal A B c d e N G S r
      hs hq hr hrD hAvan
  dsimp only at hDjet
  have hI4jet :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_I4_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S r
      hs hq hr hrD
  dsimp only at hI4jet
  have hB2conv : (B ^ 2).coeff (2 * D - r) =
      ∑ i ∈ Finset.range (r + 1),
        B.coeff (D - i) * B.coeff (D - (r - i)) := by
    have h := coeff_mul_sub_bounds68 B B D D r hrD hrD hB' hB'
    simpa [pow_two, two_mul] using h
  have hc2conv : (c ^ 2).coeff (2 * Cc - r) =
      ∑ i ∈ Finset.range (r + 1),
        c.coeff (Cc - i) * c.coeff (Cc - (r - i)) := by
    have h := coeff_mul_sub_bounds68 c c Cc Cc r
      (by dsimp only [Cc]; omega) (by dsimp only [Cc]; omega) hc' hc'
    simpa [pow_two, two_mul] using h
  let bj : ℕ → k := fun i => B.coeff (D - i)
  let cj : ℕ → k := fun i => c.coeff (Cc - i)
  let ej : ℕ → k := fun i => e.coeff (E - i)
  let dj' : ℕ → k := fun i => d.coeff (V - i)
  have hdiscRed :=
    fiveToSix_qZero_disc_reduced_of_ih68
      (A.coeff p) (A.coeff (p - r)) (B.coeff D) bj cj lam cGap r hr
      (by linear_combination ha0lam) rfl (hmatchc 0 hr)
      (by
        dsimp only [cj, bj]
        exact hgapc)
      (fun j hj1 hj2 => hmatchc j hj2)
  have hi4Red :=
    fiveToSix_qZero_i4_reduced_of_ih68
      (B.coeff D) (d.coeff V) bj cj ej dj' lam eGap cGap r hr
      rfl (hmatchc 0 hr) (hmatche 0 hr) rfl
      (by
        dsimp only [ej, dj']
        exact hgage)
      (by
        dsimp only [cj, bj]
        exact hgapc)
      (fun j hj1 hj2 => hmatchc j hj2)
      (fun j hj1 hj2 => hmatche j hj2)
  have hdisc0 : A.coeff (p - r) * B.coeff D ^ 2 +
      (6 : k) * lam * B.coeff D * cGap = 0 := by
    have hsrc : A.coeff p * (B ^ 2).coeff (2 * D - r) +
        A.coeff (p - r) * B.coeff D ^ 2 +
        (3 : k) * (c ^ 2).coeff (2 * Cc - r) = 0 := by
      dsimp only [p, D, Cc] at hDjet ⊢
      linear_combination hDjet
    have hsrc' :
        A.coeff p * ∑ i ∈ Finset.range (r + 1), bj i * bj (r - i) +
          A.coeff (p - r) * B.coeff D ^ 2 +
          (3 : k) * ∑ i ∈ Finset.range (r + 1), cj i * cj (r - i) = 0 := by
      dsimp only [bj, cj]
      rw [← hB2conv, ← hc2conv]
      exact hsrc
    have hred := hdiscRed
    dsimp only [bj, cj] at hred
    rw [hsrc'] at hred
    exact hred.symm
  have hi40 : B.coeff D * eGap + d.coeff V * cGap = 0 := by
    have hsrc :
        (∑ i ∈ Finset.range (r + 1), B.coeff (D - i) * e.coeff (E - (r - i))) +
          (∑ i ∈ Finset.range (r + 1),
            c.coeff (Cc - i) * d.coeff (V - (r - i))) = 0 := by
      dsimp only [D, Cc, V, E] at hI4jet ⊢
      exact hI4jet
    have hred := hi4Red
    dsimp only [bj, cj, ej, dj'] at hred
    rw [hsrc] at hred
    exact hred.symm
  have hL0closed : L0.coeff i0 =
      A.coeff p * T.coeff (p - 1 - r) +
        A.coeff (p - r) * T.coeff (p - 1) -
        (3 : k) * (B * c * derivative e).coeff i0 +
        (3 : k) * (c * derivative c * d).coeff i0 := by
    simpa [i0, p, T, L0] using hL0
  have hkernel :
      (((p : ℕ) : k) - (r : k)) * A.coeff (p - r) * B.coeff D ^ 2 *
          d.coeff V + L0.coeff i0 +
        ((p : ℕ) : k) * A.coeff p * BBD = 0 := by
    have hcombo :=
      fiveToSix_qZero_kernel_unfolded_combo68
        ((p : ℕ) : k) BBD Sx lam (A.coeff (p - r)) (B.coeff D)
        (d.coeff V) cGap eGap r
        ((V : ℕ) : k) ((E : ℕ) : k) ((Cc : ℕ) : k)
        hVcast hEcast h2Ccast
    have hL0eq : L0.coeff i0 =
        (-((3 : k) * lam ^ 2)) *
            ((1 / 2 : k) * ((((p : ℕ) : k) - (r : k)) * BBD +
              (((V : ℕ) : k) * BBD - Sx))) +
          A.coeff (p - r) *
            ((1 / 2 : k) * (((p : ℕ) : k) + ((V : ℕ) : k)) *
              B.coeff D ^ 2 * d.coeff V) -
          (3 : k) *
            (-(lam ^ 2) * (((E : ℕ) : k) * BBD - Sx) +
              lam * B.coeff D ^ 2 * (((E : ℕ) : k) - (r : k)) * eGap -
              lam * ((E : ℕ) : k) * B.coeff D * d.coeff V * cGap) +
          (3 : k) *
            ((lam ^ 2 / 2) *
                (((2 : k) * ((Cc : ℕ) : k) - (r : k)) * BBD + Sx) +
              ((2 : k) * ((Cc : ℕ) : k) - (r : k)) *
                lam * B.coeff D * cGap * d.coeff V) := by
      rw [hL0closed, ha0lam, hTsub, hTtop, hBCE_closed, hCCD_closed]
    rw [hL0eq, ha0lam]
    have h14 : (14 : k) ≠ 0 := by norm_num
    have hmul :
        (14 : k) *
          ((((p : ℕ) : k) - (r : k)) * A.coeff (p - r) * B.coeff D ^ 2 *
              d.coeff V +
            (-((3 : k) * lam ^ 2)) *
                ((1 / 2 : k) * ((((p : ℕ) : k) - (r : k)) * BBD +
                  (((V : ℕ) : k) * BBD - Sx))) +
              A.coeff (p - r) *
                ((1 / 2 : k) * (((p : ℕ) : k) + ((V : ℕ) : k)) *
                  B.coeff D ^ 2 * d.coeff V) -
              (3 : k) *
                (-(lam ^ 2) * (((E : ℕ) : k) * BBD - Sx) +
                  lam * B.coeff D ^ 2 * (((E : ℕ) : k) - (r : k)) * eGap -
                  lam * ((E : ℕ) : k) * B.coeff D * d.coeff V * cGap) +
              (3 : k) *
                ((lam ^ 2 / 2) *
                    (((2 : k) * ((Cc : ℕ) : k) - (r : k)) * BBD + Sx) +
                  ((2 : k) * ((Cc : ℕ) : k) - (r : k)) *
                    lam * B.coeff D * cGap * d.coeff V) +
            ((p : ℕ) : k) * (-((3 : k) * lam ^ 2)) * BBD) = 0 := by
      linear_combination hcombo +
        ((25 : k) * ((p : ℕ) : k) - (14 : k) * (r : k)) * d.coeff V * hdisc0 -
        (3 : k) * ((15 : k) * ((p : ℕ) : k) - (14 : k) * (r : k)) *
          (lam * B.coeff D) * hi40
    convert (mul_eq_zero.mp hmul).resolve_left h14 using 1 <;> ring
  have hL2BBD : L2.coeff (p - r - 1) =
      (6 : k) * ((p - r : ℕ) : k) * BBD := by
    simpa [BBD, Q] using hL2
  rw [hL2BBD, hprcast]
  linear_combination (6 : k) * (((p : ℕ) : k) - (r : k)) * hkernel

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

#print axioms coeff_mul_sub_bounds_vanishing_left68
#print axioms fiveToSix_qZero_derivA_mul_of_vanishing68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_transport_at68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_remainder_step68
#print axioms fiveToSix_qZero_rowTwo_load_derivative68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_jet_vanishing_pred68
#print axioms fiveToSix_qZero_disc_reduced_of_ih68
#print axioms fiveToSix_qZero_i4_reduced_of_ih68
#print axioms fiveToSix_qZero_matched_weights_cancel68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_load_of_vanishing68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_companion_of_vanishing68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_through_D68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_companion_step68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_induction_step68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68

end Max11DegreeRoutes
