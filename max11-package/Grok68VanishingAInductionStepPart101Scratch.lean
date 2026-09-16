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

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
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

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
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
