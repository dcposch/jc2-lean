import Grok68VanishingAInductionStepPart15Scratch

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

/-! ## Row-two load coefficient, uniformly -/

/-! ## Row-zero load under vanishing through `r-1` -/

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

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAInductionStep68
end Max11DegreeRoutes
