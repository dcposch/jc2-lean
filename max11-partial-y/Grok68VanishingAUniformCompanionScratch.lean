import Grok68VanishingAOrder4CompanionScratch

/-! # Uniform order-`k` matching on the `q=0` vanishing-A chamber

The producing companion split is landed through `k=4`
(`Sol68...QZeroCompanion*` and
`Grok68VanishingAOrder4CompanionScratch.lean`).  The matching
recurrence that consumes a vanishing row `A_(2N-k)=0` and returns
`c_Cc B_(D-k) - B_D c_(Cc-k) = 0` together with the `e/d` incidence is
a different object: it is uniform in `k` on the interval `1 ≤ k ≤ D`,
using only the order-`k` discriminant jet, the order-`k` uncompensated
I4 jet, the cusp/I4 tops, and previous matching rows.

This file lands that matching induction, the Cauchy product that
makes the jets uniform, and the elimination-count remainder form
through a granted vanishing depth `K ≤ D`.  Matching through `k=D`
drops the comparison polynomials to degree at most `N-1` and
`E-D-1`.  It does **not** force the remainders `r_c` and `r_e` to
vanish, so it does **not** give the identity
`c_Cc X^N B = B_D c`.

The terminal-style comparison of `(*)` *would* close if those
remainders vanished: `Be+cd=0` writes a degree-`3D` leading term
`-(1/9) B_D^3` as a constant.  That comparison is landed below as a
theorem with the extra hypotheses `R_c=R_e=0`.  Those hypotheses are
not an output of matching through `k=D`, nor of the charged integral
`(S)`.

The producing companion for `k ≥ 5` is the remaining input.  Disc
and I4 jets at those orders are now uniform (this file).  The gap is
the order-`k` remainder-cancel together with the order-`k` load
certificate, landed only for `k=1,2,3,4`.  This is not a closure.
The next unused source coefficient remains `A_(2N-5)`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAUniformCompanion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Uniform Cauchy product -/

/-- Reindex `{0,…,r}` by `j ↦ u-j` onto the high interval `{u-r,…,u}`. -/
theorem fiveToSix_qZero_sum_range_shift68
    (f : ℕ → k) (u r : ℕ) (hru : r ≤ u) :
    ∑ j ∈ Finset.range (r + 1), f (u - j) =
      ∑ i ∈ (Finset.range (u + 1)).filter (fun i => u - r ≤ i), f i := by
  induction r with
  | zero =>
    have hfilter :
        (Finset.range (u + 1)).filter (fun i => u ≤ i) = {u} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    simp only [Nat.sub_zero]
    rw [hfilter, Finset.sum_singleton]
  | succ r ih =>
    have hr0 : r ≤ u := by omega
    have hr1 : r + 1 ≤ u := by omega
    rw [Finset.sum_range_succ, ih hr0]
    have hfilter :
        (Finset.range (u + 1)).filter (fun i => u - (r + 1) ≤ i) =
          insert (u - (r + 1))
            ((Finset.range (u + 1)).filter (fun i => u - r ≤ i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      omega
    have hnot :
        u - (r + 1) ∉
          (Finset.range (u + 1)).filter (fun i => u - r ≤ i) := by
      simp only [Finset.mem_filter, Finset.mem_range, not_and, not_le]
      intro
      omega
    rw [hfilter, Finset.sum_insert hnot]
    abel

/-- Cauchy product `r` steps below the sum of two separate degree bounds. -/
theorem coeff_mul_sub_bounds68 (f g : k[X]) (u v r : ℕ)
    (hru : r ≤ u) (hrv : r ≤ v)
    (hf : f.natDegree ≤ u) (hg : g.natDegree ≤ v) :
    (f * g).coeff (u + v - r) =
      ∑ j ∈ Finset.range (r + 1),
        f.coeff (u - j) * g.coeff (v - (r - j)) := by
  let n := u + v - r
  have hsum : (f * g).coeff n =
      ∑ i ∈ Finset.range (n + 1), f.coeff i * g.coeff (n - i) := by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have hsubset :
      ((Finset.range (u + 1)).filter (fun i => u - r ≤ i)) ⊆
        Finset.range (n + 1) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    omega
  have hzero : ∀ i ∈ Finset.range (n + 1),
      i ∉ (Finset.range (u + 1)).filter (fun i => u - r ≤ i) →
        f.coeff i * g.coeff (n - i) = 0 := by
    intro i hi hni
    simp only [Finset.mem_filter, Finset.mem_range] at hi hni
    by_cases hiu : i < u + 1
    · have hlt : i < u - r := by
        have : ¬ u - r ≤ i := by
          intro hle
          exact hni ⟨hiu, hle⟩
        omega
      have : v < n - i := by
        dsimp only [n]; omega
      rw [coeff_eq_zero_of_natDegree_lt (hg.trans_lt this), mul_zero]
    · have : u < i := by omega
      rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt this), zero_mul]
  have hsupp :
      ∑ i ∈ Finset.range (n + 1), f.coeff i * g.coeff (n - i) =
        ∑ i ∈ (Finset.range (u + 1)).filter (fun i => u - r ≤ i),
          f.coeff i * g.coeff (n - i) :=
    (Finset.sum_subset hsubset hzero).symm
  have hshift := fiveToSix_qZero_sum_range_shift68
      (fun i => f.coeff i * g.coeff (n - i)) u r hru
  have hreidx :
      ∑ j ∈ Finset.range (r + 1), f.coeff (u - j) * g.coeff (n - (u - j)) =
        ∑ i ∈ (Finset.range (u + 1)).filter (fun i => u - r ≤ i),
          f.coeff i * g.coeff (n - i) := hshift
  have hidx : ∀ j ∈ Finset.range (r + 1),
      n - (u - j) = v - (r - j) := by
    intro j hj
    have : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    dsimp only [n]; omega
  rw [hsum, hsupp, ← hreidx]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [hidx j hj]

/-! ## Sum splits for the matching algebra -/

/-- Peel the two endpoints of a length-`r+1` convolution. -/
theorem fiveToSix_qZero_sum_pair_ends68 (f : ℕ → k) (r : ℕ) (hr : 0 < r) :
    ∑ i ∈ Finset.range (r + 1), f i * f (r - i) =
      (2 : k) * f 0 * f r +
        ∑ i ∈ (Finset.range r).erase 0, f i * f (r - i) := by
  have h0 : 0 ∈ Finset.range (r + 1) := by simp
  rw [← Finset.add_sum_erase (Finset.range (r + 1))
    (fun i => f i * f (r - i)) h0]
  have hr_mem : r ∈ (Finset.range (r + 1)).erase 0 := by
    simp only [Finset.mem_erase, Finset.mem_range, ne_eq]
    exact ⟨Nat.ne_of_gt hr, Nat.lt_succ_self r⟩
  rw [← Finset.add_sum_erase ((Finset.range (r + 1)).erase 0)
    (fun i => f i * f (r - i)) hr_mem]
  have hmid :
      ((Finset.range (r + 1)).erase 0).erase r = (Finset.range r).erase 0 := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_range, ne_eq]
    omega
  rw [hmid]
  simp only [Nat.sub_zero, Nat.sub_self]
  ring

/-- Peel the two endpoints of a general length-`r+1` sum. -/
theorem fiveToSix_qZero_sum_ends68 (f : ℕ → k) (r : ℕ) (hr : 0 < r) :
    ∑ i ∈ Finset.range (r + 1), f i =
      f 0 + f r + ∑ i ∈ (Finset.range r).erase 0, f i := by
  have h0 : 0 ∈ Finset.range (r + 1) := by simp
  rw [← Finset.add_sum_erase (Finset.range (r + 1)) f h0]
  have hr_mem : r ∈ (Finset.range (r + 1)).erase 0 := by
    simp only [Finset.mem_erase, Finset.mem_range, ne_eq]
    exact ⟨Nat.ne_of_gt hr, Nat.lt_succ_self r⟩
  rw [← Finset.add_sum_erase ((Finset.range (r + 1)).erase 0) f hr_mem]
  have hmid :
      ((Finset.range (r + 1)).erase 0).erase r = (Finset.range r).erase 0 := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_range, ne_eq]
    omega
  rw [hmid]
  abel

/-! ## Uniform matching algebra -/

/-- Order-`r` discriminant, after vanishing of `A` through `r` and matching
through `r-1`, reduces to the order-one logarithmic comparison. -/
theorem fiveToSix_qZero_vanishingA_Bc_jet_succ_algebra68
    (a b c : k) (bj cj : ℕ → k)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (r : ℕ) (hr : 0 < r)
    (h0b : bj 0 = b) (h0c : cj 0 = c)
    (hmatch : ∀ j, 0 < j → j < r → c * bj j - b * cj j = 0)
    (hD : a * (∑ i ∈ Finset.range (r + 1), bj i * bj (r - i)) +
        (3 : k) * (∑ i ∈ Finset.range (r + 1), cj i * cj (r - i)) = 0) :
    c * bj r - b * cj r = 0 := by
  have hBsplit := fiveToSix_qZero_sum_pair_ends68 bj r hr
  have hCsplit := fiveToSix_qZero_sum_pair_ends68 cj r hr
  rw [h0b] at hBsplit
  rw [h0c] at hCsplit
  have hmid0 :
      ∑ i ∈ (Finset.range r).erase 0,
        (a * bj i * bj (r - i) + (3 : k) * cj i * cj (r - i)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi0 := Finset.mem_erase.mp hi
    have hir : i < r := Finset.mem_range.mp hi0.2
    have hi1 : 0 < i := Nat.pos_of_ne_zero hi0.1
    have hir1 : 0 < r - i := by omega
    have hir2 : r - i < r := by omega
    have hmi := hmatch i hi1 hir
    have hmr := hmatch (r - i) hir1 hir2
    have hw :=
      fiveToSix_qZero_vanishingA_Bc_weighted_algebra68
        a b c (bj i) (cj i) hb hcusp hmi
    exact fiveToSix_qZero_vanishingA_Bc_cross_algebra68
      a b c (bj i) (cj i) (bj (r - i)) (cj (r - i)) hb hw hmr
  have hmid :
      a * (∑ i ∈ (Finset.range r).erase 0, bj i * bj (r - i)) +
        (3 : k) * (∑ i ∈ (Finset.range r).erase 0, cj i * cj (r - i)) = 0 := by
    have hdistrib :
        ∑ i ∈ (Finset.range r).erase 0,
            (a * bj i * bj (r - i) + (3 : k) * cj i * cj (r - i)) =
          a * (∑ i ∈ (Finset.range r).erase 0, bj i * bj (r - i)) +
            (3 : k) * (∑ i ∈ (Finset.range r).erase 0, cj i * cj (r - i)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro i _; ring
      · refine Finset.sum_congr rfl ?_
        intro i _; ring
    exact hdistrib.symm.trans hmid0
  have hD1 : (2 : k) * a * b * bj r + (6 : k) * c * cj r = 0 := by
    rw [hBsplit, hCsplit] at hD
    linear_combination hD - hmid
  exact fiveToSix_qZero_vanishingA_Bc_jet_one_algebra68
    a b c (bj r) (cj r) ha hb hcusp hD1

/-- Order-`r` uncompensated I4, after `B`/`c` matching through `r` and
`e`/`d` incidence through `r-1`, reduces to the order-one incidence. -/
theorem fiveToSix_qZero_vanishingA_ed_jet_succ_algebra68
    (b c : k) (bj cj ej dj : ℕ → k)
    (hb : b ≠ 0)
    (h0b : bj 0 = b) (h0c : cj 0 = c)
    (r : ℕ) (hr : 0 < r)
    (hI40 : b * ej 0 + c * dj 0 = 0)
    (hI4r : (∑ i ∈ Finset.range (r + 1), bj i * ej (r - i)) +
        (∑ i ∈ Finset.range (r + 1), cj i * dj (r - i)) = 0)
    (hBc : ∀ j, j ≤ r → c * bj j - b * cj j = 0)
    (hEd : ∀ j, j < r → b * ej j + c * dj j = 0) :
    b * ej r + c * dj r = 0 := by
  have hBe := fiveToSix_qZero_sum_ends68 (fun i => bj i * ej (r - i)) r hr
  have hCd := fiveToSix_qZero_sum_ends68 (fun i => cj i * dj (r - i)) r hr
  have hmid :
      ∑ i ∈ (Finset.range r).erase 0,
        (bj i * ej (r - i) + cj i * dj (r - i)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi0 := Finset.mem_erase.mp hi
    have hir : i < r := Finset.mem_range.mp hi0.2
    have hir1 : r - i < r := by omega
    have hE := hEd (r - i) hir1
    have hB := hBc i (Nat.le_of_lt hir)
    have hcross :=
      fiveToSix_qZero_vanishingA_ed_cross_algebra68
        b c (bj i) (cj i) (ej (r - i)) (dj (r - i)) hb hE hB
    linear_combination hcross
  have hend :
      bj r * ej 0 + cj r * dj 0 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68
      b c (bj r) (cj r) (ej 0) (dj 0) hb hI40 (hBc r le_rfl)
  have hleft : b * ej r + c * dj r = 0 := by
    rw [h0b] at hBe
    rw [h0c] at hCd
    simp only [Nat.sub_zero, Nat.sub_self] at hBe hCd
    have hsum :
        b * ej r + bj r * ej 0 +
            (∑ i ∈ (Finset.range r).erase 0, bj i * ej (r - i)) +
          (c * dj r + cj r * dj 0 +
            ∑ i ∈ (Finset.range r).erase 0, cj i * dj (r - i)) = 0 := by
      rw [hBe, hCd] at hI4r
      linear_combination hI4r
    have hmid' :
        (∑ i ∈ (Finset.range r).erase 0, bj i * ej (r - i)) +
          (∑ i ∈ (Finset.range r).erase 0, cj i * dj (r - i)) = 0 := by
      have hdistrib :
          ∑ i ∈ (Finset.range r).erase 0,
              (bj i * ej (r - i) + cj i * dj (r - i)) =
            (∑ i ∈ (Finset.range r).erase 0, bj i * ej (r - i)) +
              ∑ i ∈ (Finset.range r).erase 0, cj i * dj (r - i) :=
        Finset.sum_add_distrib
      exact hdistrib.symm.trans hmid
    linear_combination hsum - hend - hmid'
  exact hleft

/-! ## Source: uniform discriminant and I4 jets -/

/-- Packet arithmetic used by every uniform jet: `G=2S` on this wall
identifies `p+2D=U=2 Cc` and places `D` inside the reflected-discriminant
window. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    let U := 8 * N - 2 * G
    9 * N = 7 * S ∧ 0 < D ∧ D ≤ p ∧ D ≤ min S (7 * N - 2 * G - S) ∧
      p + 2 * D = U ∧ 2 * Cc = U ∧ Cc + V = D + E ∧ N + D = Cc ∧
      N + V = E ∧ A.natDegree ≤ p ∧ B.natDegree ≤ D ∧
      c.natDegree ≤ Cc ∧ d.natDegree ≤ V ∧ e.natDegree ≤ E ∧
      A.coeff p ≠ 0 ∧ B.coeff D ≠ 0 ∧
      A.coeff p * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let U := 8 * N - 2 * G
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
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
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hA' : A.natDegree ≤ p := by simpa [p] using hA
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
  have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hc
  have hd' : d.natDegree ≤ V := by dsimp only [V]; rw [hGS] at hd; omega
  have he' : e.natDegree ≤ E := by dsimp only [E]; rw [hGS] at he; omega
  have hDpos : 0 < D := by dsimp only [D]; omega
  have hDp : D ≤ p := by dsimp only [D, p]; omega
  have hDwin : D ≤ min S (7 * N - 2 * G - S) := by
    dsimp only [D]; rw [hGS]; omega
  have hpU : p + 2 * D = U := by
    dsimp only [p, D, U]; rw [hGS]; omega
  have hCcU : 2 * Cc = U := by
    dsimp only [Cc, U]; rw [hGS]; omega
  have hKV : Cc + V = D + E := by dsimp only [D, Cc, V, E]; omega
  have hND : N + D = Cc := by dsimp only [D, Cc]; omega
  have hNV : N + V = E := by dsimp only [V, E]; omega
  have ha0 : A.coeff p ≠ 0 := by simpa [p] using hatop
  have hb0 : B.coeff D ≠ 0 := by simpa [D, hGS] using hBtop
  have hD0 : A.coeff p * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 := by
    simpa [p, D, Cc, hGS] using hcuspEq
  exact ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV, hA', hB', hc',
    hd', he', ha0, hb0, hD0⟩

/-- Uniform reflected-discriminant jet on `1 ≤ r ≤ D`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_jet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    (∑ j ∈ Finset.range (r + 1),
          A.coeff (p - j) * (B ^ 2).coeff (2 * D - (r - j))) +
        (3 : k) *
          (∑ j ∈ Finset.range (r + 1),
            c.coeff (Cc - j) * c.coeff (Cc - (r - j))) = 0 ∧
      (B ^ 2).coeff (2 * D - r) =
        ∑ i ∈ Finset.range (r + 1),
          B.coeff (D - i) * B.coeff (D - (r - i)) := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let U := 8 * N - 2 * G
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
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
  rcases hrest with ⟨hless, hmu, hzeta, hzero, hDeltaDeg⟩
  have hrwin : r ≤ min S (7 * N - 2 * G - S) := le_trans hrD hDwin
  have href : (Delta.reflect U).coeff r = 0 := by
    dsimp only [Delta, U]
    exact hzero r hrwin
  have hU : r ≤ U := by
    dsimp only [U]; rw [hGS]; omega
  have hDelta : Delta.coeff (U - r) = 0 := by
    rw [coeff_reflect, revAt_le hU] at href
    exact href
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by compute_degree; omega
  have hr2D : r ≤ 2 * D := by omega
  have hABB := coeff_mul_sub_bounds68 A (B ^ 2) p (2 * D) r
    (le_trans hrD hDp) hr2D hA' hB2deg
  have hcc := coeff_mul_sub_bounds68 c c Cc Cc r
    (by dsimp only [Cc]; omega) (by dsimp only [Cc]; omega) hc' hc'
  have hB2 := coeff_mul_sub_bounds68 B B D D r hrD hrD hB' hB'
  have hB2' : (B ^ 2).coeff (2 * D - r) =
      ∑ i ∈ Finset.range (r + 1),
        B.coeff (D - i) * B.coeff (D - (r - i)) := by
    simpa [pow_two, two_mul] using hB2
  have hABB' : (A * B ^ 2).coeff (U - r) =
      ∑ j ∈ Finset.range (r + 1),
        A.coeff (p - j) * (B ^ 2).coeff (2 * D - (r - j)) := by
    have : p + 2 * D - r = U - r := by omega
    simpa [this] using hABB
  have hcc' : (c ^ 2).coeff (U - r) =
      ∑ j ∈ Finset.range (r + 1),
        c.coeff (Cc - j) * c.coeff (Cc - (r - j)) := by
    have : Cc + Cc - r = U - r := by omega
    simpa [this, pow_two] using hcc
  dsimp only [Delta, fiveToSixCuspDiscriminantPolynomial68] at hDelta
  simp only [coeff_add, coeff_smul, smul_eq_mul, hABB', hcc'] at hDelta
  refine ⟨?_, hB2'⟩
  linear_combination hDelta

/-- After vanishing of `A` through `r`, the discriminant jet is the
convolution of `B` and of `c` alone. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_jet_of_vanishing68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j ≤ r → A.coeff (2 * N - j) = 0) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    A.coeff p *
        (∑ i ∈ Finset.range (r + 1), B.coeff (D - i) * B.coeff (D - (r - i))) +
      (3 : k) *
        (∑ j ∈ Finset.range (r + 1),
          c.coeff (Cc - j) * c.coeff (Cc - (r - j))) = 0 := by
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
        A.coeff p * (B ^ 2).coeff (2 * D - r) := by
    have h0 : 0 ∈ Finset.range (r + 1) := by simp
    rw [← Finset.add_sum_erase (Finset.range (r + 1))
      (fun j => A.coeff (p - j) * (B ^ 2).coeff (2 * D - (r - j))) h0]
    have hrest :
        ∑ j ∈ (Finset.range (r + 1)).erase 0,
            A.coeff (p - j) * (B ^ 2).coeff (2 * D - (r - j)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hj0 := Finset.mem_erase.mp hj
      have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0.1)
      have hj2 : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj0.2)
      have hAj : A.coeff (p - j) = 0 := by
        simpa [p] using hAvan j hj1 hj2
      rw [hAj, zero_mul]
    simp only [Nat.sub_zero, hrest, add_zero]
  rw [hArest, hB2] at hfull
  linear_combination hfull

/-- Uniform uncompensated I4 jet on `1 ≤ r ≤ D`.  Secondary summands
`B^3`, `d`, and `B` are strictly shorter than `K-r`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_I4_jet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    (∑ i ∈ Finset.range (r + 1), B.coeff (D - i) * e.coeff (E - (r - i))) +
      (∑ i ∈ Finset.range (r + 1),
        c.coeff (Cc - i) * d.coeff (V - (r - i))) = 0 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let K := D + E
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hFconst :
      Fce = C (Fce.coeff 0) :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hKr : r < K := by dsimp only [D, E, K]; omega
  have hFK : Fce.coeff (K - r) = 0 := by
    rw [hFconst, coeff_C]
    split_ifs with h
    · omega
    · rfl
  have hB3low : (B ^ 3).natDegree < K - r := by
    have : (B ^ 3).natDegree ≤ 3 * D := by compute_degree; omega
    dsimp only [D, E, K] at *; omega
  have hdLow : d.natDegree < K - r := by
    dsimp only [D, E, K, V] at *; omega
  have hBLow : B.natDegree < K - r := by
    dsimp only [D, E, K] at *; omega
  have hrE : r ≤ E := by dsimp only [D, E]; omega
  have hrV : r ≤ V := by dsimp only [D, V]; omega
  have hrC : r ≤ Cc := by dsimp only [D, Cc]; omega
  have hBe := coeff_mul_sub_bounds68 B e D E r hrD hrE hB' he'
  have hcd := coeff_mul_sub_bounds68 c d Cc V r hrC hrV hc' hd'
  have hBe' : (B * e).coeff (K - r) =
      ∑ i ∈ Finset.range (r + 1), B.coeff (D - i) * e.coeff (E - (r - i)) := by
    dsimp only [K]
    exact hBe
  have hcd' : (c * d).coeff (K - r) =
      ∑ i ∈ Finset.range (r + 1),
        c.coeff (Cc - i) * d.coeff (V - (r - i)) := by
    have : Cc + V - r = K - r := by omega
    rw [← this]
    exact hcd
  dsimp only [Fce] at hFK
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hBe', hcd',
    coeff_eq_zero_of_natDegree_lt hB3low,
    coeff_eq_zero_of_natDegree_lt hdLow,
    coeff_eq_zero_of_natDegree_lt hBLow, mul_zero, sub_zero, add_zero] at hFK
  linear_combination hFK

/-! ## Source-backed matching step and induction -/

/-- One matching step for `B`/`c`, given vanishing of `A` through `r`
and matching through `r-1`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_matching_step68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j ≤ r → A.coeff (2 * N - j) = 0)
    (hprev : ∀ j, 1 ≤ j → j < r →
      c.coeff (4 * N - 2 * S) * B.coeff ((3 * N - 2 * S) - j) -
        B.coeff (3 * N - 2 * S) * c.coeff ((4 * N - 2 * S) - j) = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    c.coeff Cc * B.coeff (D - r) - B.coeff D * c.coeff (Cc - r) = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hDconv :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_jet_of_vanishing68
      alpha gamma epsilon zeta eta terminal A B c d e N G S r
      hs hq hr hrD hAvan
  dsimp only at hDconv
  let bj : ℕ → k := fun i => B.coeff (D - i)
  let cj : ℕ → k := fun i => c.coeff (Cc - i)
  have hmatch : ∀ j, 0 < j → j < r → c.coeff Cc * bj j - B.coeff D * cj j = 0 := by
    intro j hj1 hj2
    simpa [bj, cj, D, Cc] using hprev j (Nat.succ_le_of_lt hj1) hj2
  exact fiveToSix_qZero_vanishingA_Bc_jet_succ_algebra68
    (A.coeff p) (B.coeff D) (c.coeff Cc) bj cj ha0 hb0 hD0 r hr rfl rfl
    hmatch (by simpa [bj, cj, p, D, Cc] using hDconv)

/-- One matching step for `e`/`d`, given `B`/`c` matching through `r`
and `e`/`d` incidence through `r-1`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_matching_step68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S r : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hr : 0 < r) (hrD : r ≤ 3 * N - 2 * S)
    (hBc : ∀ j, j ≤ r →
      c.coeff (4 * N - 2 * S) * B.coeff ((3 * N - 2 * S) - j) -
        B.coeff (3 * N - 2 * S) * c.coeff ((4 * N - 2 * S) - j) = 0)
    (hprev : ∀ j, j < r →
      B.coeff (3 * N - 2 * S) * e.coeff ((6 * N - 3 * S) - j) +
        c.coeff (4 * N - 2 * S) * d.coeff ((5 * N - 3 * S) - j) = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    B.coeff D * e.coeff (E - r) + c.coeff Cc * d.coeff (V - r) = 0 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hI4 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_I4_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S r
      hs hq hr hrD
  dsimp only at hI4
  have hI40 :=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).1
  let bj : ℕ → k := fun i => B.coeff (D - i)
  let cj : ℕ → k := fun i => c.coeff (Cc - i)
  let ej : ℕ → k := fun i => e.coeff (E - i)
  let dj : ℕ → k := fun i => d.coeff (V - i)
  have hBc' : ∀ j, j ≤ r → c.coeff Cc * bj j - B.coeff D * cj j = 0 := by
    intro j hj
    simpa [bj, cj, D, Cc] using hBc j hj
  have hEd' : ∀ j, j < r → B.coeff D * ej j + c.coeff Cc * dj j = 0 := by
    intro j hj
    simpa [ej, dj, D, Cc, V, E] using hprev j hj
  exact fiveToSix_qZero_vanishingA_ed_jet_succ_algebra68
    (B.coeff D) (c.coeff Cc) bj cj ej dj hb0 rfl rfl r hr
    (by simpa [D, Cc, V, E, ej, dj] using hI40)
    (by simpa [bj, cj, ej, dj, D, Cc, V, E] using hI4)
    hBc' hEd'

/-- All-orders `B`/`c` matching through a granted vanishing depth `K ≤ D`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_matching_through68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S K : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hK : 0 < K) (hKD : K ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j ≤ K → A.coeff (2 * N - j) = 0) :
    ∀ r, 1 ≤ r → r ≤ K →
      c.coeff (4 * N - 2 * S) * B.coeff ((3 * N - 2 * S) - r) -
        B.coeff (3 * N - 2 * S) * c.coeff ((4 * N - 2 * S) - r) = 0 := by
  intro r hr1 hr2
  have hgoal : ∀ n, n ≤ K → ∀ m, 1 ≤ m → m ≤ n →
      c.coeff (4 * N - 2 * S) * B.coeff ((3 * N - 2 * S) - m) -
        B.coeff (3 * N - 2 * S) * c.coeff ((4 * N - 2 * S) - m) = 0 := by
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
      · have hrpos : 0 < n + 1 := Nat.succ_pos n
        have hrD : n + 1 ≤ 3 * N - 2 * S := by omega
        have hstep :=
          fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_matching_step68
            alpha gamma epsilon zeta eta terminal A B c d e N G S (n + 1)
            hterminal hs hq hrpos hrD
            (fun j hj1 hj2 => hAvan j hj1 (le_trans hj2 (by omega)))
            (fun j hj1 hj2 => ih (by omega) j hj1 (by omega))
        simpa [heq] using hstep
  exact hgoal K le_rfl r hr1 hr2

/-- All-orders `e`/`d` matching through a granted vanishing depth `K ≤ D`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_matching_through68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S K : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hK : 0 < K) (hKD : K ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j ≤ K → A.coeff (2 * N - j) = 0) :
    ∀ r, 1 ≤ r → r ≤ K →
      B.coeff (3 * N - 2 * S) * e.coeff ((6 * N - 3 * S) - r) +
        c.coeff (4 * N - 2 * S) * d.coeff ((5 * N - 3 * S) - r) = 0 := by
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_matching_through68
      alpha gamma epsilon zeta eta terminal A B c d e N G S K
      hterminal hs hq hK hKD hAvan
  intro r hr1 hr2
  have hgoal : ∀ n, n ≤ K → ∀ m, 1 ≤ m → m ≤ n →
      B.coeff (3 * N - 2 * S) * e.coeff ((6 * N - 3 * S) - m) +
        c.coeff (4 * N - 2 * S) * d.coeff ((5 * N - 3 * S) - m) = 0 := by
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
      · have hrpos : 0 < n + 1 := Nat.succ_pos n
        have hrD : n + 1 ≤ 3 * N - 2 * S := by omega
        have hBcAll : ∀ j, j ≤ n + 1 →
            c.coeff (4 * N - 2 * S) * B.coeff ((3 * N - 2 * S) - j) -
              B.coeff (3 * N - 2 * S) * c.coeff ((4 * N - 2 * S) - j) = 0 := by
          intro j hj
          by_cases hj0 : j = 0
          · simp [hj0]
            ring
          · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
            exact hBc j hj1 (le_trans hj (by omega))
        have hstep :=
          fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_matching_step68
            alpha gamma epsilon zeta eta terminal A B c d e N G S (n + 1)
            hterminal hs hq hrpos hrD hBcAll
            (fun j hj => by
              by_cases hj0 : j = 0
              · have hI40 :=
                  (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
                    alpha gamma epsilon zeta eta terminal A B c d e N G S
                    hs hq).1
                simpa [hj0] using hI40
              · have hj1 : 1 ≤ j :=
                  Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
                exact ih (by omega) j hj1 (Nat.lt_succ_iff.mp hj))
        simpa [heq] using hstep
  exact hgoal K le_rfl r hr1 hr2

/-! ## Degree drop from granted vanishing -/

theorem fiveToSix_qZero_Bc_comparison_coeff68
    (B c : k[X]) (N D Cc r : ℕ)
    (hND : N + D = Cc) (hr : r ≤ D) :
    (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c).coeff (Cc - r) =
      c.coeff Cc * B.coeff (D - r) - B.coeff D * c.coeff (Cc - r) := by
  have hidx : Cc - r = N + (D - r) := by omega
  have hL : (C (c.coeff Cc) * X ^ N * B).coeff (Cc - r) =
      c.coeff Cc * B.coeff (D - r) := by
    rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
  simp only [coeff_sub, hL, coeff_C_mul]

theorem fiveToSix_qZero_ed_comparison_coeff68
    (B c d e : k[X]) (N D Cc V E r : ℕ)
    (hNV : N + V = E) (hr : r ≤ V) :
    (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d).coeff (E - r) =
      B.coeff D * e.coeff (E - r) + c.coeff Cc * d.coeff (V - r) := by
  have hidx : E - r = N + (V - r) := by omega
  have hR : (C (c.coeff Cc) * X ^ N * d).coeff (E - r) =
      c.coeff Cc * d.coeff (V - r) := by
    rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
  simp only [coeff_add, coeff_C_mul, hR]

/-- Elimination-count remainder form: vanishing through `K ≤ D` drops
`c_Cc X^N B - B_D c` to degree at most `Cc-K-1`.  This is not
`R_c = 0`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree_of_vanishing68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S K : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hK : 0 < K) (hKD : K ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j ≤ K → A.coeff (2 * N - j) = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c).natDegree ≤ Cc - K - 1 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let R := C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c
  change R.natDegree ≤ Cc - K - 1
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_matching_through68
      alpha gamma epsilon zeta eta terminal A B c d e N G S K
      hterminal hs hq hK hKD hAvan
  have hleR : R.natDegree ≤ Cc := by
    dsimp only [R]; compute_degree; omega
  have hKCc : K + 1 ≤ Cc := by dsimp only [Cc]; omega
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  by_cases hgt : Cc < n
  · exact coeff_eq_zero_of_natDegree_lt (hleR.trans_lt hgt)
  · have hnCc : n ≤ Cc := Nat.not_lt.mp hgt
    have hnK : Cc - K ≤ n := by omega
    have hr : Cc - n ≤ K := by omega
    have hcoeff : R.coeff n = 0 := by
      have hrD : Cc - n ≤ D := by omega
      by_cases hn0 : n = Cc
      · subst n
        have hL : (C (c.coeff Cc) * X ^ N * B).coeff Cc =
            c.coeff Cc * B.coeff D := by
          have hidx : Cc = N + D := by omega
          rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
        dsimp only [R]
        rw [coeff_sub, hL, coeff_C_mul]
        ring
      · have hr1 : 1 ≤ Cc - n := by omega
        have hmatch := hBc (Cc - n) hr1 hr
        have hC := fiveToSix_qZero_Bc_comparison_coeff68 B c N D Cc (Cc - n)
          (by omega) hrD
        have hn' : Cc - (Cc - n) = n := by omega
        dsimp only [R] at hC ⊢
        rw [hn'] at hC
        rw [hC]
        dsimp only [D, Cc] at hmatch ⊢
        have hnCc : 4 * N - 2 * S - (4 * N - 2 * S - n) = n := by omega
        simpa [hnCc] using hmatch
    exact hcoeff

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree_of_vanishing68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S K : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hK : 0 < K) (hKD : K ≤ 3 * N - 2 * S)
    (hAvan : ∀ j, 1 ≤ j → j ≤ K → A.coeff (2 * N - j) = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d).natDegree ≤ E - K - 1 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let R := C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d
  change R.natDegree ≤ E - K - 1
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hEd :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_matching_through68
      alpha gamma epsilon zeta eta terminal A B c d e N G S K
      hterminal hs hq hK hKD hAvan
  have hI40 :=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).1
  have hleR : R.natDegree ≤ E := by
    dsimp only [R]; compute_degree; omega
  have hKE : K + 1 ≤ E := by dsimp only [E]; omega
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  by_cases hgt : E < n
  · exact coeff_eq_zero_of_natDegree_lt (hleR.trans_lt hgt)
  · have hnE : n ≤ E := Nat.not_lt.mp hgt
    have hcoeff : R.coeff n = 0 := by
      have hrV : E - n ≤ V := by omega
      by_cases hn0 : n = E
      · subst n
        have hR : (C (c.coeff Cc) * X ^ N * d).coeff E =
            c.coeff Cc * d.coeff V := by
          have hidx : E = N + V := by omega
          rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
        dsimp only [R]
        rw [coeff_add, coeff_C_mul, hR]
        dsimp only [D, Cc, V, E] at hI40 ⊢
        linear_combination hI40
      · have hr1 : 1 ≤ E - n := by omega
        have hrK : E - n ≤ K := by omega
        have hmatch := hEd (E - n) hr1 hrK
        have hC := fiveToSix_qZero_ed_comparison_coeff68 B c d e N D Cc V E
          (E - n) (by omega) hrV
        have hn' : E - (E - n) = n := by omega
        dsimp only [R] at hC ⊢
        rw [hn'] at hC
        rw [hC]
        dsimp only [D, Cc, V, E] at hmatch ⊢
        have hnE : 6 * N - 3 * S - (6 * N - 3 * S - n) = n := by omega
        simpa [hnE] using hmatch
    exact hcoeff

/-- Conditional proportionality through `k=D`: the comparison polynomials
drop to degree at most `N-1` and `E-D-1`.  Not the identity
`c_Cc X^N B = B_D c`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_proportionality_of_vanishing_through_D68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hAvan : ∀ j, 1 ≤ j → j ≤ 3 * N - 2 * S → A.coeff (2 * N - j) = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let E := 6 * N - 3 * S
    (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c).natDegree ≤ N - 1 ∧
      (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d).natDegree ≤ E - D - 1 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let E := 6 * N - 3 * S
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  have hDpos : 0 < D := hwall.2.1
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree_of_vanishing68
      alpha gamma epsilon zeta eta terminal A B c d e N G S D
      hterminal hs hq hDpos le_rfl hAvan
  have hEd :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree_of_vanishing68
      alpha gamma epsilon zeta eta terminal A B c d e N G S D
      hterminal hs hq hDpos le_rfl hAvan
  dsimp only [D, Cc, E] at hBc hEd ⊢
  have hCcD : 4 * N - 2 * S - (3 * N - 2 * S) - 1 = N - 1 := by omega
  exact ⟨by simpa [hCcD] using hBc, hEd⟩

/-! ## Zero-remainder comparison (does not fire on the landed residual) -/

/-- Ring form: identical matching writes `Be+cd` as zero, so `Fce` is a
cubic in `B` plus linear terms in `d` and `B`. -/
theorem fiveToSix_qZero_vanishingA_zero_remainder_Fce_algebra68
    (gamma epsilon : k) (B c d e : k[X]) (N D Cc : ℕ)
    (hb : B.coeff D ≠ 0)
    (hc : C (c.coeff Cc) * X ^ N * B = C (B.coeff D) * c)
    (he : C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d = 0) :
    B * e + c * d = 0 := by
  have hCne : C (B.coeff D) ≠ 0 := by
    intro hC
    exact hb (C_eq_zero.mp hC)
  have hmul : C (B.coeff D) * (B * e + c * d) = 0 := by
    calc
      C (B.coeff D) * (B * e + c * d) =
          B * (C (B.coeff D) * e) + C (B.coeff D) * c * d := by ring
      _ = B * (-(C (c.coeff Cc) * X ^ N * d)) +
            (C (c.coeff Cc) * X ^ N * B) * d := by
        have he' : C (B.coeff D) * e = -(C (c.coeff Cc) * X ^ N * d) := by
          linear_combination he
        rw [he', hc]
      _ = 0 := by ring
  exact (mul_eq_zero.mp hmul).resolve_left hCne

/-- If the comparison polynomials vanished identically, the leading
coefficient `-(1/9) B_D^3` of `Fce` at degree `3D` would be a nonzero
constant.  This is the terminal-style comparison of `(*)`.  It does not
apply to the landed residual: matching through `k=D` leaves
`deg r_c ≤ N-1`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_zero_remainder_impossible68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hBc0 : C (c.coeff (4 * N - 2 * S)) * X ^ N * B -
      C (B.coeff (3 * N - 2 * S)) * c = 0)
    (hEd0 : C (B.coeff (3 * N - 2 * S)) * e +
      C (c.coeff (4 * N - 2 * S)) * X ^ N * d = 0) :
    False := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hBe :
      B * e + c * d = 0 :=
    fiveToSix_qZero_vanishingA_zero_remainder_Fce_algebra68
      gamma epsilon B c d e N D Cc hb0
      (sub_eq_zero.mp (by simpa [D, Cc] using hBc0))
      (by simpa [D, Cc] using hEd0)
  have hFconst :
      Fce = C (Fce.coeff 0) :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hBdeg : B.natDegree = D :=
    natDegree_eq_of_le_of_coeff_ne_zero hB' hb0
  have hB3top : (B ^ 3).coeff (3 * D) = B.coeff D ^ 3 :=
    coeff_pow_of_natDegree_le (by simpa [hBdeg] using hB')
  have h3Dpos : 0 < 3 * D := by omega
  have hdLow : d.natDegree < 3 * D := by
    dsimp only [D, V] at hd' ⊢; omega
  have hBLow : B.natDegree < 3 * D := by
    rw [hBdeg]; omega
  have hlead : Fce.coeff (3 * D) = -((1 / 9 : k) * B.coeff D ^ 3) := by
    dsimp only [Fce]
    rw [hBe]
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, coeff_zero]
    have hd0 : d.coeff (3 * D) = 0 :=
      coeff_eq_zero_of_natDegree_lt hdLow
    have hB0 : B.coeff (3 * D) = 0 :=
      coeff_eq_zero_of_natDegree_lt hBLow
    rw [hd0, hB0, hB3top]
    ring
  have hC : Fce.coeff (3 * D) = 0 := by
    rw [hFconst, coeff_C]
    split_ifs with h
    · omega
    · rfl
  have hb03 : B.coeff D ^ 3 ≠ 0 := pow_ne_zero 3 hb0
  have hne : -((1 / 9 : k) * B.coeff D ^ 3) ≠ 0 := by
    intro hz
    have : (1 / 9 : k) * B.coeff D ^ 3 = 0 := by linear_combination -hz
    have h9 : (1 / 9 : k) ≠ 0 := by norm_num
    exact hb03 ((mul_eq_zero.mp this).resolve_left h9)
  exact hne (hlead.symm.trans hC)

/-! ## Landed producing depth, and the named producing gap -/

/-- The producing companion split is landed through `k=4`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_through_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    ∀ j, 1 ≤ j → j ≤ 4 → A.coeff (2 * N - j) = 0 := by
  intro j hj1 hj2
  have hA :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hA
  have : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with h | h | h | h
  · simpa [h] using hA.2.1
  · simpa [h] using hA.2.2.1
  · simpa [h] using hA.2.2.2.1
  · simpa [h] using hA.2.2.2.2

/-- On the chart `D ≤ 4` (equivalently `m=1` on this wall), producing
already covers `k=D`, so matching through `D` is landed.  Remainders
still have degree up to `N-1`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_through_D_of_D_le_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hD4 : 3 * N - 2 * S ≤ 4) :
    (∀ j, 1 ≤ j → j ≤ 3 * N - 2 * S → A.coeff (2 * N - j) = 0) ∧
      (C (c.coeff (4 * N - 2 * S)) * X ^ N * B -
          C (B.coeff (3 * N - 2 * S)) * c).natDegree ≤ N - 1 ∧
      (C (B.coeff (3 * N - 2 * S)) * e +
          C (c.coeff (4 * N - 2 * S)) * X ^ N * d).natDegree ≤
        (6 * N - 3 * S) - (3 * N - 2 * S) - 1 := by
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  have hDpos : 0 < 3 * N - 2 * S := hwall.2.1
  have hAvan : ∀ j, 1 ≤ j → j ≤ 3 * N - 2 * S → A.coeff (2 * N - j) = 0 := by
    intro j hj1 hj2
    exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_through_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq j hj1 (le_trans hj2 hD4)
  have hprop :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_proportionality_of_vanishing_through_D68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hAvan
  dsimp only at hprop
  exact ⟨hAvan, hprop⟩

/-! ## Residual packet

Residual after the uniform matching induction.  The producing companion
is landed through `k=4`; matching is a theorem of any granted vanishing
depth `K ≤ D`.  The order-`k` remainder-cancel and load certificate
needed to *produce* vanishing `A` at `k ≥ 5` are not named.  Disc and
I4 jets at those orders are uniform (theorems above).  Not a closure:
`r_c=r_e=0` is the extra hypothesis of
`..._zero_remainder_impossible68`, not an output of matching through
`k=D`.  Next unused source coefficient: `A_(2N-5)`. -/
def FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAUniformCompanionResidual68
    (gamma epsilon : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAOrder4CompanionResidual68
    gamma epsilon A B c d e N S

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_uniform_companion68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAUniformCompanionResidual68
      gamma epsilon A B c d e N S :=
  fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_order4_companion68
    alpha gamma epsilon zeta eta terminal A B c d e N G S
    hterminal hs hq

#print axioms coeff_mul_sub_bounds68
#print axioms fiveToSix_qZero_vanishingA_Bc_jet_succ_algebra68
#print axioms fiveToSix_qZero_vanishingA_ed_jet_succ_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_jet68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_I4_jet68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_matching_through68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_matching_through68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_proportionality_of_vanishing_through_D68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_zero_remainder_impossible68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_through_four68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_uniform_companion68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAUniformCompanion68

end Max11DegreeRoutes
