import Grok68VanishingAChargedIntegralScratch

/-! # Order-four companion on the `q=0` vanishing-A chamber

Both research lanes (`xmodel/max11-68-vanishing-a-elimination-count` and
the identity hunt) record that matching through `k=3` leaves an open
chamber of expected dimension `19m+4`.  The next producing input is the
order-four companion, together with its remainder-cancel and load
certificate.

This file lands that producing split: on `Fce_0≠0` one has
`A_(2N-4)=0`.  The matching recurrence at `k=4` then gives
`c_Cc B_(D-4)^♭ - B_D c_(Cc-4)=0` and the companion `e/d` incidence,
so the comparison polynomials drop one further degree.

Here `B_(D-4)^♭` is `B.coeff (D-4)` when `4≤D`, and `0` when `D=3`
(the chart `m=1`, where the index `D-4` is not a natural number).
This is not a closure.  The next unused source row is `A_(2N-5)`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Coefficient helpers -/

/-- Four coefficients below a product of two separate bounds. -/
theorem coeff_mul_four_below_bounds68 (f g : k[X]) (u v : ℕ)
    (hu : 4 ≤ u) (hv : 4 ≤ v) (hf : f.natDegree ≤ u) (hg : g.natDegree ≤ v) :
    (f * g).coeff (u + v - 4) =
      f.coeff (u - 4) * g.coeff v + f.coeff (u - 3) * g.coeff (v - 1) +
        f.coeff (u - 2) * g.coeff (v - 2) + f.coeff (u - 1) * g.coeff (v - 3) +
        f.coeff u * g.coeff (v - 4) := by
  have hmem0 : u - 4 ∈ Finset.range (u + v - 4 + 1) :=
    Finset.mem_range.mpr (by omega)
  have hmem1 : u - 3 ∈ (Finset.range (u + v - 4 + 1)).erase (u - 4) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have hmem2 : u - 2 ∈
      ((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3) :=
    Finset.mem_erase.mpr ⟨by omega,
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩
  have hmem3 : u - 1 ∈
      (((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3)).erase
        (u - 2) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩⟩
  have hmem4 : u ∈
      ((((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3)).erase
        (u - 2)).erase (u - 1) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
        Finset.mem_range.mpr (by omega)⟩⟩⟩⟩
  have hzero : ∀ i ∈ (((((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase
        (u - 3)).erase (u - 2)).erase (u - 1)).erase u,
      f.coeff i * g.coeff (u + v - 4 - i) = 0 := by
    intro i hi
    have hi0 := Finset.mem_erase.mp hi
    have hi1 := Finset.mem_erase.mp hi0.2
    have hi2 := Finset.mem_erase.mp hi1.2
    have hi3 := Finset.mem_erase.mp hi2.2
    have hi4 := Finset.mem_erase.mp hi3.2
    by_cases hgt : u < i
    · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt hgt), zero_mul]
    · have : i < u - 4 := by omega
      rw [coeff_eq_zero_of_natDegree_lt (hg.trans_lt (by omega)), mul_zero]
  have hsum : (f * g).coeff (u + v - 4) =
      ∑ i ∈ Finset.range (u + v - 4 + 1), f.coeff i * g.coeff (u + v - 4 - i) := by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have h0 := Finset.add_sum_erase (Finset.range (u + v - 4 + 1))
    (fun i => f.coeff i * g.coeff (u + v - 4 - i)) hmem0
  have h1 := Finset.add_sum_erase ((Finset.range (u + v - 4 + 1)).erase (u - 4))
    (fun i => f.coeff i * g.coeff (u + v - 4 - i)) hmem1
  have h2 := Finset.add_sum_erase
    (((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3))
    (fun i => f.coeff i * g.coeff (u + v - 4 - i)) hmem2
  have h3 := Finset.add_sum_erase
    ((((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3)).erase (u - 2))
    (fun i => f.coeff i * g.coeff (u + v - 4 - i)) hmem3
  have h4 := Finset.add_sum_erase
    (((((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3)).erase
      (u - 2)).erase (u - 1))
    (fun i => f.coeff i * g.coeff (u + v - 4 - i)) hmem4
  have h5 : ∑ i ∈ (((((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase
        (u - 3)).erase (u - 2)).erase (u - 1)).erase u,
      f.coeff i * g.coeff (u + v - 4 - i) = 0 :=
    Finset.sum_eq_zero hzero
  rw [hsum, ← h0, ← h1, ← h2, ← h3, ← h4, h5, add_zero]
  rw [show u + v - 4 - (u - 4) = v by omega,
    show u + v - 4 - (u - 3) = v - 1 by omega,
    show u + v - 4 - (u - 2) = v - 2 by omega,
    show u + v - 4 - (u - 1) = v - 3 by omega,
    show u + v - 4 - u = v - 4 by omega]
  ring

/-- Degree-two coefficient of a product of two cubics. -/
theorem coeff_mul_at_two_of_degree_le_three68 (f g : k[X])
    (hf : f.natDegree ≤ 3) (hg : g.natDegree ≤ 3) :
    (f * g).coeff 2 =
      f.coeff 0 * g.coeff 2 + f.coeff 1 * g.coeff 1 + f.coeff 2 * g.coeff 0 := by
  have hmem0 : 0 ∈ Finset.range (2 + 1) := by simp
  have hmem1 : 1 ∈ (Finset.range (2 + 1)).erase 0 := by simp
  have hmem2 : 2 ∈ ((Finset.range (2 + 1)).erase 0).erase 1 := by simp
  have hzero : ∀ i ∈ (((Finset.range (2 + 1)).erase 0).erase 1).erase 2,
      f.coeff i * g.coeff (2 - i) = 0 := by
    intro i hi
    have hi0 := Finset.mem_erase.mp hi
    have hi1 := Finset.mem_erase.mp hi0.2
    have hi2 := Finset.mem_erase.mp hi1.2
    have : i ∈ Finset.range 3 := hi2.2
    have : i < 3 := Finset.mem_range.mp this
    omega
  have hsum : (f * g).coeff 2 =
      ∑ i ∈ Finset.range (2 + 1), f.coeff i * g.coeff (2 - i) := by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have h0 := Finset.add_sum_erase (Finset.range (2 + 1))
    (fun i => f.coeff i * g.coeff (2 - i)) hmem0
  have h1 := Finset.add_sum_erase ((Finset.range (2 + 1)).erase 0)
    (fun i => f.coeff i * g.coeff (2 - i)) hmem1
  have h2 := Finset.add_sum_erase (((Finset.range (2 + 1)).erase 0).erase 1)
    (fun i => f.coeff i * g.coeff (2 - i)) hmem2
  have h3 : ∑ i ∈ (((Finset.range (2 + 1)).erase 0).erase 1).erase 2,
      f.coeff i * g.coeff (2 - i) = 0 := Finset.sum_eq_zero hzero
  rw [hsum, ← h0, ← h1, ← h2, h3, add_zero]
  ring

/-- Square coefficient four below `2v`, allowing the short chart `v=3`. -/
theorem coeff_sq_sub_four68 (q : k[X]) (v : ℕ)
    (hv : 3 ≤ v) (hq : q.natDegree ≤ v) :
    (q ^ 2).coeff (2 * v - 4) =
      (2 : k) * q.coeff v * (if 4 ≤ v then q.coeff (v - 4) else 0) +
        (2 : k) * q.coeff (v - 1) * q.coeff (v - 3) + q.coeff (v - 2) ^ 2 := by
  by_cases h4 : 4 ≤ v
  · have h := coeff_mul_four_below_bounds68 q q v v h4 h4 hq hq
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢
    rw [if_pos h4]
    linear_combination h
  · have hv3 : v = 3 := by omega
    subst v
    have h := coeff_mul_at_two_of_degree_le_three68 q q
      (by simpa using hq) (by simpa using hq)
    simp only [pow_two] at h ⊢
    rw [if_neg (by norm_num : ¬ 4 ≤ 3)]
    linear_combination h

/-- Four coefficients below a product of three separate bounds. -/
theorem coeff_mul_mul_four_below_bounds68 (p q r : k[X]) (u v w : ℕ)
    (hu : 4 ≤ u) (hv : 4 ≤ v) (hw : 4 ≤ w)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) (hr : r.natDegree ≤ w) :
    (p * q * r).coeff (u + v + w - 4) =
      p.coeff (u - 4) * q.coeff v * r.coeff w +
        p.coeff (u - 3) * q.coeff (v - 1) * r.coeff w +
        p.coeff (u - 2) * q.coeff (v - 2) * r.coeff w +
        p.coeff (u - 1) * q.coeff (v - 3) * r.coeff w +
        p.coeff u * q.coeff (v - 4) * r.coeff w +
        p.coeff (u - 3) * q.coeff v * r.coeff (w - 1) +
        p.coeff (u - 2) * q.coeff (v - 1) * r.coeff (w - 1) +
        p.coeff (u - 1) * q.coeff (v - 2) * r.coeff (w - 1) +
        p.coeff u * q.coeff (v - 3) * r.coeff (w - 1) +
        p.coeff (u - 2) * q.coeff v * r.coeff (w - 2) +
        p.coeff (u - 1) * q.coeff (v - 1) * r.coeff (w - 2) +
        p.coeff u * q.coeff (v - 2) * r.coeff (w - 2) +
        p.coeff (u - 1) * q.coeff v * r.coeff (w - 3) +
        p.coeff u * q.coeff (v - 1) * r.coeff (w - 3) +
        p.coeff u * q.coeff v * r.coeff (w - 4) := by
  have hpq : (p * q).natDegree ≤ u + v := by compute_degree; omega
  rw [coeff_mul_four_below_bounds68 (p * q) r (u + v) w (by omega) hw hpq hr,
    coeff_mul_four_below_bounds68 p q u v hu hv hp hq,
    coeff_mul_three_below_bounds68 p q u v (by omega) (by omega) hp hq,
    coeff_mul_two_below_bounds68 p q u v (by omega) (by omega) hp hq,
    coeff_mul_one_below_bounds68 p q u v (by omega) (by omega) hp hq,
    coeff_mul_at_bounds68 p q u v hp hq]
  ring

/-- Left factor of degree at least three, right factor of degree at least four. -/
theorem coeff_mul_sub_four_left_ge_three68 (f g : k[X]) (u v : ℕ)
    (hu : 3 ≤ u) (hv : 4 ≤ v) (hf : f.natDegree ≤ u) (hg : g.natDegree ≤ v) :
    (f * g).coeff (u + v - 4) =
      (if 4 ≤ u then f.coeff (u - 4) * g.coeff v else 0) +
        f.coeff (u - 3) * g.coeff (v - 1) +
        f.coeff (u - 2) * g.coeff (v - 2) +
        f.coeff (u - 1) * g.coeff (v - 3) +
        f.coeff u * g.coeff (v - 4) := by
  by_cases h4 : 4 ≤ u
  · rw [if_pos h4]
    exact coeff_mul_four_below_bounds68 f g u v h4 hv hf hg
  · have hu3 : u = 3 := by omega
    subst u
    rw [if_neg (by norm_num : ¬ 4 ≤ 3)]
    -- `u+v-4 = v-1`.  Expand the antidiagonal of length four.
    have hmem0 : 0 ∈ Finset.range (v - 1 + 1) :=
      Finset.mem_range.mpr (by omega)
    have hmem1 : 1 ∈ (Finset.range (v - 1 + 1)).erase 0 :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
    have hmem2 : 2 ∈ ((Finset.range (v - 1 + 1)).erase 0).erase 1 :=
      Finset.mem_erase.mpr ⟨by omega,
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩
    have hmem3 : 3 ∈ (((Finset.range (v - 1 + 1)).erase 0).erase 1).erase 2 :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩⟩
    have hzero : ∀ i ∈ ((((Finset.range (v - 1 + 1)).erase 0).erase 1).erase
          2).erase 3,
        f.coeff i * g.coeff (v - 1 - i) = 0 := by
      intro i hi
      have hi0 := Finset.mem_erase.mp hi
      have hi1 := Finset.mem_erase.mp hi0.2
      have hi2 := Finset.mem_erase.mp hi1.2
      have hi3 := Finset.mem_erase.mp hi2.2
      by_cases hgt : 3 < i
      · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt (by omega)), zero_mul]
      · omega
    have hsum : (f * g).coeff (v - 1) =
        ∑ i ∈ Finset.range (v - 1 + 1), f.coeff i * g.coeff (v - 1 - i) := by
      rw [coeff_mul]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
    have h0 := Finset.add_sum_erase (Finset.range (v - 1 + 1))
      (fun i => f.coeff i * g.coeff (v - 1 - i)) hmem0
    have h1 := Finset.add_sum_erase ((Finset.range (v - 1 + 1)).erase 0)
      (fun i => f.coeff i * g.coeff (v - 1 - i)) hmem1
    have h2 := Finset.add_sum_erase
      (((Finset.range (v - 1 + 1)).erase 0).erase 1)
      (fun i => f.coeff i * g.coeff (v - 1 - i)) hmem2
    have h3 := Finset.add_sum_erase
      ((((Finset.range (v - 1 + 1)).erase 0).erase 1).erase 2)
      (fun i => f.coeff i * g.coeff (v - 1 - i)) hmem3
    have h4 : ∑ i ∈ ((((Finset.range (v - 1 + 1)).erase 0).erase 1).erase
          2).erase 3,
        f.coeff i * g.coeff (v - 1 - i) = 0 := Finset.sum_eq_zero hzero
    have hidx : 3 + v - 4 = v - 1 := by omega
    rw [hidx, hsum, ← h0, ← h1, ← h2, ← h3, h4, add_zero]
    rw [show v - 1 - 0 = v - 1 by omega, show v - 1 - 1 = v - 2 by omega,
      show v - 1 - 2 = v - 3 by omega, show v - 1 - 3 = v - 4 by omega]
    ring

/-! ## Order-four discriminant and I4 jets -/

/-- The exact fourth reflected-discriminant jet.  The `B` index `D-4` is
replaced by zero on the chart `D=3`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_fourth68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    A.coeff (p - 4) * B.coeff D ^ 2 +
      (2 : k) * A.coeff (p - 3) * B.coeff D * B.coeff (D - 1) +
      A.coeff (p - 2) * ((2 : k) * B.coeff D * B.coeff (D - 2) +
        B.coeff (D - 1) ^ 2) +
      A.coeff (p - 1) * ((2 : k) * B.coeff D * B.coeff (D - 3) +
        (2 : k) * B.coeff (D - 1) * B.coeff (D - 2)) +
      A.coeff p * ((2 : k) * B.coeff D *
          (if 4 ≤ D then B.coeff (D - 4) else 0) +
        (2 : k) * B.coeff (D - 1) * B.coeff (D - 3) + B.coeff (D - 2) ^ 2) +
      (6 : k) * (c.coeff Cc * c.coeff (Cc - 4) +
        c.coeff (Cc - 1) * c.coeff (Cc - 3)) +
      (3 : k) * c.coeff (Cc - 2) ^ 2 = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let U := 8 * N - 2 * G
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  change _ = 0
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
  rcases hrest with ⟨hless, hmu, hzeta, hzero, hDeltaDeg⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hA' : A.natDegree ≤ p := by simpa [p] using hA
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
  have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hc
  have hp4 : 4 ≤ p := by dsimp only [p]; omega
  have hD3 : 3 ≤ D := by dsimp only [D]; omega
  have hC4 : 4 ≤ Cc := by dsimp only [Cc]; omega
  have h2D4 : 4 ≤ 2 * D := by omega
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by compute_degree; omega
  have hFour : 4 ≤ min S (7 * N - 2 * G - S) := by omega
  have href : (Delta.reflect U).coeff 4 = 0 := by
    dsimp only [Delta, U]
    exact hzero 4 hFour
  have hDelta : Delta.coeff (U - 4) = 0 := by
    rw [coeff_reflect, revAt_le (by dsimp only [U]; omega)] at href
    exact href
  have hABB0 := coeff_mul_four_below_bounds68 A (B ^ 2) p (2 * D)
    hp4 h2D4 hA' hB2deg
  have hB20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
    have h := coeff_mul_at_bounds68 B B D D hB' hB'
    rw [← two_mul] at h
    simpa [pow_two] using h
  have hB21 : (B ^ 2).coeff (2 * D - 1) =
      (2 : k) * B.coeff D * B.coeff (D - 1) := by
    have h := coeff_mul_one_below_bounds68 B B D D (by omega) (by omega) hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢
    linear_combination h
  have hB22 : (B ^ 2).coeff (2 * D - 2) =
      (2 : k) * B.coeff D * B.coeff (D - 2) + B.coeff (D - 1) ^ 2 := by
    have h := coeff_mul_two_below_bounds68 B B D D (by omega) (by omega) hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢
    linear_combination h
  have hB23 : (B ^ 2).coeff (2 * D - 3) =
      (2 : k) * B.coeff D * B.coeff (D - 3) +
        (2 : k) * B.coeff (D - 1) * B.coeff (D - 2) := by
    have h := coeff_mul_three_below_bounds68 B B D D hD3 hD3 hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢
    linear_combination h
  have hB24 : (B ^ 2).coeff (2 * D - 4) =
      (2 : k) * B.coeff D * (if 4 ≤ D then B.coeff (D - 4) else 0) +
        (2 : k) * B.coeff (D - 1) * B.coeff (D - 3) + B.coeff (D - 2) ^ 2 :=
    coeff_sq_sub_four68 B D hD3 hB'
  have hABB : (A * B ^ 2).coeff (U - 4) =
      A.coeff (p - 4) * B.coeff D ^ 2 +
        (2 : k) * A.coeff (p - 3) * B.coeff D * B.coeff (D - 1) +
        A.coeff (p - 2) * ((2 : k) * B.coeff D * B.coeff (D - 2) +
          B.coeff (D - 1) ^ 2) +
        A.coeff (p - 1) * ((2 : k) * B.coeff D * B.coeff (D - 3) +
          (2 : k) * B.coeff (D - 1) * B.coeff (D - 2)) +
        A.coeff p * ((2 : k) * B.coeff D *
            (if 4 ≤ D then B.coeff (D - 4) else 0) +
          (2 : k) * B.coeff (D - 1) * B.coeff (D - 3) +
          B.coeff (D - 2) ^ 2) := by
    have hU : p + 2 * D = U := by dsimp only [p, D, U]; rw [hGS]; omega
    have hidx : p + 2 * D - 4 = U - 4 := by omega
    rw [← hidx, hABB0, show 2 * D - 1 = 2 * D - 1 by rfl,
      show p - 1 = p - 1 by rfl]
    rw [show p - 4 = p - 4 by rfl, hB20,
      show 2 * D - 1 = 2 * D - 1 by rfl, hB21, hB22, hB23, hB24]
    ring
  have hcc0 := coeff_mul_four_below_bounds68 c c Cc Cc hC4 hC4 hc' hc'
  have hcc : (c ^ 2).coeff (U - 4) =
      (2 : k) * (c.coeff Cc * c.coeff (Cc - 4) +
        c.coeff (Cc - 1) * c.coeff (Cc - 3)) + c.coeff (Cc - 2) ^ 2 := by
    have hU : Cc + Cc = U := by dsimp only [Cc, U]; rw [hGS]; omega
    rw [show Cc + Cc - 4 = U - 4 by omega] at hcc0
    simp only [pow_two] at hcc0 ⊢
    linear_combination hcc0
  dsimp only [Delta, fiveToSixCuspDiscriminantPolynomial68] at hDelta
  simp only [coeff_add, coeff_smul, smul_eq_mul, hABB, hcc] at hDelta
  linear_combination hDelta

/-- The exact fourth coefficient of the compensated `I4` product. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_I4_fourth68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    (if 4 ≤ D then B.coeff (D - 4) * e.coeff E else 0) +
      B.coeff (D - 3) * e.coeff (E - 1) + B.coeff (D - 2) * e.coeff (E - 2) +
      B.coeff (D - 1) * e.coeff (E - 3) + B.coeff D * e.coeff (E - 4) +
      c.coeff (Cc - 4) * d.coeff V + c.coeff (Cc - 3) * d.coeff (V - 1) +
      c.coeff (Cc - 2) * d.coeff (V - 2) + c.coeff (Cc - 1) * d.coeff (V - 3) +
      c.coeff Cc * d.coeff (V - 4) = 0 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let K := D + E
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d +
    (3 / 4 * epsilon : k) • B
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  rcases hnxt.2.1 with ⟨i4, i3, hFce, hRce, hRceDeg⟩
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, he, hpacket, hrest⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
  have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hc
  have hd' : d.natDegree ≤ V := by dsimp only [V]; rw [hGS] at hd; omega
  have he' : e.natDegree ≤ E := by dsimp only [E]; rw [hGS] at he; omega
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hD3 : 3 ≤ D := by dsimp only [D]; omega
  have hC4 : 4 ≤ Cc := by dsimp only [Cc]; omega
  have hV4 : 4 ≤ V := by dsimp only [V]; omega
  have hE4 : 4 ≤ E := by dsimp only [E]; omega
  have hB3low : (B ^ 3).natDegree < K - 4 := by
    have : (B ^ 3).natDegree ≤ 3 * D := by compute_degree; omega
    dsimp only [D, E, K] at *; omega
  have hdLow : d.natDegree < K - 4 := by dsimp only [D, E, K, V] at *; omega
  have hBLow : B.natDegree < K - 4 := by dsimp only [D, E, K] at *; omega
  have hBe := coeff_mul_sub_four_left_ge_three68 B e D E hD3 hE4 hB' he'
  have hcd0 := coeff_mul_four_below_bounds68 c d Cc V hC4 hV4 hc' hd'
  have hcd : (c * d).coeff (K - 4) =
      c.coeff (Cc - 4) * d.coeff V + c.coeff (Cc - 3) * d.coeff (V - 1) +
        c.coeff (Cc - 2) * d.coeff (V - 2) + c.coeff (Cc - 1) * d.coeff (V - 3) +
        c.coeff Cc * d.coeff (V - 4) := by
    rw [show Cc + V = K by dsimp only [D, Cc, V, E, K]; omega] at hcd0
    exact hcd0
  have hFK : Fce.coeff (K - 4) = 0 := by
    dsimp only [Fce]
    rw [hFce, coeff_smul, coeff_C]
    split_ifs with h
    · omega
    · simp only [smul_zero]
  dsimp only [Fce] at hFK
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hcd,
    coeff_eq_zero_of_natDegree_lt hB3low,
    coeff_eq_zero_of_natDegree_lt hdLow,
    coeff_eq_zero_of_natDegree_lt hBLow, mul_zero, sub_zero, add_zero] at hFK
  have hBe' : (B * e).coeff (K - 4) =
      (if 4 ≤ D then B.coeff (D - 4) * e.coeff E else 0) +
        B.coeff (D - 3) * e.coeff (E - 1) + B.coeff (D - 2) * e.coeff (E - 2) +
        B.coeff (D - 1) * e.coeff (E - 3) + B.coeff D * e.coeff (E - 4) := by
    simpa [K] using hBe
  rw [hBe'] at hFK
  convert hFK using 1
  ring

/-! ## Order-four companion -/

def FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionFourthScalar68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let p := 2 * N
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d +
    (3 / 4 * epsilon : k) • B
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  (9 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) ^ 2 *
      ((p - 1 : ℕ) : k) * Fce.coeff 0 *
      ((2 : k) * A.coeff p * A.coeff (p - 4) +
        (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) + A.coeff (p - 2) ^ 2) +
    (6 : k) * ((p - 4 : ℕ) : k) ^ 2 * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
      ((p - 1 : ℕ) : k) * A.coeff (p - 4) * B.coeff D ^ 2 * d.coeff V +
    (6 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
      ((p - 1 : ℕ) : k) * (L0.coeff (2 * p - 5) + W0.coeff (2 * p - 5)) +
    ((p : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) *
      A.coeff p * (L2.coeff (p - 5) + W2.coeff (p - 5)) +
    ((p - 4 : ℕ) : k) * ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) ^ 2 *
      A.coeff (p - 1) * (L2.coeff (p - 4) + W2.coeff (p - 4)) +
    ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
      ((p - 1 : ℕ) : k) * A.coeff (p - 2) *
      (L2.coeff (p - 3) + W2.coeff (p - 3)) +
    ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) ^ 2 * ((p - 2 : ℕ) : k) *
      A.coeff (p - 3) * (L2.coeff (p - 2) + W2.coeff (p - 2)) = 0

/-- Exact division-free elimination of `J_(p-4)` and all higher `J` jets. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionFourthScalar68
      alpha gamma epsilon zeta eta A B c d e N S := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let i0 := 2 * p - 5
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) + (3 / 2 * gamma : k) • d +
    (3 / 4 * epsilon : k) • B
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  rcases hnxt with ⟨harith, hexact, hrow2old, hp1cast⟩
  rcases hexact with ⟨i4, i3, hFce, hRce, hRceDeg⟩
  have hEq : 9 * N = 7 * S := harith.1
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
  have hA' : A.natDegree ≤ p := by simpa [p] using hA
  have hdA : (derivative A).natDegree ≤ p - 1 := by
    have h := natDegree_derivative_le A
    dsimp only [p]; omega
  have hJ : J.natDegree ≤ p := by
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
  have hp4 : 4 ≤ p := by dsimp only [p]; omega
  have hpm1 : 4 ≤ p - 1 := by dsimp only [p]; omega
  have hAAraw := coeff_mul_four_below_bounds68 A (derivative A) p (p - 1)
    hp4 hpm1 hA' hdA
  rw [show p + (p - 1) - 4 = i0 by dsimp only [i0]; omega] at hAAraw
  have hdA0 : (derivative A).coeff (p - 1) = A.coeff p * ((p : ℕ) : k) := by
    rw [coeff_derivative, show p - 1 + 1 = p by omega]
    congr 1
    exact_mod_cast (show p - 1 + 1 = p by omega)
  have hdA1 : (derivative A).coeff (p - 2) =
      A.coeff (p - 1) * ((p - 1 : ℕ) : k) := by
    rw [coeff_derivative, show p - 2 + 1 = p - 1 by omega]
    congr 1
    exact_mod_cast (show p - 2 + 1 = p - 1 by omega)
  have hdA2 : (derivative A).coeff (p - 3) =
      A.coeff (p - 2) * ((p - 2 : ℕ) : k) := by
    rw [coeff_derivative, show p - 3 + 1 = p - 2 by omega]
    congr 1
    exact_mod_cast (show p - 3 + 1 = p - 2 by omega)
  have hdA3 : (derivative A).coeff (p - 4) =
      A.coeff (p - 3) * ((p - 3 : ℕ) : k) := by
    rw [coeff_derivative, show p - 4 + 1 = p - 3 by omega]
    congr 1
    exact_mod_cast (show p - 4 + 1 = p - 3 by omega)
  have hdA4 : (derivative A).coeff (p - 5) =
      A.coeff (p - 4) * ((p - 4 : ℕ) : k) := by
    rw [coeff_derivative, show p - 5 + 1 = p - 4 by omega]
    congr 1
    exact_mod_cast (show p - 5 + 1 = p - 4 by omega)
  rw [show p - 1 - 1 = p - 2 by omega, show p - 1 - 2 = p - 3 by omega,
    show p - 1 - 3 = p - 4 by omega, show p - 1 - 4 = p - 5 by omega,
    hdA0, hdA1, hdA2, hdA3, hdA4] at hAAraw
  have hAA : (A * derivative A).coeff i0 =
      ((p - 2 : ℕ) : k) *
        ((2 : k) * A.coeff p * A.coeff (p - 4) +
          (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
          A.coeff (p - 2) ^ 2) := by
    have hc04 : ((p : ℕ) : k) + ((p - 4 : ℕ) : k) =
        (2 : k) * ((p - 2 : ℕ) : k) := by
      exact_mod_cast (show p + (p - 4) = 2 * (p - 2) by omega)
    have hc13 : ((p - 1 : ℕ) : k) + ((p - 3 : ℕ) : k) =
        (2 : k) * ((p - 2 : ℕ) : k) := by
      exact_mod_cast (show (p - 1) + (p - 3) = 2 * (p - 2) by omega)
    linear_combination hAAraw + A.coeff p * A.coeff (p - 4) * hc04 +
      A.coeff (p - 1) * A.coeff (p - 3) * hc13
  have hAJraw := coeff_mul_four_below_bounds68 (derivative A) J (p - 1) p
    hpm1 hp4 hdA hJ
  rw [show (p - 1) + p - 4 = i0 by dsimp only [i0]; omega,
    show p - 1 - 1 = p - 2 by omega, show p - 1 - 2 = p - 3 by omega,
    show p - 1 - 3 = p - 4 by omega, show p - 1 - 4 = p - 5 by omega,
    hdA0, hdA1, hdA2, hdA3, hdA4] at hAJraw
  have hAJ : (derivative A * J).coeff i0 =
      ((p : ℕ) : k) * A.coeff p * J.coeff (p - 4) +
        ((p - 1 : ℕ) : k) * A.coeff (p - 1) * J.coeff (p - 3) +
        ((p - 2 : ℕ) : k) * A.coeff (p - 2) * J.coeff (p - 2) +
        ((p - 3 : ℕ) : k) * A.coeff (p - 3) * J.coeff (p - 1) +
        ((p - 4 : ℕ) : k) * A.coeff (p - 4) * J.coeff p := by
    linear_combination hAJraw
  have hFconst : Fce = C (Fce.coeff 0) := by
    apply eq_C_of_natDegree_le_zero
    have hFce' : Fce = (3 / 8 : k) • C i4 := hFce
    rw [hFce']
    compute_degree
  have hAAF : (A * derivative A * Fce).coeff i0 = Fce.coeff 0 *
      ((p - 2 : ℕ) : k) *
        ((2 : k) * A.coeff p * A.coeff (p - 4) +
          (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
          A.coeff (p - 2) ^ 2) := by
    have heq : A * derivative A * Fce = Fce.coeff 0 • (A * derivative A) := by
      calc
        A * derivative A * Fce = (A * derivative A) * C (Fce.coeff 0) := by
          conv_lhs => rw [hFconst]
        _ = Fce.coeff 0 • (A * derivative A) := by
          simp only [smul_eq_C_mul]
          ring
    rw [heq, coeff_smul, hAA]
    ring
  rcases had with ⟨j4, j3, hj4, hj3, hrow0, hrow1, hrowTwo, hpos, hiff⟩
  have hfull0 := hpos i0 (by dsimp only [i0, p]; omega)
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
  simp only [coeff_add, coeff_sub, hAAF, hAJ] at hfull0
  have hrow0main :
      Fce.coeff 0 * ((p - 2 : ℕ) : k) *
          ((2 : k) * A.coeff p * A.coeff (p - 4) +
            (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
            A.coeff (p - 2) ^ 2) -
        (((p : ℕ) : k) * A.coeff p * J.coeff (p - 4) +
          ((p - 1 : ℕ) : k) * A.coeff (p - 1) * J.coeff (p - 3) +
          ((p - 2 : ℕ) : k) * A.coeff (p - 2) * J.coeff (p - 2) +
          ((p - 3 : ℕ) : k) * A.coeff (p - 3) * J.coeff (p - 1) +
          ((p - 4 : ℕ) : k) * A.coeff (p - 4) * J.coeff p) +
        L0.coeff i0 + W0.coeff i0 = 0 := by
    linear_combination hfull0
  have hr1 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S 1 hs hq
      (by dsimp only [p] at *; omega)
  have hr2 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S 2 hs hq
      (by dsimp only [p] at *; omega)
  have hr3 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S 3 hs hq
      (by dsimp only [p] at *; omega)
  have hr4 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S 4 hs hq
      (by dsimp only [p] at *; omega)
  dsimp only at hr1 hr2 hr3 hr4
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
  have hp1c : ((p - 1 : ℕ) : k) = ((p : ℕ) : k) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
  have hp2c : ((p - 2 : ℕ) : k) = ((p : ℕ) : k) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ p)]; norm_num
  have hp3c : ((p - 3 : ℕ) : k) = ((p : ℕ) : k) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ p)]; norm_num
  have hp4c : ((p - 4 : ℕ) : k) = ((p : ℕ) : k) - 4 := by
    rw [Nat.cast_sub hp4]; norm_num
  have hresult :
      (9 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) *
          ((p - 2 : ℕ) : k) ^ 2 * ((p - 1 : ℕ) : k) * Fce.coeff 0 *
          ((2 : k) * A.coeff p * A.coeff (p - 4) +
            (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
            A.coeff (p - 2) ^ 2) +
        (6 : k) * ((p - 4 : ℕ) : k) ^ 2 * ((p - 3 : ℕ) : k) *
          ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) *
          A.coeff (p - 4) * B.coeff D ^ 2 * d.coeff V +
        (6 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) *
          ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) *
          (L0.coeff i0 + W0.coeff i0) +
        ((p : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
          ((p - 1 : ℕ) : k) * A.coeff p * (L2.coeff (p - 5) + W2.coeff (p - 5)) +
        ((p - 4 : ℕ) : k) * ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) ^ 2 *
          A.coeff (p - 1) * (L2.coeff (p - 4) + W2.coeff (p - 4)) +
        ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
          ((p - 1 : ℕ) : k) * A.coeff (p - 2) *
          (L2.coeff (p - 3) + W2.coeff (p - 3)) +
        ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) ^ 2 * ((p - 2 : ℕ) : k) *
          A.coeff (p - 3) * (L2.coeff (p - 2) + W2.coeff (p - 2)) = 0 := by
    rw [hp1c, hp2c, hp3c, hp4c] at hrow0main ⊢
    rw [hp1c] at hr1
    rw [hp2c] at hr2
    rw [hp3c] at hr3
    rw [hp4c] at hr4
    linear_combination
      (6 : k) * (((p : ℕ) : k) - 4) * (((p : ℕ) : k) - 3) *
        (((p : ℕ) : k) - 2) * (((p : ℕ) : k) - 1) * hrow0main +
      ((p : ℕ) : k) * (((p : ℕ) : k) - 3) * (((p : ℕ) : k) - 2) *
        (((p : ℕ) : k) - 1) * A.coeff p * hr4 +
      (((p : ℕ) : k) - 4) * (((p : ℕ) : k) - 2) *
        (((p : ℕ) : k) - 1) ^ 2 * A.coeff (p - 1) * hr3 +
      (((p : ℕ) : k) - 4) * (((p : ℕ) : k) - 3) * (((p : ℕ) : k) - 2) *
        (((p : ℕ) : k) - 1) * A.coeff (p - 2) * hr2 +
      (((p : ℕ) : k) - 4) * (((p : ℕ) : k) - 3) ^ 2 *
        (((p : ℕ) : k) - 2) * A.coeff (p - 3) * hr1 +
      (3 : k) * (((p : ℕ) : k) - 4) ^ 2 * (((p : ℕ) : k) - 3) *
        (((p : ℕ) : k) - 2) * (((p : ℕ) : k) - 1) * A.coeff (p - 4) *
        htopReduced
  dsimp only
    [FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionFourthScalar68,
      p, D, V, Fce, L0, W0, L2, W2]
  simpa only [i0] using hresult

/-! ## Remainder cancel -/

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_fourth_transport68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let i0 := 4 * N - 5
    let i2 := 2 * N - 5
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
  let i0 := 4 * N - 5
  let i2 := 2 * N - 5
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
  have hi0pos : 0 < i0 := by dsimp only [i0]; omega
  have hfull0 := hpos i0 hi0pos
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
  have hfull0' :
      (FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
        alpha gamma epsilon 0 eta A B c d e).coeff (4 * N - 5) = 0 := by
    simpa only [i0] using hfull0
  have hfull2' :
      (FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
        alpha gamma epsilon 0 eta A B c d e).coeff (2 * N - 5) = 0 := by
    simpa only [i2] using hfull2
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
    simp only [coeff_sub, hfull0', zero_sub, coeff_add, coeff_smul, smul_eq_mul]
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
    simp only [coeff_sub, hfull2', zero_sub, coeff_add, coeff_smul, smul_eq_mul]
    dsimp only [i2] at hc2 ⊢
    linear_combination hc2

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_clean_fourth_split68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let i0 := 4 * N - 5
    let i2 := 2 * N - 5
    let W0 := FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
      gamma epsilon A B c d e
    let W2 := FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
      gamma epsilon B c d
    (N = 7 ∧ S = 9 ∧
      W0.coeff i0 =
        -(21 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 3) * c.coeff Cc -
        (39 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff (D - 2) *
          c.coeff Cc -
        (18 : k) * gamma * A.coeff (2 * N - 2) * B.coeff (D - 1) * c.coeff Cc -
        (33 / 2 : k) * gamma * A.coeff (2 * N - 3) * B.coeff D * c.coeff Cc -
        (21 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 2) * c.coeff (Cc - 1) -
        (39 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff (D - 1) *
          c.coeff (Cc - 1) -
        (18 : k) * gamma * A.coeff (2 * N - 2) * B.coeff D * c.coeff (Cc - 1) -
        (21 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 1) * c.coeff (Cc - 2) -
        (39 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff D *
          c.coeff (Cc - 2) -
        (21 : k) * gamma * A.coeff (2 * N) * B.coeff D * c.coeff (Cc - 3) ∧
      W2.coeff i2 = (90 : k) * gamma *
        (B.coeff (D - 3) * c.coeff Cc + B.coeff (D - 2) * c.coeff (Cc - 1) +
          B.coeff (D - 1) * c.coeff (Cc - 2) + B.coeff D * c.coeff (Cc - 3))) ∨
    (N = 14 ∧ S = 18 ∧
      W0.coeff i0 =
        -(42 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 2) * c.coeff Cc -
        (81 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff (D - 1) *
          c.coeff Cc -
        (39 : k) * gamma * A.coeff (2 * N - 2) * B.coeff D * c.coeff Cc -
        (42 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 1) * c.coeff (Cc - 1) -
        (81 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff D *
          c.coeff (Cc - 1) -
        (42 : k) * gamma * A.coeff (2 * N) * B.coeff D * c.coeff (Cc - 2) ∧
      W2.coeff i2 = (216 : k) * gamma *
        (B.coeff (D - 2) * c.coeff Cc + B.coeff (D - 1) * c.coeff (Cc - 1) +
          B.coeff D * c.coeff (Cc - 2))) ∨
    (N = 21 ∧ S = 27 ∧
      W0.coeff i0 =
        -(63 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 1) * c.coeff Cc -
        (123 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff D * c.coeff Cc -
        (63 : k) * gamma * A.coeff (2 * N) * B.coeff D * c.coeff (Cc - 1) ∧
      W2.coeff i2 = (342 : k) * gamma *
        (B.coeff (D - 1) * c.coeff Cc + B.coeff D * c.coeff (Cc - 1))) ∨
    (N = 28 ∧ S = 36 ∧
      W0.coeff i0 = -(84 : k) * gamma * A.coeff (2 * N) * B.coeff D * c.coeff Cc ∧
      W2.coeff i2 = (468 : k) * gamma * B.coeff D * c.coeff Cc) ∨
    (35 ≤ N ∧ W0.coeff i0 = 0 ∧ W2.coeff i2 = 0) := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let i0 := 4 * N - 5
  let i2 := 2 * N - 5
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
    gamma epsilon A B c d e
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
    gamma epsilon B c d
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
  rcases hs.1 with ⟨hsupport, hrows⟩
  rcases hsupport with ⟨hstop, hTD⟩
  have hEq : 9 * N = 7 * S := by dsimp only at hTD; omega
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
  have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hc
  have hd' : d.natDegree ≤ V := by dsimp only [V]; rw [hGS] at hd; omega
  have he' : e.natDegree ≤ E := by dsimp only [E]; rw [hGS] at he; omega
  have harith : (N = 7 ∧ S = 9) ∨ (N = 14 ∧ S = 18) ∨ (N = 21 ∧ S = 27) ∨
      (N = 28 ∧ S = 36) ∨ 35 ≤ N := by omega
  have hdecomp0 :
      FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
          gamma epsilon A B c d e =
        -(3 / 2 * gamma : k) • (B * derivative A * c) +
          ((3 : k) • (B * d * derivative d) + (3 : k) • (derivative B * d ^ 2) -
            (9 / 2 * gamma : k) • (B * derivative e) +
            (9 / 2 * gamma : k) • (d * derivative c) +
            (9 / 4 * epsilon : k) • (d * derivative A)) := by
    dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68]
    module
  have hdecomp2 :
      FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
          gamma epsilon B c d =
        ((9 * gamma : k) • (B * derivative c) +
          (9 * gamma : k) • (c * derivative B)) -
          (27 / 2 * epsilon : k) • derivative d := by rfl
  rcases harith with h7 | h14 | h21 | h28 | hlarge
  · left
    rcases h7 with ⟨hN7, hS9⟩
    subst N; subst S
    norm_num [D, Cc, V, E] at hB' hc' hd' he'
    have hdA : (derivative A).natDegree ≤ 13 := by
      have h := natDegree_derivative_le A; omega
    have hBAc := coeff_mul_mul_three_below_bounds68 B (derivative A) c
      3 13 10 (by norm_num) (by norm_num) (by norm_num) hB' hdA hc'
    norm_num at hBAc
    simp only [coeff_derivative] at hBAc
    norm_num at hBAc
    have hBc := coeff_mul_three_below_bounds68 B (derivative c) 3 9
      (by norm_num) (by norm_num) hB'
      (by have h := natDegree_derivative_le c; omega)
    have hdB : (derivative B).natDegree ≤ 2 := by
      have h := natDegree_derivative_le B; omega
    have hcB : (c * derivative B).coeff 9 =
        c.coeff 7 * (derivative B).coeff 2 +
          c.coeff 8 * (derivative B).coeff 1 +
          c.coeff 9 * (derivative B).coeff 0 := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have hmem7 : 7 ∈ Finset.range (9 + 1) := by simp
      have hmem8 : 8 ∈ (Finset.range (9 + 1)).erase 7 := by simp
      have hmem9 : 9 ∈ ((Finset.range (9 + 1)).erase 7).erase 8 := by simp
      have hzero : ∀ i ∈ (((Finset.range (9 + 1)).erase 7).erase 8).erase 9,
          c.coeff i * (derivative B).coeff (9 - i) = 0 := by
        intro i hi
        have hi9 := (Finset.mem_erase.mp hi).1
        have hi8 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        have hi7 :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2).1
        have hirange :=
          (Finset.mem_erase.mp
            (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2).2
        have hi9lt : i < 10 := Finset.mem_range.mp hirange
        by_cases hgt : 10 ≤ i
        · exact (Nat.lt_irrefl _ (hgt.trans_lt hi9lt)).elim
        · have : 2 < 9 - i := by omega
          rw [coeff_eq_zero_of_natDegree_lt (hdB.trans_lt this), mul_zero]
      have hsum := Finset.add_sum_erase (Finset.range (9 + 1))
        (fun i => c.coeff i * (derivative B).coeff (9 - i)) hmem7
      have hsum2 := Finset.add_sum_erase ((Finset.range (9 + 1)).erase 7)
        (fun i => c.coeff i * (derivative B).coeff (9 - i)) hmem8
      have hsum3 := Finset.add_sum_erase
        (((Finset.range (9 + 1)).erase 7).erase 8)
        (fun i => c.coeff i * (derivative B).coeff (9 - i)) hmem9
      have hz : ∑ i ∈ (((Finset.range (9 + 1)).erase 7).erase 8).erase 9,
          c.coeff i * (derivative B).coeff (9 - i) = 0 :=
        Finset.sum_eq_zero hzero
      rw [← hsum, ← hsum2, ← hsum3, hz, add_zero]
      ring
    norm_num at hBc
    simp only [coeff_derivative] at hBc hcB
    norm_num at hBc hcB
    have hlow0 : ((3 : k) • (B * d * derivative d) +
          (3 : k) • (derivative B * d ^ 2) -
          (9 / 2 * gamma : k) • (B * derivative e) +
          (9 / 2 * gamma : k) • (d * derivative c) +
          (9 / 4 * epsilon : k) • (d * derivative A)).natDegree < 23 := by
      compute_degree; omega
    have hlow2 : ((27 / 2 * epsilon : k) • derivative d).natDegree < 9 := by
      compute_degree; omega
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [hdecomp0, coeff_add, coeff_smul, hBAc,
        coeff_eq_zero_of_natDegree_lt hlow0, smul_eq_mul, add_zero]
      norm_num [D, Cc, i0]
      ring
    · simp only [hdecomp2, coeff_sub, coeff_add, coeff_smul, hBc, hcB,
        coeff_eq_zero_of_natDegree_lt hlow2, smul_eq_mul, sub_zero]
      norm_num [D, Cc, i2]
      ring
  · right; left
    rcases h14 with ⟨hN14, hS18⟩
    subst N; subst S
    norm_num [D, Cc, V, E] at hB' hc' hd' he'
    have hdA : (derivative A).natDegree ≤ 27 := by
      have h := natDegree_derivative_le A; omega
    have hBAc := coeff_mul_mul_two_below_bounds68 B (derivative A) c
      6 27 20 (by norm_num) (by norm_num) (by norm_num) hB' hdA hc'
    norm_num at hBAc
    simp only [coeff_derivative] at hBAc
    norm_num at hBAc
    have hBc := coeff_mul_two_below_bounds68 B (derivative c) 6 19
      (by norm_num) (by norm_num) hB'
      (by have h := natDegree_derivative_le c; omega)
    have hcB := coeff_mul_two_below_bounds68 c (derivative B) 20 5
      (by norm_num) (by norm_num) hc'
      (by have h := natDegree_derivative_le B; omega)
    norm_num at hBc hcB
    simp only [coeff_derivative] at hBc hcB
    norm_num at hBc hcB
    have hlow0 : ((3 : k) • (B * d * derivative d) +
          (3 : k) • (derivative B * d ^ 2) -
          (9 / 2 * gamma : k) • (B * derivative e) +
          (9 / 2 * gamma : k) • (d * derivative c) +
          (9 / 4 * epsilon : k) • (d * derivative A)).natDegree < 51 := by
      compute_degree; omega
    have hlow2 : ((27 / 2 * epsilon : k) • derivative d).natDegree < 23 := by
      compute_degree; omega
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [hdecomp0, coeff_add, coeff_smul, hBAc,
        coeff_eq_zero_of_natDegree_lt hlow0, smul_eq_mul, add_zero]
      norm_num [D, Cc, i0]
      ring
    · simp only [hdecomp2, coeff_sub, coeff_add, coeff_smul, hBc, hcB,
        coeff_eq_zero_of_natDegree_lt hlow2, smul_eq_mul, sub_zero]
      norm_num [D, Cc, i2]
      ring
  · right; right; left
    rcases h21 with ⟨hN21, hS27⟩
    subst N; subst S
    norm_num [D, Cc, V, E] at hB' hc' hd' he'
    have hdA : (derivative A).natDegree ≤ 41 := by
      have h := natDegree_derivative_le A; omega
    have hBAc := coeff_mul_mul_one_below_bounds68 B (derivative A) c
      9 41 30 (by norm_num) (by norm_num) (by norm_num) hB' hdA hc'
    norm_num at hBAc
    simp only [coeff_derivative] at hBAc
    norm_num at hBAc
    have hBc := coeff_mul_one_below_bounds68 B (derivative c) 9 29
      (by norm_num) (by norm_num) hB'
      (by have h := natDegree_derivative_le c; omega)
    have hcB := coeff_mul_one_below_bounds68 c (derivative B) 30 8
      (by norm_num) (by norm_num) hc'
      (by have h := natDegree_derivative_le B; omega)
    norm_num at hBc hcB
    simp only [coeff_derivative] at hBc hcB
    norm_num at hBc hcB
    have hlow0 : ((3 : k) • (B * d * derivative d) +
          (3 : k) • (derivative B * d ^ 2) -
          (9 / 2 * gamma : k) • (B * derivative e) +
          (9 / 2 * gamma : k) • (d * derivative c) +
          (9 / 4 * epsilon : k) • (d * derivative A)).natDegree < 79 := by
      compute_degree; omega
    have hlow2 : ((27 / 2 * epsilon : k) • derivative d).natDegree < 37 := by
      compute_degree; omega
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [hdecomp0, coeff_add, coeff_smul, hBAc,
        coeff_eq_zero_of_natDegree_lt hlow0, smul_eq_mul, add_zero]
      norm_num [D, Cc, i0]
      ring
    · simp only [hdecomp2, coeff_sub, coeff_add, coeff_smul, hBc, hcB,
        coeff_eq_zero_of_natDegree_lt hlow2, smul_eq_mul, sub_zero]
      norm_num [D, Cc, i2]
      ring
  · right; right; right; left
    rcases h28 with ⟨hN28, hS36⟩
    subst N; subst S
    norm_num [D, Cc, V, E] at hB' hc' hd' he'
    have hBAc := coeff_mul_mul_derivative_at_bounds68 B c A 12 40 56
      (by norm_num) hB' hc' hA
    norm_num at hBAc
    have hBAc' : (B * derivative A * c).coeff 107 =
        B.coeff 12 * A.coeff 56 * c.coeff 40 * (56 : k) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hBAc
    have hBc := coeff_mul_derivative_at_bounds68 B c 12 40
      (by norm_num) hB' hc'
    have hcB := coeff_mul_derivative_at_bounds68 c B 40 12
      (by norm_num) hc' hB'
    norm_num at hBc hcB
    have hlow0 : ((3 : k) • (B * d * derivative d) +
          (3 : k) • (derivative B * d ^ 2) -
          (9 / 2 * gamma : k) • (B * derivative e) +
          (9 / 2 * gamma : k) • (d * derivative c) +
          (9 / 4 * epsilon : k) • (d * derivative A)).natDegree < 107 := by
      compute_degree; omega
    have hlow2 : ((27 / 2 * epsilon : k) • derivative d).natDegree < 51 := by
      compute_degree; omega
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [hdecomp0, coeff_add, coeff_smul, hBAc',
        coeff_eq_zero_of_natDegree_lt hlow0, smul_eq_mul, add_zero]
      norm_num [D, Cc, i0]
      ring
    · simp only [hdecomp2, coeff_sub, coeff_add, coeff_smul, hBc, hcB,
        coeff_eq_zero_of_natDegree_lt hlow2, smul_eq_mul, sub_zero]
      norm_num [D, Cc, i2]
      ring
  · right; right; right; right
    refine ⟨hlarge, ?_, ?_⟩
    · apply coeff_eq_zero_of_natDegree_lt
      dsimp only [W0, i0,
        FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68]
      compute_degree
      omega
    · apply coeff_eq_zero_of_natDegree_lt
      dsimp only [W2, i2,
        FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68]
      compute_degree
      omega

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_fourth_cancel68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
      alpha gamma epsilon zeta eta A B c d e
    let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
      alpha gamma epsilon zeta eta A B c d e
    (6 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * W0.coeff (2 * p - 5) +
      ((p : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * A.coeff p * W2.coeff (p - 5) +
      ((p - 4 : ℕ) : k) * ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) ^ 2 *
        A.coeff (p - 1) * W2.coeff (p - 4) +
      ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * A.coeff (p - 2) * W2.coeff (p - 3) +
      ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) ^ 2 * ((p - 2 : ℕ) : k) *
        A.coeff (p - 3) * W2.coeff (p - 2) = 0 := by
  let p := 2 * N
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hold := fiveToSix_zetaFirst_B3_equality_support_qZero_source_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hnext := fiveToSix_zetaFirst_B3_equality_support_qZero_clean_next_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hthird := fiveToSix_zetaFirst_B3_equality_support_qZero_clean_third_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hfourth :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_clean_fourth_split68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have htr4 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_fourth_transport68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have htr3 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_third_transport68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have htr2 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_next_transport68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hold hnext hthird hfourth htr4 htr3 htr2 ⊢
  rcases hfourth with h7 | h14 | h21 | h28 | hlarge
  · rcases h7 with ⟨hN, hS, hW0, hW24⟩
    rcases hthird with ht7 | ht14 | ht21 | htlarge
    · rcases ht7 with ⟨_, _, _, hW23⟩
      rcases hnext with hn7 | hn14 | hnlarge
      · rcases hn7 with ⟨_, _, _, hW22⟩
        rcases hold with ho7 | holarge
        · rcases ho7 with ⟨_, _, _, hW21⟩
          subst N; subst S
          norm_num at hW0 hW24 hW23 hW22 hW21 htr4 htr3 htr2 ⊢
          rw [htr4.1, hW0, htr4.2, hW24, htr3.2, hW23, htr2.2, hW22, hW21]
          ring
        · omega
      · omega
      · omega
    · omega
    · omega
    · omega
  · rcases h14 with ⟨hN, hS, hW0, hW24⟩
    rcases hthird with ht7 | ht14 | ht21 | htlarge
    · omega
    · rcases ht14 with ⟨_, _, _, hW23⟩
      rcases hnext with hn7 | hn14 | hnlarge
      · omega
      · rcases hn14 with ⟨_, _, _, hW22⟩
        rcases hold with ho7 | holarge
        · omega
        · rcases holarge with ⟨_, hW01, hW21⟩
          subst N; subst S
          norm_num at hW0 hW24 hW23 hW22 hW21 htr4 htr3 htr2 ⊢
          rw [htr4.1, hW0, htr4.2, hW24, htr3.2, hW23, htr2.2, hW22, hW21]
          ring
      · omega
    · omega
    · omega
  · rcases h21 with ⟨hN, hS, hW0, hW24⟩
    rcases hthird with ht7 | ht14 | ht21 | htlarge
    · omega
    · omega
    · rcases ht21 with ⟨_, _, _, hW23⟩
      rcases hnext with hn7 | hn14 | hnlarge
      · omega
      · omega
      · rcases hnlarge with ⟨_, _, hW22⟩
        rcases hold with ho7 | holarge
        · omega
        · rcases holarge with ⟨_, _, hW21⟩
          subst N; subst S
          norm_num at hW0 hW24 hW23 hW22 hW21 htr4 htr3 htr2 ⊢
          rw [htr4.1, hW0, htr4.2, hW24, htr3.2, hW23, htr2.2, hW22, hW21]
          ring
    · omega
  · rcases h28 with ⟨hN, hS, hW0, hW24⟩
    rcases hthird with ht7 | ht14 | ht21 | htlarge
    · omega
    · omega
    · omega
    · rcases htlarge with ⟨_, _, hW23⟩
      rcases hnext with hn7 | hn14 | hnlarge
      · omega
      · omega
      · rcases hnlarge with ⟨_, _, hW22⟩
        rcases hold with ho7 | holarge
        · omega
        · rcases holarge with ⟨_, _, hW21⟩
          subst N; subst S
          norm_num at hW0 hW24 hW23 hW22 hW21 htr4 htr3 htr2 ⊢
          rw [htr4.1, hW0, htr4.2, hW24, htr3.2, hW23, htr2.2, hW22, hW21]
          ring
  · rcases hlarge with ⟨hNl, hW0, hW24⟩
    rcases hthird with ht7 | ht14 | ht21 | htlarge
    · omega
    · omega
    · omega
    · rcases htlarge with ⟨_, hW03, hW23⟩
      rcases hnext with hn7 | hn14 | hnlarge
      · omega
      · omega
      · rcases hnlarge with ⟨_, hW02, hW22⟩
        rcases hold with ho7 | holarge
        · omega
        · rcases holarge with ⟨_, hW01, hW21⟩
          rw [show 2 * (2 * N) - 5 = 4 * N - 5 by omega]
          rw [htr4.1, hW0, htr4.2, hW24, htr3.2, hW23, htr2.2, hW22, hW21]
          ring

/-! ## Order-four load jets and algebra -/

def FiveToSixQZeroBBDJetFour68 (b0 b1 b2 b3 b4 d0 d1 d2 d3 d4 : k) : k :=
  b0 ^ 2 * d4 + 2 * b0 * b1 * d3 + (2 * b0 * b2 + b1 ^ 2) * d2 +
    (2 * b0 * b3 + 2 * b1 * b2) * d1 + (2 * b0 * b4 + 2 * b1 * b3 + b2 ^ 2) * d0

def FiveToSixQZeroBBDerivativeJetFour68
    (P b0 b1 b2 b3 b4 d0 d1 d2 d3 d4 : k) : k :=
  (4 / 7 * P - 4) * b0 ^ 2 * d4 + 2 * (4 / 7 * P - 3) * b0 * b1 * d3 +
    (4 / 7 * P - 2) * (2 * b0 * b2 + b1 ^ 2) * d2 +
    (4 / 7 * P - 1) * (2 * b0 * b3 + 2 * b1 * b2) * d1 +
    (4 / 7 * P) * (2 * b0 * b4 + 2 * b1 * b3 + b2 ^ 2) * d0

def FiveToSixQZeroBCEDerivativeJetFour68
    (P b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 e0 e1 e2 e3 e4 : k) : k :=
  (15 / 14 * P) * (b0 * c4 + b1 * c3 + b2 * c2 + b3 * c1 + b4 * c0) * e0 +
    (15 / 14 * P - 1) * (b0 * c3 + b1 * c2 + b2 * c1 + b3 * c0) * e1 +
    (15 / 14 * P - 2) * (b0 * c2 + b1 * c1 + b2 * c0) * e2 +
    (15 / 14 * P - 3) * (b0 * c1 + b1 * c0) * e3 +
    (15 / 14 * P - 4) * b0 * c0 * e4

def FiveToSixQZeroCCDerivativeDJetFour68
    (P c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 : k) : k :=
  (1 / 2 : k) * ((10 / 7 * P - 4) * (2 * c0 * c4 + 2 * c1 * c3 + c2 ^ 2) * d0 +
    (10 / 7 * P - 3) * (2 * c0 * c3 + 2 * c1 * c2) * d1 +
    (10 / 7 * P - 2) * (2 * c0 * c2 + c1 ^ 2) * d2 +
    (10 / 7 * P - 1) * (2 * c0 * c1) * d3 +
    (10 / 7 * P) * c0 ^ 2 * d4)

def FiveToSixQZeroRowZeroLoadJetFour68
    (P a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
      d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 : k) : k :=
  (1 / 2 : k) * a0 * ((P - 4) *
      FiveToSixQZeroBBDJetFour68 b0 b1 b2 b3 b4 d0 d1 d2 d3 d4 +
    FiveToSixQZeroBBDerivativeJetFour68 P b0 b1 b2 b3 b4 d0 d1 d2 d3 d4) +
  (1 / 2 : k) * a1 * ((P - 3) *
      FiveToSixQZeroBBDJetThree68 b0 b1 b2 b3 d0 d1 d2 d3 +
    FiveToSixQZeroBBDerivativeJetThree68 P b0 b1 b2 b3 d0 d1 d2 d3) +
  (1 / 2 : k) * a2 * ((P - 2) *
      FiveToSixQZeroBBDJetTwo68 b0 b1 b2 d0 d1 d2 +
    FiveToSixQZeroBBDerivativeJetTwo68 P b0 b1 b2 d0 d1 d2) +
  (1 / 2 : k) * a3 * ((P - 1) *
      FiveToSixQZeroBBDJetOne68 b0 b1 d0 d1 +
    FiveToSixQZeroBBDerivativeJetOne68 P b0 b1 d0 d1) +
  (1 / 2 : k) * a4 * (P * FiveToSixQZeroBBDJetZero68 b0 d0 +
    FiveToSixQZeroBBDerivativeJetZero68 P b0 d0) -
  3 * FiveToSixQZeroBCEDerivativeJetFour68 P
    b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 e0 e1 e2 e3 e4 +
  3 * FiveToSixQZeroCCDerivativeDJetFour68 P
    c0 c1 c2 c3 c4 d0 d1 d2 d3 d4

/-- Exact polynomial certificate for the fourth load. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_algebra68
    (P a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
      d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 : k)
    (hb0 : b0 ≠ 0)
    (hD0 : a0 * b0 ^ 2 + 3 * c0 ^ 2 = 0)
    (hD1 : a1 * b0 ^ 2 + 2 * a0 * b0 * b1 + 6 * c0 * c1 = 0)
    (hD2 : a2 * b0 ^ 2 + 2 * a1 * b0 * b1 + a0 * (2 * b0 * b2 + b1 ^ 2) +
      3 * (2 * c0 * c2 + c1 ^ 2) = 0)
    (hD3 : a3 * b0 ^ 2 + 2 * a2 * b0 * b1 + a1 * (2 * b0 * b2 + b1 ^ 2) +
      a0 * (2 * b0 * b3 + 2 * b1 * b2) + 6 * (c0 * c3 + c1 * c2) = 0)
    (hD4 : a4 * b0 ^ 2 + 2 * a3 * b0 * b1 + a2 * (2 * b0 * b2 + b1 ^ 2) +
      a1 * (2 * b0 * b3 + 2 * b1 * b2) +
      a0 * (2 * b0 * b4 + 2 * b1 * b3 + b2 ^ 2) +
      6 * (c0 * c4 + c1 * c3) + 3 * c2 ^ 2 = 0)
    (hI40 : b0 * e0 + c0 * d0 = 0)
    (hI41 : b1 * e0 + b0 * e1 + c1 * d0 + c0 * d1 = 0)
    (hI42 : b2 * e0 + b1 * e1 + b0 * e2 + c2 * d0 + c1 * d1 + c0 * d2 = 0)
    (hI43 : b3 * e0 + b2 * e1 + b1 * e2 + b0 * e3 +
      c3 * d0 + c2 * d1 + c1 * d2 + c0 * d3 = 0)
    (hI44 : b4 * e0 + b3 * e1 + b2 * e2 + b1 * e3 + b0 * e4 +
      c4 * d0 + c3 * d1 + c2 * d2 + c1 * d3 + c0 * d4 = 0) :
    6 * (P - 4) ^ 2 * (P - 3) * (P - 2) * (P - 1) * a4 * b0 ^ 2 * d0 +
      6 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        FiveToSixQZeroRowZeroLoadJetFour68 P
          a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
          d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 +
      P * (P - 3) * (P - 2) * (P - 1) * a0 * (6 * (P - 4) *
        FiveToSixQZeroBBDJetFour68 b0 b1 b2 b3 b4 d0 d1 d2 d3 d4) +
      (P - 4) * (P - 2) * (P - 1) ^ 2 * a1 * (6 * (P - 3) *
        FiveToSixQZeroBBDJetThree68 b0 b1 b2 b3 d0 d1 d2 d3) +
      (P - 4) * (P - 3) * (P - 2) * (P - 1) * a2 * (6 * (P - 2) *
        FiveToSixQZeroBBDJetTwo68 b0 b1 b2 d0 d1 d2) +
      (P - 4) * (P - 3) ^ 2 * (P - 2) * a3 * (6 * (P - 1) *
        FiveToSixQZeroBBDJetOne68 b0 b1 d0 d1) = 0 := by
  have hmul : b0 ^ 4 * (
      6 * (P - 4) ^ 2 * (P - 3) * (P - 2) * (P - 1) * a4 * b0 ^ 2 * d0 +
        6 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
          FiveToSixQZeroRowZeroLoadJetFour68 P
            a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
            d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 +
        P * (P - 3) * (P - 2) * (P - 1) * a0 * (6 * (P - 4) *
          FiveToSixQZeroBBDJetFour68 b0 b1 b2 b3 b4 d0 d1 d2 d3 d4) +
        (P - 4) * (P - 2) * (P - 1) ^ 2 * a1 * (6 * (P - 3) *
          FiveToSixQZeroBBDJetThree68 b0 b1 b2 b3 d0 d1 d2 d3) +
        (P - 4) * (P - 3) * (P - 2) * (P - 1) * a2 * (6 * (P - 2) *
          FiveToSixQZeroBBDJetTwo68 b0 b1 b2 d0 d1 d2) +
        (P - 4) * (P - 3) ^ 2 * (P - 2) * a3 * (6 * (P - 1) *
          FiveToSixQZeroBBDJetOne68 b0 b1 d0 d1)) = 0 := by
    dsimp only [FiveToSixQZeroRowZeroLoadJetFour68,
      FiveToSixQZeroBBDJetZero68, FiveToSixQZeroBBDJetOne68,
      FiveToSixQZeroBBDJetTwo68, FiveToSixQZeroBBDJetThree68,
      FiveToSixQZeroBBDJetFour68,
      FiveToSixQZeroBBDerivativeJetZero68,
      FiveToSixQZeroBBDerivativeJetOne68,
      FiveToSixQZeroBBDerivativeJetTwo68,
      FiveToSixQZeroBBDerivativeJetThree68,
      FiveToSixQZeroBBDerivativeJetFour68,
      FiveToSixQZeroBCEDerivativeJetFour68,
      FiveToSixQZeroCCDerivativeDJetFour68]
    linear_combination
      (3 / 7 : k) * b0 ^ 4 * d0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        (25 * P - 56) * hD4 +
      (3 / 7 : k) * b0 ^ 3 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 * d1 + 14 * b1 * d0) * hD3 +
      (3 / 7 : k) * b0 ^ 2 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 ^ 2 * d2 + 14 * b0 * b1 * d1 +
          28 * b0 * b2 * d0 - 14 * b1 ^ 2 * d0) * hD2 +
      (3 / 7 : k) * b0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 ^ 3 * d3 + 14 * b0 ^ 2 * b1 * d2 +
          28 * b0 ^ 2 * b2 * d1 + 42 * b0 ^ 2 * b3 * d0 -
          14 * b0 * b1 ^ 2 * d1 - 42 * b0 * b1 * b2 * d0 +
          14 * b1 ^ 3 * d0) * hD1 +
      (3 / 7 : k) * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((25 * P - 56) * b0 ^ 4 * d4 + 14 * b0 ^ 3 * b1 * d3 +
          28 * b0 ^ 3 * b2 * d2 + 42 * b0 ^ 3 * b3 * d1 +
          56 * b0 ^ 3 * b4 * d0 - 14 * b0 ^ 2 * b1 ^ 2 * d2 -
          42 * b0 ^ 2 * b1 * b2 * d1 - 56 * b0 ^ 2 * b1 * b3 * d0 -
          28 * b0 ^ 2 * b2 ^ 2 * d0 + 14 * b0 * b1 ^ 3 * d1 +
          56 * b0 * b1 ^ 2 * b2 * d0 - 14 * b1 ^ 4 * d0) * hD0 -
      (9 / 7 : k) * b0 ^ 4 * c0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        (15 * P - 56) * hI44 -
      (9 / 7 : k) * b0 ^ 3 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((15 * P - 42) * b0 * c1 + 14 * b1 * c0) * hI43 -
      (9 / 7 : k) * b0 ^ 2 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((15 * P - 28) * b0 ^ 2 * c2 + 14 * b0 * b1 * c1 +
          28 * b0 * b2 * c0 - 14 * b1 ^ 2 * c0) * hI42 -
      (9 / 7 : k) * b0 * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        ((15 * P - 14) * b0 ^ 3 * c3 + 14 * b0 ^ 2 * b1 * c2 +
          28 * b0 ^ 2 * b2 * c1 + 42 * b0 ^ 2 * b3 * c0 -
          14 * b0 * b1 ^ 2 * c1 - 42 * b0 * b1 * b2 * c0 +
          14 * b1 ^ 3 * c0) * hI41 -
      (9 / 7 : k) * (P - 4) * (P - 3) * (P - 2) * (P - 1) *
        (15 * P * b0 ^ 4 * c4 + 14 * b0 ^ 3 * b1 * c3 +
          28 * b0 ^ 3 * b2 * c2 + 42 * b0 ^ 3 * b3 * c1 +
          56 * b0 ^ 3 * b4 * c0 - 14 * b0 ^ 2 * b1 ^ 2 * c2 -
          42 * b0 ^ 2 * b1 * b2 * c1 - 56 * b0 ^ 2 * b1 * b3 * c0 -
          28 * b0 ^ 2 * b2 ^ 2 * c0 + 14 * b0 * b1 ^ 3 * c1 +
          56 * b0 * b1 ^ 2 * b2 * c0 - 14 * b1 ^ 4 * c0) * hI40
  have hb04 : b0 ^ 4 ≠ 0 := pow_ne_zero 4 hb0
  exact (mul_eq_zero.mp hmul).resolve_left hb04

/-- Exact fourth-jet expansion of the row-two load. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_fourth68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    L2.coeff (p - 5) = (6 : k) * ((p - 4 : ℕ) : k) *
      FiveToSixQZeroBBDJetFour68
        (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
        (if 4 ≤ D then B.coeff (D - 4) else 0)
        (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
        (d.coeff (V - 4)) := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  change L2.coeff (p - 5) = _
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
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
  have hd' : d.natDegree ≤ V := by dsimp only [V]; rw [hGS] at hd; omega
  have hD3 : 3 ≤ D := by dsimp only [D]; omega
  have hV4 : 4 ≤ V := by dsimp only [V]; omega
  have h2D4 : 4 ≤ 2 * D := by omega
  have hpEq : p = 2 * D + V := by dsimp only [p, D, V]; omega
  have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by compute_degree; omega
  have hprod0 := coeff_mul_four_below_bounds68 (B ^ 2) d (2 * D) V
    h2D4 hV4 hB2deg hd'
  have hB20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
    have h := coeff_mul_at_bounds68 B B D D hB' hB'
    rw [← two_mul] at h
    simpa [pow_two] using h
  have hB21 : (B ^ 2).coeff (2 * D - 1) =
      (2 : k) * B.coeff D * B.coeff (D - 1) := by
    have h := coeff_mul_one_below_bounds68 B B D D (by omega) (by omega) hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢; linear_combination h
  have hB22 : (B ^ 2).coeff (2 * D - 2) =
      (2 : k) * B.coeff D * B.coeff (D - 2) + B.coeff (D - 1) ^ 2 := by
    have h := coeff_mul_two_below_bounds68 B B D D (by omega) (by omega) hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢; linear_combination h
  have hB23 : (B ^ 2).coeff (2 * D - 3) =
      (2 : k) * B.coeff D * B.coeff (D - 3) +
        (2 : k) * B.coeff (D - 1) * B.coeff (D - 2) := by
    have h := coeff_mul_three_below_bounds68 B B D D hD3 hD3 hB' hB'
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢; linear_combination h
  have hB24 := coeff_sq_sub_four68 B D hD3 hB'
  have hprod : (B ^ 2 * d).coeff (p - 4) =
      FiveToSixQZeroBBDJetFour68
        (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
        (if 4 ≤ D then B.coeff (D - 4) else 0)
        (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
        (d.coeff (V - 4)) := by
    rw [hpEq, show 2 * D + V - 4 = 2 * D + V - 4 by rfl, hprod0,
      hB20, hB21, hB22, hB23, hB24]
    dsimp only [FiveToSixQZeroBBDJetFour68]
    ring
  have hsq : derivative (B ^ 2) = (2 : k) • (B * derivative B) := by
    rw [show B ^ 2 = B * B by ring, derivative_mul]
    simp only [two_smul]; ring
  have hder : derivative (B ^ 2 * d) =
      (2 : k) • (B * derivative B * d) + B ^ 2 * derivative d := by
    rw [derivative_mul, hsq]; simp only [two_smul]; ring
  have hL2poly : L2 = (6 : k) • derivative (B ^ 2 * d) := by
    dsimp only [L2, FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68]
    rw [hder]; module
  have hidx : p - 5 + 1 = p - 4 := by dsimp only [p]; omega
  have hcast : (((p - 5 : ℕ) : k) + 1) = ((p - 4 : ℕ) : k) := by
    exact_mod_cast hidx
  rw [hL2poly, coeff_smul, coeff_derivative, hidx, hcast, hprod]
  ring

#print axioms coeff_mul_four_below_bounds68
#print axioms coeff_sq_sub_four68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_fourth68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_I4_fourth68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_fourth_cancel68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_fourth68

/-! ## Source-backed load, reduction, and split -/

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_source68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
    let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    (6 : k) * ((p - 4 : ℕ) : k) ^ 2 * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * A.coeff (p - 4) * B.coeff D ^ 2 * d.coeff V +
      (6 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * L0.coeff (2 * p - 5) +
      ((p : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * A.coeff p * L2.coeff (p - 5) +
      ((p - 4 : ℕ) : k) * ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) ^ 2 *
        A.coeff (p - 1) * L2.coeff (p - 4) +
      ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * A.coeff (p - 2) * L2.coeff (p - 3) +
      ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) ^ 2 * ((p - 2 : ℕ) : k) *
        A.coeff (p - 3) * L2.coeff (p - 2) = 0 := by
  -- The identity is the order-four load algebra after the four disc/I4 jets
  -- and the four row-two load expansions.  The row-zero load is identified
  -- with `RowZeroLoadJetFour` by reducing the defining polynomial against
  -- the same jets; that identification is discharged by the algebra
  -- certificate after substituting the source expansions of `L2` and the
  -- cusp/I4 rows, together with the defining expansion of `L0` as
  -- `A*(B^2 d' + B B' d) - 3 B c e' + 3 c c' d`.
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let b4 : k := if 4 ≤ D then B.coeff (D - 4) else 0
  change _ = 0
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
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hb0 : B.coeff D ≠ 0 := by simpa [D, hGS] using hBtop
  have hD0 : A.coeff p * B.coeff D ^ 2 + 3 * c.coeff Cc ^ 2 = 0 := by
    simpa [p, D, Cc, hGS] using hcuspEq
  have hD1 := fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD2 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next_two68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD3 := fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD4 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_fourth68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI40 :=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).1
  have hI41 := fiveToSix_zetaFirst_B3_equality_support_qZero_top_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI42 := fiveToSix_zetaFirst_B3_equality_support_qZero_I4_next_two68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI43 := fiveToSix_zetaFirst_B3_equality_support_qZero_I4_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI44 := fiveToSix_zetaFirst_B3_equality_support_qZero_I4_fourth68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hD1 hD2 hD3 hD4 hI40 hI41 hI42 hI43 hI44
  have hL21 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hL22 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hL23 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hL24 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_fourth68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hL21 hL22 hL23 hL24
  have hL0 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowZero_load_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  -- Identify `L0` at `2p-5` with the order-four jet by the same generating
  -- function as the third jet, shifted one step.  The algebra certificate
  -- only needs that identification after the `L2` expansions.
  have halg :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_algebra68
      ((p : ℕ) : k)
      (A.coeff p) (A.coeff (p - 1)) (A.coeff (p - 2)) (A.coeff (p - 3))
      (A.coeff (p - 4))
      (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
      (c.coeff Cc) (c.coeff (Cc - 1)) (c.coeff (Cc - 2)) (c.coeff (Cc - 3))
      (c.coeff (Cc - 4))
      (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
      (d.coeff (V - 4))
      (e.coeff E) (e.coeff (E - 1)) (e.coeff (E - 2)) (e.coeff (E - 3))
      (e.coeff (E - 4))
      hb0 hD0 hD1 hD2 hD3 (by
        dsimp only [b4] at *
        simpa [p, D, Cc] using hD4) hI40 hI41 hI42 hI43 (by
        dsimp only [b4] at *
        simpa [D, Cc, V, E] using hI44)
  have hp1 : ((p - 1 : ℕ) : k) = ((p : ℕ) : k) - 1 := by
    rw [Nat.cast_sub (by dsimp only [p]; omega)]; norm_num
  have hp2 : ((p - 2 : ℕ) : k) = ((p : ℕ) : k) - 2 := by
    rw [Nat.cast_sub (by dsimp only [p]; omega)]; norm_num
  have hp3 : ((p - 3 : ℕ) : k) = ((p : ℕ) : k) - 3 := by
    rw [Nat.cast_sub (by dsimp only [p]; omega)]; norm_num
  have hp4 : ((p - 4 : ℕ) : k) = ((p : ℕ) : k) - 4 := by
    rw [Nat.cast_sub (by dsimp only [p]; omega)]; norm_num
  -- `L0.coeff (2p-5)` is the order-four row-zero load jet: this is the
  -- defining expansion of `L0` against `B^2 d`, `B c e'`, and `c c' d`.
  -- It is supplied by evaluating the same Cauchy products as
  -- `rowZero_load_third` one index lower; the algebra identity then
  -- cancels every non-`Fce` term.
  have hL0four :
      L0.coeff (2 * p - 5) =
        FiveToSixQZeroRowZeroLoadJetFour68 ((p : ℕ) : k)
          (A.coeff p) (A.coeff (p - 1)) (A.coeff (p - 2)) (A.coeff (p - 3))
          (A.coeff (p - 4))
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (c.coeff Cc) (c.coeff (Cc - 1)) (c.coeff (Cc - 2)) (c.coeff (Cc - 3))
          (c.coeff (Cc - 4))
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4))
          (e.coeff E) (e.coeff (E - 1)) (e.coeff (E - 2)) (e.coeff (E - 3))
          (e.coeff (E - 4)) := by
    -- Direct expansion of `L0 = A*(B^2*d'+B*B'*d)-3*B*c*e'+3*c*c'*d`.
    -- The Cauchy products are the order-four jets by construction of those
    -- `def`s; we close by the polynomial ring.
    have hA' : A.natDegree ≤ p := by simpa [p] using hA
    have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
    have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hc
    have hd' : d.natDegree ≤ V := by dsimp only [V]; rw [hGS] at hd; omega
    have he' : e.natDegree ≤ E := by dsimp only [E]; rw [hGS] at he; omega
    have hpEq : p = 2 * D + V := by dsimp only [p, D, V]; omega
    have htwopEq : 2 * p = D + Cc + E := by dsimp only [p, D, Cc, E]; omega
    have htwopEq' : 2 * p = 2 * Cc + V := by dsimp only [p, Cc, V]; omega
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
    let Q := B ^ 2 * d
    let R := B ^ 2 * derivative d
    let T := B ^ 2 * derivative d + B * derivative B * d
    have hQdeg : Q.natDegree ≤ p := by dsimp only [Q]; compute_degree; omega
    have hTdeg : T.natDegree ≤ p - 1 := by
      have hdd := natDegree_derivative_le d
      have hdB := natDegree_derivative_le B
      dsimp only [T]; compute_degree; omega
    have h2D4 : 4 ≤ 2 * D := by omega
    have hV4 : 4 ≤ V := by dsimp only [V]; omega
    have hB2deg : (B ^ 2).natDegree ≤ 2 * D := by compute_degree; omega
    have hdder : (derivative d).natDegree ≤ V - 1 :=
      (natDegree_derivative_le d).trans (Nat.sub_le_sub_right hd' 1)
    have hV1 : 4 ≤ V - 1 := by dsimp only [V]; omega
    have hQ4 : Q.coeff (p - 4) =
        FiveToSixQZeroBBDJetFour68
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4)) := by
      have h := coeff_mul_four_below_bounds68 (B ^ 2) d (2 * D) V
        h2D4 hV4 hB2deg hd'
      have hB20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
        have h' := coeff_mul_at_bounds68 B B D D hB' hB'
        rw [← two_mul] at h'
        simpa [pow_two] using h'
      have hB21 : (B ^ 2).coeff (2 * D - 1) =
          (2 : k) * B.coeff D * B.coeff (D - 1) := by
        have h' := coeff_mul_one_below_bounds68 B B D D
          (by omega) (by omega) hB' hB'
        rw [← two_mul] at h'
        simp only [pow_two] at h' ⊢; linear_combination h'
      have hB22 : (B ^ 2).coeff (2 * D - 2) =
          (2 : k) * B.coeff D * B.coeff (D - 2) + B.coeff (D - 1) ^ 2 := by
        have h' := coeff_mul_two_below_bounds68 B B D D
          (by omega) (by omega) hB' hB'
        rw [← two_mul] at h'
        simp only [pow_two] at h' ⊢; linear_combination h'
      have hB23 : (B ^ 2).coeff (2 * D - 3) =
          (2 : k) * B.coeff D * B.coeff (D - 3) +
            (2 : k) * B.coeff (D - 1) * B.coeff (D - 2) := by
        have h' := coeff_mul_three_below_bounds68 B B D D
          (by dsimp only [D]; omega) (by dsimp only [D]; omega) hB' hB'
        rw [← two_mul] at h'
        simp only [pow_two] at h' ⊢; linear_combination h'
      have hB24 := coeff_sq_sub_four68 B D (by dsimp only [D]; omega) hB'
      have hpQ : p - 4 = 2 * D + V - 4 := by omega
      dsimp only [Q, FiveToSixQZeroBBDJetFour68, b4]
      rw [hpQ, h, hB20, hB21, hB22, hB23, hB24]
      ring
    have hdt := coeff_derivative_at_bound68 d V (by omega)
    have hd1 := coeff_derivative_at_bound68 d (V - 1) (by omega)
    have hd2 := coeff_derivative_at_bound68 d (V - 2) (by omega)
    have hd3 := coeff_derivative_at_bound68 d (V - 3) (by omega)
    have hd4 := coeff_derivative_at_bound68 d (V - 4) (by omega)
    have hcastV1 : (((V - 1 : ℕ) : k)) = ((V : ℕ) : k) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hcastV2 : (((V - 2 : ℕ) : k)) = ((V : ℕ) : k) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hcastV3 : (((V - 3 : ℕ) : k)) = ((V : ℕ) : k) - 3 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hcastV4 : (((V - 4 : ℕ) : k)) = ((V : ℕ) : k) - 4 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hR4 : R.coeff (p - 5) =
        FiveToSixQZeroBBDerivativeJetFour68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4)) := by
      have h := coeff_mul_four_below_bounds68 (B ^ 2) (derivative d)
        (2 * D) (V - 1) h2D4 hV1 hB2deg hdder
      have hB20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
        have h' := coeff_mul_at_bounds68 B B D D hB' hB'
        rw [← two_mul] at h'
        simpa [pow_two] using h'
      have hB21 : (B ^ 2).coeff (2 * D - 1) =
          (2 : k) * B.coeff D * B.coeff (D - 1) := by
        have h' := coeff_mul_one_below_bounds68 B B D D
          (by omega) (by omega) hB' hB'
        rw [← two_mul] at h'
        simp only [pow_two] at h' ⊢; linear_combination h'
      have hB22 : (B ^ 2).coeff (2 * D - 2) =
          (2 : k) * B.coeff D * B.coeff (D - 2) + B.coeff (D - 1) ^ 2 := by
        have h' := coeff_mul_two_below_bounds68 B B D D
          (by omega) (by omega) hB' hB'
        rw [← two_mul] at h'
        simp only [pow_two] at h' ⊢; linear_combination h'
      have hB23 : (B ^ 2).coeff (2 * D - 3) =
          (2 : k) * B.coeff D * B.coeff (D - 3) +
            (2 : k) * B.coeff (D - 1) * B.coeff (D - 2) := by
        have h' := coeff_mul_three_below_bounds68 B B D D
          (by dsimp only [D]; omega) (by dsimp only [D]; omega) hB' hB'
        rw [← two_mul] at h'
        simp only [pow_two] at h' ⊢; linear_combination h'
      have hB24 := coeff_sq_sub_four68 B D (by dsimp only [D]; omega) hB'
      have hpR : 2 * D + (V - 1) - 4 = p - 5 := by omega
      rw [hpR, hB20, hB21, hB22, hB23, hB24] at h
      rw [show V - 1 - 2 = V - 2 - 1 by omega,
        show V - 1 - 3 = V - 3 - 1 by omega,
        show V - 1 - 4 = V - 4 - 1 by omega] at h
      rw [hdt, hd1, hd2, hd3, hd4, hcastV1, hcastV2, hcastV3, hcastV4] at h
      dsimp only [R, FiveToSixQZeroBBDerivativeJetFour68, b4]
      rw [hVcast] at h
      simp only [pow_two] at h ⊢
      linear_combination h
    have hTpoly : T = (1 / 2 : k) • (derivative Q + R) := by
      dsimp only [T, Q, R]
      have hder : derivative (B ^ 2 * d) =
          derivative (B ^ 2) * d + B ^ 2 * derivative d := by
        rw [derivative_mul]
      have hsq : derivative (B ^ 2) = (2 : k) • (B * derivative B) := by
        rw [show B ^ 2 = B * B by ring, derivative_mul]
        simp only [two_smul]; ring
      rw [hder, hsq, smul_mul_assoc, add_assoc]
      have htwice : B ^ 2 * derivative d + B ^ 2 * derivative d =
          (2 : k) • (B ^ 2 * derivative d) := by simp only [two_smul]
      rw [htwice, ← smul_add, smul_smul]
      norm_num
      ring
    -- Remaining `T` jets `k=0,1,2,3` are the third-file identities shifted
    -- by the same `Q,R` expansion; they are recovered from
    -- `rowZero_load_third` after subtracting the new `A_(p-4)` slot.
    have hT4 : T.coeff (p - 5) = (1 / 2 : k) * (((p : ℕ) : k) - 4) *
        FiveToSixQZeroBBDJetFour68
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4)) +
        (1 / 2 : k) * FiveToSixQZeroBBDerivativeJetFour68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4)) := by
      rw [hTpoly, coeff_smul, coeff_add, coeff_derivative,
        show p - 5 + 1 = p - 4 by omega, hQ4, hR4]
      have hcast : (((p - 5 : ℕ) : k) + 1) = ((p : ℕ) : k) - 4 := by
        calc
          ((p - 5 : ℕ) : k) + 1 = ((p - 4 : ℕ) : k) := by
            exact_mod_cast (show p - 5 + 1 = p - 4 by omega)
          _ = ((p : ℕ) : k) - 4 := by
            rw [Nat.cast_sub (by dsimp only [p]; omega)]; norm_num
      rw [hcast]
      simp only [smul_eq_mul]
      ring
    have hQ0 : Q.coeff p = FiveToSixQZeroBBDJetZero68 (B.coeff D) (d.coeff V) := by
      have h := coeff_mul_mul_at_bounds68 B B d D D V hB' hB' hd'
      rw [show D + D + V = p by omega] at h
      dsimp only [Q, FiveToSixQZeroBBDJetZero68]
      simpa only [pow_two] using h
    have hQ1 : Q.coeff (p - 1) = FiveToSixQZeroBBDJetOne68
        (B.coeff D) (B.coeff (D - 1)) (d.coeff V) (d.coeff (V - 1)) := by
      have h := coeff_mul_mul_one_below_bounds68 B B d D D V
        (by omega) (by omega) (by omega) hB' hB' hd'
      rw [show D + D + V - 1 = p - 1 by omega] at h
      dsimp only [Q, FiveToSixQZeroBBDJetOne68]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      linear_combination h
    have hQ2 : Q.coeff (p - 2) = FiveToSixQZeroBBDJetTwo68
        (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
        (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) := by
      have h := coeff_mul_mul_two_below_bounds68 B B d D D V
        (by omega) (by omega) (by omega) hB' hB' hd'
      rw [show D + D + V - 2 = p - 2 by omega] at h
      dsimp only [Q, FiveToSixQZeroBBDJetTwo68]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      linear_combination h
    have hQ3 : Q.coeff (p - 3) = FiveToSixQZeroBBDJetThree68
        (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
        (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3)) := by
      have h := coeff_mul_mul_three_below_bounds68 B B d D D V
        (by dsimp only [D]; omega) (by dsimp only [D]; omega) (by omega)
        hB' hB' hd'
      rw [show D + D + V - 3 = p - 3 by omega] at h
      dsimp only [Q, FiveToSixQZeroBBDJetThree68]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      linear_combination h
    have hR0 : R.coeff (p - 1) = FiveToSixQZeroBBDerivativeJetZero68
        ((p : ℕ) : k) (B.coeff D) (d.coeff V) := by
      have h := coeff_mul_mul_at_bounds68 B B (derivative d)
        D D (V - 1) hB' hB' hdder
      rw [show D + D + (V - 1) = p - 1 by omega, hdt] at h
      dsimp only [R, FiveToSixQZeroBBDerivativeJetZero68]
      rw [← hVcast]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      linear_combination h
    have hR1 : R.coeff (p - 2) = FiveToSixQZeroBBDerivativeJetOne68
        ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1))
        (d.coeff V) (d.coeff (V - 1)) := by
      have h := coeff_mul_mul_one_below_bounds68 B B (derivative d)
        D D (V - 1) (by omega) (by omega) (by omega) hB' hB' hdder
      rw [show D + D + (V - 1) - 1 = p - 2 by omega, hdt, hd1, hcastV1] at h
      dsimp only [R, FiveToSixQZeroBBDerivativeJetOne68]
      rw [← hVcast]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      linear_combination h
    have hR2 : R.coeff (p - 3) = FiveToSixQZeroBBDerivativeJetTwo68
        ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
        (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) := by
      have h := coeff_mul_mul_two_below_bounds68 B B (derivative d)
        D D (V - 1) (by omega) (by omega) (by omega) hB' hB' hdder
      rw [show D + D + (V - 1) - 2 = p - 3 by omega,
        show V - 1 - 2 = V - 2 - 1 by omega, hdt, hd1, hd2, hcastV1, hcastV2] at h
      dsimp only [R, FiveToSixQZeroBBDerivativeJetTwo68]
      rw [← hVcast]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      linear_combination h
    have hR3 : R.coeff (p - 4) = FiveToSixQZeroBBDerivativeJetThree68
        ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
        (B.coeff (D - 3)) (d.coeff V) (d.coeff (V - 1))
        (d.coeff (V - 2)) (d.coeff (V - 3)) := by
      have h := coeff_mul_mul_three_below_bounds68 B B (derivative d)
        D D (V - 1) (by dsimp only [D]; omega) (by dsimp only [D]; omega)
        (by omega) hB' hB' hdder
      rw [show D + D + (V - 1) - 3 = p - 4 by omega,
        show V - 1 - 2 = V - 2 - 1 by omega, show V - 1 - 3 = V - 3 - 1 by omega,
        hdt, hd1, hd2, hd3, hcastV1, hcastV2, hcastV3] at h
      dsimp only [R, FiveToSixQZeroBBDerivativeJetThree68]
      rw [← hVcast]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      linear_combination h
    have hT0 : T.coeff (p - 1) = (1 / 2 : k) * (p *
        FiveToSixQZeroBBDJetZero68 (B.coeff D) (d.coeff V) +
        FiveToSixQZeroBBDerivativeJetZero68 ((p : ℕ) : k)
          (B.coeff D) (d.coeff V)) := by
      rw [hTpoly, coeff_smul, coeff_add, coeff_derivative,
        show p - 1 + 1 = p by omega, hQ0, hR0]
      have hcast : (((p - 1 : ℕ) : k) + 1) = ((p : ℕ) : k) := by
        exact_mod_cast (show p - 1 + 1 = p by omega)
      rw [hcast]; simp only [smul_eq_mul]; ring
    have hT1 : T.coeff (p - 2) = (1 / 2 : k) * (((p : ℕ) : k) - 1) *
        FiveToSixQZeroBBDJetOne68 (B.coeff D) (B.coeff (D - 1))
          (d.coeff V) (d.coeff (V - 1)) +
        (1 / 2 : k) * FiveToSixQZeroBBDerivativeJetOne68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (d.coeff V) (d.coeff (V - 1)) := by
      rw [hTpoly, coeff_smul, coeff_add, coeff_derivative,
        show p - 2 + 1 = p - 1 by omega, hQ1, hR1]
      have hcast : (((p - 2 : ℕ) : k) + 1) = ((p : ℕ) : k) - 1 := by
        calc
          ((p - 2 : ℕ) : k) + 1 = ((p - 1 : ℕ) : k) := by
            exact_mod_cast (show p - 2 + 1 = p - 1 by omega)
          _ = ((p : ℕ) : k) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [hcast]; ring
    have hT2 : T.coeff (p - 3) = (1 / 2 : k) * (((p : ℕ) : k) - 2) *
        FiveToSixQZeroBBDJetTwo68 (B.coeff D) (B.coeff (D - 1))
          (B.coeff (D - 2)) (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) +
        (1 / 2 : k) * FiveToSixQZeroBBDerivativeJetTwo68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) := by
      rw [hTpoly, coeff_smul, coeff_add, coeff_derivative,
        show p - 3 + 1 = p - 2 by omega, hQ2, hR2]
      have hcast : (((p - 3 : ℕ) : k) + 1) = ((p : ℕ) : k) - 2 := by
        calc
          ((p - 3 : ℕ) : k) + 1 = ((p - 2 : ℕ) : k) := by
            exact_mod_cast (show p - 3 + 1 = p - 2 by omega)
          _ = ((p : ℕ) : k) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [hcast]; ring
    have hT3 : T.coeff (p - 4) = (1 / 2 : k) * (((p : ℕ) : k) - 3) *
        FiveToSixQZeroBBDJetThree68
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3)) +
        (1 / 2 : k) * FiveToSixQZeroBBDerivativeJetThree68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3)) := by
      rw [hTpoly, coeff_smul, coeff_add, coeff_derivative,
        show p - 4 + 1 = p - 3 by omega, hQ3, hR3]
      have hcast : (((p - 4 : ℕ) : k) + 1) = ((p : ℕ) : k) - 3 := by
        calc
          ((p - 4 : ℕ) : k) + 1 = ((p - 3 : ℕ) : k) := by
            exact_mod_cast (show p - 4 + 1 = p - 3 by omega)
          _ = ((p : ℕ) : k) - 3 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [hcast]; ring
    have hATraw := coeff_mul_four_below_bounds68 A T p (p - 1)
      (by dsimp only [p]; omega) (by dsimp only [p]; omega) hA' hTdeg
    rw [show p + (p - 1) - 4 = 2 * p - 5 by omega,
      show p - 1 - 1 = p - 2 by omega, show p - 1 - 2 = p - 3 by omega,
      show p - 1 - 3 = p - 4 by omega, show p - 1 - 4 = p - 5 by omega,
      hT0, hT1, hT2, hT3, hT4] at hATraw
    have hAT : (A * T).coeff (2 * p - 5) =
        (1 / 2 : k) * A.coeff p * (((p : ℕ) : k) - 4) *
            FiveToSixQZeroBBDJetFour68
              (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
              b4 (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2))
              (d.coeff (V - 3)) (d.coeff (V - 4)) +
          (1 / 2 : k) * A.coeff p * FiveToSixQZeroBBDerivativeJetFour68
            ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
            (B.coeff (D - 3)) b4 (d.coeff V) (d.coeff (V - 1))
            (d.coeff (V - 2)) (d.coeff (V - 3)) (d.coeff (V - 4)) +
          (1 / 2 : k) * A.coeff (p - 1) * (((p : ℕ) : k) - 3) *
            FiveToSixQZeroBBDJetThree68
              (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
              (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3)) +
          (1 / 2 : k) * A.coeff (p - 1) * FiveToSixQZeroBBDerivativeJetThree68
            ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
            (B.coeff (D - 3)) (d.coeff V) (d.coeff (V - 1))
            (d.coeff (V - 2)) (d.coeff (V - 3)) +
          (1 / 2 : k) * A.coeff (p - 2) * (((p : ℕ) : k) - 2) *
            FiveToSixQZeroBBDJetTwo68
              (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
              (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) +
          (1 / 2 : k) * A.coeff (p - 2) * FiveToSixQZeroBBDerivativeJetTwo68
            ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
            (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) +
          (1 / 2 : k) * A.coeff (p - 3) * (((p : ℕ) : k) - 1) *
            FiveToSixQZeroBBDJetOne68
              (B.coeff D) (B.coeff (D - 1)) (d.coeff V) (d.coeff (V - 1)) +
          (1 / 2 : k) * A.coeff (p - 3) * FiveToSixQZeroBBDerivativeJetOne68
            ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1))
            (d.coeff V) (d.coeff (V - 1)) +
          (1 / 2 : k) * A.coeff (p - 4) * ((p : ℕ) : k) *
            FiveToSixQZeroBBDJetZero68 (B.coeff D) (d.coeff V) +
          (1 / 2 : k) * A.coeff (p - 4) * FiveToSixQZeroBBDerivativeJetZero68
            ((p : ℕ) : k) (B.coeff D) (d.coeff V) := by
      linear_combination hATraw
    have hde' : (derivative e).natDegree ≤ E - 1 :=
      (natDegree_derivative_le e).trans (Nat.sub_le_sub_right he' 1)
    have het := coeff_derivative_at_bound68 e E (by omega)
    have he1 := coeff_derivative_at_bound68 e (E - 1) (by omega)
    have he2 := coeff_derivative_at_bound68 e (E - 2) (by omega)
    have he3 := coeff_derivative_at_bound68 e (E - 3) (by omega)
    have he4 := coeff_derivative_at_bound68 e (E - 4) (by omega)
    have hcastE1 : (((E - 1 : ℕ) : k)) = ((E : ℕ) : k) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hcastE2 : (((E - 2 : ℕ) : k)) = ((E : ℕ) : k) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hcastE3 : (((E - 3 : ℕ) : k)) = ((E : ℕ) : k) - 3 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hcastE4 : (((E - 4 : ℕ) : k)) = ((E : ℕ) : k) - 4 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hBcdeg : (B * c).natDegree ≤ D + Cc := by compute_degree; omega
    have h3raw := coeff_mul_four_below_bounds68 (B * c) (derivative e)
      (D + Cc) (E - 1) (by omega) (by omega) hBcdeg hde'
    have hBc0 := coeff_mul_at_bounds68 B c D Cc hB' hc'
    have hBc1 := coeff_mul_one_below_bounds68 B c D Cc
      (by omega) (by omega) hB' hc'
    have hBc2 := coeff_mul_two_below_bounds68 B c D Cc
      (by omega) (by omega) hB' hc'
    have hBc3 := coeff_mul_three_below_bounds68 B c D Cc
      (by dsimp only [D]; omega) (by omega) hB' hc'
    have hBc4 := coeff_mul_sub_four_left_ge_three68 B c D Cc
      (by dsimp only [D]; omega) (by omega) hB' hc'
    have hpBCE : D + Cc + (E - 1) - 4 = 2 * p - 5 := by omega
    rw [hpBCE, hBc0, hBc1, hBc2, hBc3, hBc4] at h3raw
    rw [show E - 1 - 2 = E - 2 - 1 by omega,
      show E - 1 - 3 = E - 3 - 1 by omega,
      show E - 1 - 4 = E - 4 - 1 by omega] at h3raw
    rw [het, he1, he2, he3, he4, hcastE1, hcastE2, hcastE3, hcastE4] at h3raw
    have h3 : (B * c * derivative e).coeff (2 * p - 5) =
        FiveToSixQZeroBCEDerivativeJetFour68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (c.coeff Cc) (c.coeff (Cc - 1)) (c.coeff (Cc - 2)) (c.coeff (Cc - 3))
          (c.coeff (Cc - 4))
          (e.coeff E) (e.coeff (E - 1)) (e.coeff (E - 2)) (e.coeff (E - 3))
          (e.coeff (E - 4)) := by
      dsimp only [FiveToSixQZeroBCEDerivativeJetFour68, b4]
      rw [hEcast] at h3raw
      split_ifs at h3raw ⊢ <;> linear_combination h3raw
    have hdc' : (derivative c).natDegree ≤ Cc - 1 :=
      (natDegree_derivative_le c).trans (Nat.sub_le_sub_right hc' 1)
    have hct := coeff_derivative_at_bound68 c Cc (by omega)
    have hc1 := coeff_derivative_at_bound68 c (Cc - 1) (by omega)
    have hc2 := coeff_derivative_at_bound68 c (Cc - 2) (by omega)
    have hc3 := coeff_derivative_at_bound68 c (Cc - 3) (by omega)
    have hc4 := coeff_derivative_at_bound68 c (Cc - 4) (by omega)
    have hcastC1 : (((Cc - 1 : ℕ) : k)) = ((Cc : ℕ) : k) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hcastC2 : (((Cc - 2 : ℕ) : k)) = ((Cc : ℕ) : k) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hcastC3 : (((Cc - 3 : ℕ) : k)) = ((Cc : ℕ) : k) - 3 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hcastC4 : (((Cc - 4 : ℕ) : k)) = ((Cc : ℕ) : k) - 4 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have h4raw := coeff_mul_mul_four_below_bounds68 c (derivative c) d
      Cc (Cc - 1) V (by omega) (by omega) (by omega) hc' hdc' hd'
    rw [show Cc + (Cc - 1) + V - 4 = 2 * p - 5 by omega] at h4raw
    rw [show Cc - 1 - 2 = Cc - 2 - 1 by omega,
      show Cc - 1 - 3 = Cc - 3 - 1 by omega,
      show Cc - 1 - 4 = Cc - 4 - 1 by omega] at h4raw
    rw [hct, hc1, hc2, hc3, hc4, hcastC1, hcastC2, hcastC3, hcastC4] at h4raw
    have h4 : (c * derivative c * d).coeff (2 * p - 5) =
        FiveToSixQZeroCCDerivativeDJetFour68 ((p : ℕ) : k)
          (c.coeff Cc) (c.coeff (Cc - 1)) (c.coeff (Cc - 2)) (c.coeff (Cc - 3))
          (c.coeff (Cc - 4))
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4)) := by
      dsimp only [FiveToSixQZeroCCDerivativeDJetFour68]
      rw [hCcast] at h4raw
      linear_combination h4raw
    have hloadpoly : L0 = A * T - (3 : k) • (B * c * derivative e) +
        (3 : k) • (c * derivative c * d) := by
      dsimp only [L0, T, FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68]
      ring
    rw [hloadpoly]
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hAT, h3, h4]
    dsimp only [FiveToSixQZeroRowZeroLoadJetFour68]
    ring
  rw [hL0four, hL21, hL22, hL23, hL24, hp1, hp2, hp3, hp4]
  dsimp only [p, D, Cc, V, E, b4, FiveToSixQZeroBBDJetOne68,
    FiveToSixQZeroBBDJetTwo68, FiveToSixQZeroBBDJetThree68,
    FiveToSixQZeroBBDJetFour68] at halg ⊢
  linear_combination halg

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth_reduction68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    Fce.coeff 0 * ((2 : k) * A.coeff p * A.coeff (p - 4) +
      (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
      A.coeff (p - 2) ^ 2) = 0 := by
  let p := 2 * N
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  change Fce.coeff 0 * ((2 : k) * A.coeff p * A.coeff (p - 4) +
    (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) + A.coeff (p - 2) ^ 2) = 0
  have hcomp := fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hrem :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_fourth_cancel68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hload :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_source68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only
    [FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionFourthScalar68]
    at hcomp
  dsimp only at hrem hload
  have hmain : (9 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) *
      ((p - 2 : ℕ) : k) ^ 2 * ((p - 1 : ℕ) : k) * Fce.coeff 0 *
      ((2 : k) * A.coeff p * A.coeff (p - 4) +
        (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
        A.coeff (p - 2) ^ 2) = 0 := by
    dsimp only [p, Fce, L0, W0, L2, W2]
    linear_combination hcomp - hrem - hload
  have hp4 : 4 < p := by
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
    dsimp only [p]; omega
  have hpm4 : ((p - 4 : ℕ) : k) ≠ 0 := by exact_mod_cast (show p - 4 ≠ 0 by omega)
  have hpm3 : ((p - 3 : ℕ) : k) ≠ 0 := by exact_mod_cast (show p - 3 ≠ 0 by omega)
  have hpm2 : ((p - 2 : ℕ) : k) ≠ 0 := by exact_mod_cast (show p - 2 ≠ 0 by omega)
  have hpm1 : ((p - 1 : ℕ) : k) ≠ 0 := by exact_mod_cast (show p - 1 ≠ 0 by omega)
  have hfac : (9 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) *
      ((p - 2 : ℕ) : k) ^ 2 * ((p - 1 : ℕ) : k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpm4) hpm3)
      (pow_ne_zero 2 hpm2)) hpm1
  have hmul : ((9 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) *
      ((p - 2 : ℕ) : k) ^ 2 * ((p - 1 : ℕ) : k)) *
      (Fce.coeff 0 * ((2 : k) * A.coeff p * A.coeff (p - 4) +
        (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
        A.coeff (p - 2) ^ 2)) = 0 := by
    linear_combination hmain
  exact (mul_eq_zero.mp hmul).resolve_left hfac

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_companion_split68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    Fce.coeff 0 = 0 ∨
      (A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧ A.coeff (p - 3) = 0 ∧
        A.coeff (p - 4) = 0) := by
  let p := 2 * N
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  change Fce.coeff 0 = 0 ∨
    (A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧ A.coeff (p - 3) = 0 ∧
      A.coeff (p - 4) = 0)
  by_cases hf : Fce.coeff 0 = 0
  · exact Or.inl hf
  · right
    have hprev :=
      fiveToSix_zetaFirst_B3_equality_support_qZero_third_companion_split68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
    have hfourth :=
      fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth_reduction68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
    dsimp only at hprev hfourth
    rcases hprev with hf0 | ⟨ha1, ha2, ha3⟩
    · exact (hf hf0).elim
    have hjet : (2 : k) * A.coeff p * A.coeff (p - 4) +
        (2 : k) * A.coeff (p - 1) * A.coeff (p - 3) +
        A.coeff (p - 2) ^ 2 = 0 :=
      (mul_eq_zero.mp (by simpa only [p, Fce] using hfourth)).resolve_left hf
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
    have ha0 : A.coeff p ≠ 0 := by simpa [p] using hatop
    have htwoa0 : (2 : k) * A.coeff p ≠ 0 := mul_ne_zero (by norm_num) ha0
    have ha4 : A.coeff (p - 4) = 0 := by
      apply (mul_left_cancel₀ htwoa0)
      rw [ha1, ha2, ha3] at hjet
      linear_combination hjet
    exact ⟨ha1, ha2, ha3, ha4⟩

/-! ## Matching recurrence at `k=4` -/

theorem fiveToSix_qZero_vanishingA_Bc_weighted_algebra68
    (a b c bk ck : k) (hb : b ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hk : c * bk - b * ck = 0) :
    a * b * bk + (3 : k) * c * ck = 0 := by
  have hmul : b * (a * b * bk + (3 : k) * c * ck) = 0 := by
    linear_combination bk * hcusp - (3 : k) * c * hk
  exact (mul_eq_zero.mp hmul).resolve_left hb

theorem fiveToSix_qZero_vanishingA_Bc_jet_four_algebra68
    (a b c b1 c1 b2 c2 b3 c3 b4 c4 : k)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcusp : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hD1 : (2 : k) * a * b * b1 + (6 : k) * c * c1 = 0)
    (hD4 : a * ((2 : k) * b * b4 + (2 : k) * b1 * b3 + b2 ^ 2) +
      (6 : k) * (c * c4 + c1 * c3) + (3 : k) * c2 ^ 2 = 0)
    (h1 : c * b1 - b * c1 = 0)
    (h2 : c * b2 - b * c2 = 0)
    (h3 : c * b3 - b * c3 = 0) :
    c * b4 - b * c4 = 0 := by
  have hD1half : a * b * b1 + (3 : k) * c * c1 = 0 := by
    linear_combination (1 / 2 : k) * hD1
  have hsq2 : a * b2 ^ 2 + (3 : k) * c2 ^ 2 = 0 :=
    fiveToSix_qZero_vanishingA_Bc_sq_algebra68 a b c b2 c2 hb
      (fiveToSix_qZero_vanishingA_Bc_weighted_algebra68 a b c b2 c2 hb
        hcusp h2) h2
  have hcross13 : a * b1 * b3 + (3 : k) * c1 * c3 = 0 :=
    fiveToSix_qZero_vanishingA_Bc_cross_algebra68 a b c b1 c1 b3 c3 hb
      hD1half h3
  have hmul : (2 : k) * a * b * (c * b4 - b * c4) = 0 := by
    linear_combination c * hD4 - (2 : k) * c4 * hcusp -
      (2 : k) * c * hcross13 - c * hsq2
  have h2 : (2 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hmul).resolve_left
    (mul_ne_zero (mul_ne_zero h2 ha) hb)

theorem fiveToSix_qZero_vanishingA_ed_jet_four_algebra68
    (b c b1 c1 b2 c2 b3 c3 b4 c4 e0 e1 e2 e3 e4 d0 d1 d2 d3 d4 : k)
    (hb : b ≠ 0)
    (hI40 : b * e0 + c * d0 = 0)
    (hI44 : b4 * e0 + b3 * e1 + b2 * e2 + b1 * e3 + b * e4 +
      c4 * d0 + c3 * d1 + c2 * d2 + c1 * d3 + c * d4 = 0)
    (h1 : c * b1 - b * c1 = 0)
    (h2 : c * b2 - b * c2 = 0)
    (h3 : c * b3 - b * c3 = 0)
    (h4 : c * b4 - b * c4 = 0)
    (hE1 : b * e1 + c * d1 = 0)
    (hE2 : b * e2 + c * d2 = 0)
    (hE3 : b * e3 + c * d3 = 0) :
    b * e4 + c * d4 = 0 := by
  have hcross31 : b3 * e1 + c3 * d1 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68 b c b3 c3 e1 d1 hb hE1 h3
  have hcross22 : b2 * e2 + c2 * d2 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68 b c b2 c2 e2 d2 hb hE2 h2
  have hcross13 : b1 * e3 + c1 * d3 = 0 :=
    fiveToSix_qZero_vanishingA_ed_cross_algebra68 b c b1 c1 e3 d3 hb hE3 h1
  have hmul : b * (b * e4 + c * d4) = 0 := by
    linear_combination b * hI44 - b4 * hI40 + d0 * h4 -
      b * hcross31 - b * hcross22 - b * hcross13
  exact (mul_eq_zero.mp hmul).resolve_left hb

theorem fiveToSix_qZero_coeff_X_pow_mul_of_lt68
    (r : k) (p : k[X]) {n i : ℕ} (h : i < n) :
    (C r * X ^ n * p).coeff i = 0 := by
  have hXp : (X ^ n * p).coeff i = 0 := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [coeff_X_pow]
    split_ifs with heq
    · have : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      omega
    · rw [zero_mul]
  simp only [mul_assoc, coeff_C_mul, hXp, mul_zero]

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    c.coeff Cc * (if 4 ≤ D then B.coeff (D - 4) else 0) -
      B.coeff D * c.coeff (Cc - 4) = 0 := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  change c.coeff Cc * (if 4 ≤ D then B.coeff (D - 4) else 0) -
    B.coeff D * c.coeff (Cc - 4) = 0
  have hsplit :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_companion_split68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hFne := fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hterminal hs hq
  dsimp only at hsplit
  have hAvan : A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧
      A.coeff (p - 3) = 0 ∧ A.coeff (p - 4) = 0 := by
    rcases hsplit with hf | hA
    · exact (hFne hf).elim
    · exact hA
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hBc
  rcases hBc with ⟨h1, h2, h3⟩
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
  rcases hpacket with ⟨hN, hgt, hle, hAdeg, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have ha0 : A.coeff p ≠ 0 := by simpa [p] using hatop
  have hb0 : B.coeff D ≠ 0 := by simpa [D, hGS] using hBtop
  have hD0 : A.coeff p * B.coeff D ^ 2 + (3 : k) * c.coeff Cc ^ 2 = 0 := by
    simpa [p, D, Cc, hGS] using hcuspEq
  have hD1raw :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD4raw :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_fourth68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hD1raw hD4raw
  have hD1 : (2 : k) * A.coeff p * B.coeff D * B.coeff (D - 1) +
      (6 : k) * c.coeff Cc * c.coeff (Cc - 1) = 0 := by
    rw [hAvan.1] at hD1raw
    linear_combination hD1raw
  have hD4 : A.coeff p *
        ((2 : k) * B.coeff D * (if 4 ≤ D then B.coeff (D - 4) else 0) +
          (2 : k) * B.coeff (D - 1) * B.coeff (D - 3) +
          B.coeff (D - 2) ^ 2) +
      (6 : k) * (c.coeff Cc * c.coeff (Cc - 4) +
        c.coeff (Cc - 1) * c.coeff (Cc - 3)) +
      (3 : k) * c.coeff (Cc - 2) ^ 2 = 0 := by
    rw [hAvan.1, hAvan.2.1, hAvan.2.2.1, hAvan.2.2.2] at hD4raw
    linear_combination hD4raw
  exact fiveToSix_qZero_vanishingA_Bc_jet_four_algebra68
    (A.coeff p) (B.coeff D) (c.coeff Cc)
    (B.coeff (D - 1)) (c.coeff (Cc - 1))
    (B.coeff (D - 2)) (c.coeff (Cc - 2))
    (B.coeff (D - 3)) (c.coeff (Cc - 3))
    (if 4 ≤ D then B.coeff (D - 4) else 0) (c.coeff (Cc - 4))
    ha0 hb0 hD0 hD1 hD4 h1 h2 h3

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    B.coeff D * e.coeff (E - 4) + c.coeff Cc * d.coeff (V - 4) = 0 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  change B.coeff D * e.coeff (E - 4) + c.coeff Cc * d.coeff (V - 4) = 0
  have hBc4 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hEd :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hBc4 hBc hEd
  rcases hBc with ⟨h1, h2, h3⟩
  rcases hEd with ⟨hE1, hE2, hE3⟩
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
  have hb0 : B.coeff D ≠ 0 := by simpa [D, hGS] using hBtop
  have hI40 :=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).1
  have hI44 := fiveToSix_zetaFirst_B3_equality_support_qZero_I4_fourth68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI44' :
      (if 4 ≤ D then B.coeff (D - 4) else 0) * e.coeff E +
        B.coeff (D - 3) * e.coeff (E - 1) + B.coeff (D - 2) * e.coeff (E - 2) +
        B.coeff (D - 1) * e.coeff (E - 3) + B.coeff D * e.coeff (E - 4) +
        c.coeff (Cc - 4) * d.coeff V + c.coeff (Cc - 3) * d.coeff (V - 1) +
        c.coeff (Cc - 2) * d.coeff (V - 2) + c.coeff (Cc - 1) * d.coeff (V - 3) +
        c.coeff Cc * d.coeff (V - 4) = 0 := by
    simpa [D, Cc, V, E, ite_mul, zero_mul] using hI44
  exact fiveToSix_qZero_vanishingA_ed_jet_four_algebra68
    (B.coeff D) (c.coeff Cc)
    (B.coeff (D - 1)) (c.coeff (Cc - 1))
    (B.coeff (D - 2)) (c.coeff (Cc - 2))
    (B.coeff (D - 3)) (c.coeff (Cc - 3))
    (if 4 ≤ D then B.coeff (D - 4) else 0) (c.coeff (Cc - 4))
    (e.coeff E) (e.coeff (E - 1)) (e.coeff (E - 2)) (e.coeff (E - 3))
    (e.coeff (E - 4))
    (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
    (d.coeff (V - 4))
    hb0 hI40 hI44' h1 h2 h3 hBc4 hE1 hE2 hE3

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    A.natDegree = p ∧ A.coeff (p - 1) = 0 ∧ A.coeff (p - 2) = 0 ∧
      A.coeff (p - 3) = 0 ∧ A.coeff (p - 4) = 0 := by
  let p := 2 * N
  have hA :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hsplit :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_companion_split68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hFne := fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_ne_zero68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hterminal hs hq
  dsimp only at hA hsplit
  rcases hsplit with hf | hA4
  · exact (hFne hf).elim
  · exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, hA4.2.2.2⟩

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c).natDegree ≤ Cc - 5 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let R := C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c
  change R.natDegree ≤ Cc - 5
  have hBc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have h4 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hBc
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
  rcases hpacket with ⟨hN, hgt, hle, hA, hBdeg, hcdeg, hd0, he0, hatop,
    hcusp, had⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hBdeg
  have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hcdeg
  have hND : N + D = Cc := by dsimp only [D, Cc]; omega
  have hleR : R.natDegree ≤ Cc := by
    dsimp only [R]; compute_degree; omega
  have hcoeff4 : R.coeff (Cc - 4) = 0 := by
    dsimp only [R]
    by_cases hD4 : 4 ≤ D
    · have hidx : Cc - 4 = N + (D - 4) := by omega
      have hL : (C (c.coeff Cc) * X ^ N * B).coeff (Cc - 4) =
          c.coeff Cc * B.coeff (D - 4) := by
        rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
      simp only [D] at h4 hD4 ⊢
      simp only [coeff_sub, hL, coeff_C_mul, hD4, ite_true] at h4 ⊢
      linear_combination h4
    · have hlt : Cc - 4 < N := by dsimp only [Cc]; omega
      have hL : (C (c.coeff Cc) * X ^ N * B).coeff (Cc - 4) = 0 :=
        fiveToSix_qZero_coeff_X_pow_mul_of_lt68 (c.coeff Cc) B hlt
      simp only [D] at h4 hD4 ⊢
      simp only [coeff_sub, hL, coeff_C_mul, hD4, ite_false, zero_sub] at h4 ⊢
      linear_combination h4
  have h5 : 5 ≤ Cc := by dsimp only [Cc]; omega
  have hprev : R.natDegree ≤ Cc - 4 := hBc
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  by_cases hgt : Cc - 4 < n
  · exact coeff_eq_zero_of_natDegree_lt (hprev.trans_lt hgt)
  · have : n = Cc - 4 := by omega
    simpa [this] using hcoeff4

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let E := 6 * N - 3 * S
    (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d).natDegree ≤ E - 5 := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let R := C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d
  change R.natDegree ≤ E - 5
  have hEd :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  have hE4 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hEd hE4
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, hedeg, hpacket, hrest⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hNV : N + V = E := by dsimp only [V, E]; omega
  have hprev : R.natDegree ≤ E - 4 := hEd
  have hcoeff4 : R.coeff (E - 4) = 0 := by
    dsimp only [R]
    have hidx : E - 4 = N + (V - 4) := by omega
    have hR : (C (c.coeff Cc) * X ^ N * d).coeff (E - 4) =
        c.coeff Cc * d.coeff (V - 4) := by
      rw [hidx, fiveToSix_qZero_C_X_pow_mul_coeff68]
    simp only [coeff_add, coeff_C_mul, hR]
    linear_combination hE4
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  by_cases hgt : E - 4 < n
  · exact coeff_eq_zero_of_natDegree_lt (hprev.trans_lt hgt)
  · have : n = E - 4 := by omega
    simpa [this] using hcoeff4

/-! ## Residual packet -/

/-- Residual after the order-four companion split and matching at `k=4`.
The next unused source coefficient is `A_(2N-5)`.  Not a closure. -/
def FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAOrder4CompanionResidual68
    (gamma epsilon : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAChargedIntegralResidual68
      gamma epsilon A B c d e N S ∧
    A.coeff (p - 4) = 0 ∧
    c.coeff Cc * (if 4 ≤ D then B.coeff (D - 4) else 0) -
      B.coeff D * c.coeff (Cc - 4) = 0 ∧
    B.coeff D * e.coeff (E - 4) + c.coeff Cc * d.coeff (V - 4) = 0 ∧
    (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c).natDegree ≤ Cc - 5 ∧
    (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d).natDegree ≤ E - 5

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_order4_companion68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAOrder4CompanionResidual68
      gamma epsilon A B c d e N S := by
  refine ⟨fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_charged_integral68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq, ?_, ?_, ?_, ?_, ?_⟩
  · exact (fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_A_degree_four68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        hterminal hs hq).2.2.2.2
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_degree_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  · exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_degree_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_companion_fourth_reduction68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_companion_split68
#print axioms fiveToSix_qZero_vanishingA_Bc_jet_four_algebra68
#print axioms fiveToSix_qZero_vanishingA_ed_jet_four_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Bc_jet_four68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_ed_jet_four68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_order4_companion68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes




