import Grok610ScaleZeroCubicLoadCompeteScratch

/-! # Scale-zero cubic N₁ load ladder, `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroCubicLoadCompeteScratch`.  That file
ends at `normalized610ScaleZero_cubicResidual5`: A-dominant
load-compete after `l = 0`, with κ-route implications
`cubicKappaBetaTop610 → β = 0`, `cubicKappaDeltaTop610 → δ = 0`,
`cubicKappaZetaTop610 → ζ = 0`.

Plan `Grok610ScaleZeroCubicLoadCompetePlanScratch.md` File A (§3.1,
§3.2, §3.6): kill `β/δ/ζ/θ` through `N₁` against the correctly tuned
column predicates `cubicN1BetaTop610` (`7T > 18a`),
`cubicN1DeltaTop610` (`7T > 30a`), `cubicN1ZetaTop610` (`T > 6a`),
`cubicN1ThetaTop610` (`7T > 54a`); load-compete σ-argmin cones and
exhaust; `B = D = 0` with all odd loads vanishing forces `Π ≡ 0`.

Does not close the 15 cones (Files B/C).  No `sorry`, no new axioms,
no finite-root shortcut.  Untracked working note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

/-! ## §3.1 Correctly tuned N₁ column predicates -/

section CubicN1ColumnPredicates610

variable {k : Type*} [Field k] [CharZero k]

/-- `7 Θ > 3 ρ`: the `β A⁵` column of `N₁` strictly tops `N₁`. -/
def cubicN1BetaTop610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧
    14 * B.natDegree < 15 * A.natDegree ∧ 7 * C.natDegree < 11 * A.natDegree ∧
    7 * D.natDegree < 13 * A.natDegree ∧ 14 * E.natDegree < 33 * A.natDegree

/-- `7 Θ > 5 ρ`. -/
def cubicN1DeltaTop610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧
    14 * B.natDegree < 11 * A.natDegree ∧ 7 * C.natDegree < 9 * A.natDegree ∧
    7 * D.natDegree < 10 * A.natDegree ∧ 14 * E.natDegree < 27 * A.natDegree

/-- `Θ > ρ`. -/
def cubicN1ZetaTop610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧
    2 * B.natDegree < A.natDegree ∧ C.natDegree < A.natDegree ∧
    D.natDegree < A.natDegree ∧ 2 * E.natDegree < 3 * A.natDegree

/-- `7 Θ > 9 ρ`. -/
def cubicN1ThetaTop610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧
    14 * B.natDegree < 3 * A.natDegree ∧ 7 * C.natDegree < 5 * A.natDegree ∧
    7 * D.natDegree < 4 * A.natDegree ∧ 14 * E.natDegree < 15 * A.natDegree

theorem cubicN1DeltaTop610_to_betaTop
    {A B C D E : k[X]} (h : cubicN1DeltaTop610 A B C D E) :
    cubicN1BetaTop610 A B C D E := by
  rcases h with ⟨hload, hB, hC, hD, hE⟩
  refine ⟨hload, ?_, ?_, ?_, ?_⟩
  · have : 14 * B.natDegree + 1 ≤ 11 * A.natDegree := Nat.succ_le_of_lt hB
    omega
  · have : 7 * C.natDegree + 1 ≤ 9 * A.natDegree := Nat.succ_le_of_lt hC
    omega
  · have : 7 * D.natDegree + 1 ≤ 10 * A.natDegree := Nat.succ_le_of_lt hD
    omega
  · have : 14 * E.natDegree + 1 ≤ 27 * A.natDegree := Nat.succ_le_of_lt hE
    omega

theorem cubicN1ZetaTop610_to_deltaTop
    {A B C D E : k[X]} (h : cubicN1ZetaTop610 A B C D E) :
    cubicN1DeltaTop610 A B C D E := by
  rcases h with ⟨hload, hB, hC, hD, hE⟩
  refine ⟨hload, ?_, ?_, ?_, ?_⟩
  · have : 2 * B.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hB
    omega
  · have : C.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hC
    omega
  · have : D.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hD
    omega
  · have : 2 * E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hE
    omega

theorem cubicN1ZetaTop610_to_betaTop
    {A B C D E : k[X]} (h : cubicN1ZetaTop610 A B C D E) :
    cubicN1BetaTop610 A B C D E :=
  cubicN1DeltaTop610_to_betaTop (cubicN1ZetaTop610_to_deltaTop h)

theorem cubicN1ThetaTop610_to_zetaTop
    {A B C D E : k[X]} (h : cubicN1ThetaTop610 A B C D E) :
    cubicN1ZetaTop610 A B C D E := by
  rcases h with ⟨hload, hB, hC, hD, hE⟩
  refine ⟨hload, ?_, ?_, ?_, ?_⟩
  · have : 14 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hB
    omega
  · have : 7 * C.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hC
    omega
  · have : 7 * D.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hD
    omega
  · have : 14 * E.natDegree + 1 ≤ 15 * A.natDegree := Nat.succ_le_of_lt hE
    omega

theorem cubicN1ThetaTop610_to_deltaTop
    {A B C D E : k[X]} (h : cubicN1ThetaTop610 A B C D E) :
    cubicN1DeltaTop610 A B C D E :=
  cubicN1ZetaTop610_to_deltaTop (cubicN1ThetaTop610_to_zetaTop h)

theorem cubicN1ThetaTop610_to_betaTop
    {A B C D E : k[X]} (h : cubicN1ThetaTop610 A B C D E) :
    cubicN1BetaTop610 A B C D E :=
  cubicN1DeltaTop610_to_betaTop (cubicN1ThetaTop610_to_deltaTop h)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoLNoBetaA5610_natDegree_lt_of_N1BetaTop
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicN1BetaTop610 A B C D E) :
    (degreeZeroN1CubicNoLNoBetaA5610 alpha beta delta epsilon zeta eta
        theta A B C D E).natDegree <
      5 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBn, hCn, hDn, hEn⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hBn1 : 14 * B.natDegree + 1 ≤ 15 * A.natDegree := Nat.succ_le_of_lt hBn
  have hCn1 : 7 * C.natDegree + 1 ≤ 11 * A.natDegree := Nat.succ_le_of_lt hCn
  have hDn1 : 7 * D.natDegree + 1 ≤ 13 * A.natDegree := Nat.succ_le_of_lt hDn
  have hEn1 : 14 * E.natDegree + 1 ≤ 33 * A.natDegree := Nat.succ_le_of_lt hEn
  simp only [degreeZeroN1CubicNoLNoBetaA5610]
  compute_degree
  omega

theorem cubicN1_beta_eq_zero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicN1BetaTop610 A B C D E)
    (hl : l = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0) :
    beta = 0 := by
  by_contra hb
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (7 / 6912 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hb
  have hlead : (n1CubicBetaFace610 beta A).natDegree = 5 * A.natDegree := by
    simp only [n1CubicBetaFace610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroN1CubicNoLNoBetaA5610_natDegree_lt_of_N1BetaTop alpha
      beta delta epsilon zeta eta theta A B C D E hcone
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon zeta eta theta A B C D E hmu hkap
  have hN1deg :
      (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree =
        5 * A.natDegree := by
    subst hl
    rw [degreeZeroN1Cubic610_eq_beta_add_rest_of_l0,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoLNoBetaNoDeltaA4610_natDegree_lt_of_N1DeltaTop
    (alpha delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicN1DeltaTop610 A B C D E) :
    (degreeZeroN1CubicNoLNoBetaNoDeltaA4610 alpha delta epsilon zeta eta
        theta A B C D E).natDegree <
      4 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBn, hCn, hDn, hEn⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hBn1 : 14 * B.natDegree + 1 ≤ 11 * A.natDegree := Nat.succ_le_of_lt hBn
  have hCn1 : 7 * C.natDegree + 1 ≤ 9 * A.natDegree := Nat.succ_le_of_lt hCn
  have hDn1 : 7 * D.natDegree + 1 ≤ 10 * A.natDegree := Nat.succ_le_of_lt hDn
  have hEn1 : 14 * E.natDegree + 1 ≤ 27 * A.natDegree := Nat.succ_le_of_lt hEn
  simp only [degreeZeroN1CubicNoLNoBetaNoDeltaA4610]
  compute_degree
  omega

theorem cubicN1_delta_eq_zero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicN1DeltaTop610 A B C D E)
    (hl : l = 0) (hbeta : beta = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0) :
    delta = 0 := by
  by_contra hd
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (35 / 10368 * delta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hd
  have hlead : (n1CubicDeltaFace610 delta A).natDegree = 4 * A.natDegree := by
    simp only [n1CubicDeltaFace610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroN1CubicNoLNoBetaNoDeltaA4610_natDegree_lt_of_N1DeltaTop alpha
      delta epsilon zeta eta theta A B C D E hcone
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon zeta eta theta A B C D E hmu hkap
  have hN1deg :
      (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree =
        4 * A.natDegree := by
    subst hl
    subst hbeta
    rw [degreeZeroN1Cubic610_eq_delta_add_rest_of_l0_beta0,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoOddPureANoZetaA3610_natDegree_lt_of_N1ZetaTop
    (alpha epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicN1ZetaTop610 A B C D E) :
    (degreeZeroN1CubicNoOddPureANoZetaA3610 alpha epsilon zeta eta theta
        A B C D E).natDegree <
      3 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBn, hCn, hDn, hEn⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hBn1 : 2 * B.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hBn
  have hCn1 : C.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hCn
  have hDn1 : D.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hDn
  have hEn1 : 2 * E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hEn
  simp only [degreeZeroN1CubicNoOddPureANoZetaA3610]
  compute_degree
  omega

theorem cubicN1_zeta_eq_zero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicN1ZetaTop610 A B C D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0) :
    zeta = 0 := by
  by_contra hz
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (5 / 432 * zeta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hz
  have hlead : (n1CubicZetaFace610 zeta A).natDegree = 3 * A.natDegree := by
    simp only [n1CubicZetaFace610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroN1CubicNoOddPureANoZetaA3610_natDegree_lt_of_N1ZetaTop alpha
      epsilon zeta eta theta A B C D E hcone
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon zeta eta theta A B C D E hmu hkap
  have hN1deg :
      (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree =
        3 * A.natDegree := by
    subst hl
    subst hbeta
    subst hdelta
    rw [degreeZeroN1Cubic610_eq_zeta_add_rest_of_odds0,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoOddPureANoThetaA2610_natDegree_lt_of_N1ThetaTop
    (alpha epsilon eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicN1ThetaTop610 A B C D E) :
    (degreeZeroN1CubicNoOddPureANoThetaA2610 alpha epsilon eta theta
        A B C D E).natDegree <
      2 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBn, hCn, hDn, hEn⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hBn1 : 14 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBn
  have hCn1 : 7 * C.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hCn
  have hDn1 : 7 * D.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hDn
  have hEn1 : 14 * E.natDegree + 1 ≤ 15 * A.natDegree := Nat.succ_le_of_lt hEn
  simp only [degreeZeroN1CubicNoOddPureANoThetaA2610]
  compute_degree
  omega

theorem cubicN1_theta_eq_zero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicN1ThetaTop610 A B C D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0) (hzeta : zeta = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0) :
    theta = 0 := by
  by_contra ht
  have hApos : 0 < A.natDegree := hcone.1.1.1
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (1 / 24 * theta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) ht
  have hlead : (n1CubicThetaFace610 theta A).natDegree = 2 * A.natDegree := by
    simp only [n1CubicThetaFace610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroN1CubicNoOddPureANoThetaA2610_natDegree_lt_of_N1ThetaTop alpha
      epsilon eta theta A B C D E hcone
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon zeta eta theta A B C D E hmu hkap
  have hN1deg :
      (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree =
        2 * A.natDegree := by
    subst hl
    subst hbeta
    subst hdelta
    subst hzeta
    rw [degreeZeroN1Cubic610_eq_theta_add_rest_of_odds0,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  omega

theorem cubicN1_beta_band_disjunction
    {beta : k} (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hkill : cubicN1BetaTop610 A B C D E → beta = 0) :
    beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree := by
  by_cases hB : 14 * B.natDegree < 15 * A.natDegree
  · by_cases hC : 7 * C.natDegree < 11 * A.natDegree
    · by_cases hD : 7 * D.natDegree < 13 * A.natDegree
      · by_cases hE : 14 * E.natDegree < 33 * A.natDegree
        · exact Or.inl (hkill ⟨hload, hB, hC, hD, hE⟩)
        · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

theorem cubicN1_delta_band_disjunction
    {delta : k} (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hkill : cubicN1DeltaTop610 A B C D E → delta = 0) :
    delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree := by
  by_cases hB : 14 * B.natDegree < 11 * A.natDegree
  · by_cases hC : 7 * C.natDegree < 9 * A.natDegree
    · by_cases hD : 7 * D.natDegree < 10 * A.natDegree
      · by_cases hE : 14 * E.natDegree < 27 * A.natDegree
        · exact Or.inl (hkill ⟨hload, hB, hC, hD, hE⟩)
        · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

theorem cubicN1_zeta_band_disjunction
    {zeta : k} (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hkill : cubicN1ZetaTop610 A B C D E → zeta = 0) :
    zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree := by
  by_cases hB : 2 * B.natDegree < A.natDegree
  · by_cases hC : C.natDegree < A.natDegree
    · by_cases hD : D.natDegree < A.natDegree
      · by_cases hE : 2 * E.natDegree < 3 * A.natDegree
        · exact Or.inl (hkill ⟨hload, hB, hC, hD, hE⟩)
        · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

theorem cubicN1_theta_band_disjunction
    {theta : k} (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hkill : cubicN1ThetaTop610 A B C D E → theta = 0) :
    theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree := by
  by_cases hB : 14 * B.natDegree < 3 * A.natDegree
  · by_cases hC : 7 * C.natDegree < 5 * A.natDegree
    · by_cases hD : 7 * D.natDegree < 4 * A.natDegree
      · by_cases hE : 14 * E.natDegree < 15 * A.natDegree
        · exact Or.inl (hkill ⟨hload, hB, hC, hD, hE⟩)
        · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

end CubicN1ColumnPredicates610

/-! ## §3.2 Load-compete σ-argmin cones -/

section CubicLoadSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicLoadSigmaConeB610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ B ≠ 0 ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree)

def CubicLoadSigmaConeC610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ C ≠ 0 ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree)

def CubicLoadSigmaConeD610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ D ≠ 0 ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < A.natDegree + 2 * D.natDegree)

def CubicLoadSigmaConeE610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ E ≠ 0 ∧
    (B = 0 ∨ 3 * A.natDegree + 6 * B.natDegree < 4 * E.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < 2 * E.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 2 * E.natDegree)

def CubicLoadSigmaConeBC610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ B ≠ 0 ∧ C ≠ 0 ∧
    4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree)

def CubicLoadSigmaConeBD610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ B ≠ 0 ∧ D ≠ 0 ∧
    10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree)

def CubicLoadSigmaConeBE610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ B ≠ 0 ∧ E ≠ 0 ∧
    12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree)

def CubicLoadSigmaConeCD610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ C ≠ 0 ∧ D ≠ 0 ∧
    5 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * D.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree)

def CubicLoadSigmaConeCE610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ C ≠ 0 ∧ E ≠ 0 ∧
    6 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * E.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree < 3 * C.natDegree)

def CubicLoadSigmaConeDE610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ D ≠ 0 ∧ E ≠ 0 ∧
    6 * A.natDegree + 2 * D.natDegree = 5 * A.natDegree + 2 * E.natDegree ∧
    (B = 0 ∨ A.natDegree + 6 * B.natDegree < 4 * D.natDegree) ∧
    (C = 0 ∨ 3 * C.natDegree < A.natDegree + 2 * D.natDegree)

def CubicLoadSigmaConeBCD610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ B ≠ 0 ∧ C ≠ 0 ∧ D ≠ 0 ∧
    4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree ∧
    10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree)

def CubicLoadSigmaConeBCE610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ B ≠ 0 ∧ C ≠ 0 ∧ E ≠ 0 ∧
    4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree ∧
    12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree + 6 * B.natDegree)

def CubicLoadSigmaConeBDE610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ B ≠ 0 ∧ D ≠ 0 ∧ E ≠ 0 ∧
    10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree ∧
    12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree ∧
    (C = 0 ∨ 2 * C.natDegree < A.natDegree + 2 * B.natDegree)

def CubicLoadSigmaConeCDE610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ C ≠ 0 ∧ D ≠ 0 ∧ E ≠ 0 ∧
    5 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * D.natDegree ∧
    6 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * E.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree)

def CubicLoadSigmaConeBCDE610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ B ≠ 0 ∧ C ≠ 0 ∧ D ≠ 0 ∧ E ≠ 0 ∧
    4 * A.natDegree + 2 * B.natDegree = 3 * A.natDegree + 2 * C.natDegree ∧
    10 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * D.natDegree ∧
    12 * A.natDegree + 6 * B.natDegree = 9 * A.natDegree + 4 * E.natDegree

inductive CubicLoadSigmaSupportCone610 (A B C D E : k[X]) : Prop
  | sigmaB : CubicLoadSigmaConeB610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaC : CubicLoadSigmaConeC610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaD : CubicLoadSigmaConeD610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaE : CubicLoadSigmaConeE610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaBC : CubicLoadSigmaConeBC610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaBD : CubicLoadSigmaConeBD610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaBE : CubicLoadSigmaConeBE610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaCD : CubicLoadSigmaConeCD610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaCE : CubicLoadSigmaConeCE610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaDE : CubicLoadSigmaConeDE610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaBCD : CubicLoadSigmaConeBCD610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaBCE : CubicLoadSigmaConeBCE610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaBDE : CubicLoadSigmaConeBDE610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaCDE : CubicLoadSigmaConeCDE610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | sigmaBCDE : CubicLoadSigmaConeBCDE610 A B C D E →
      CubicLoadSigmaSupportCone610 A B C D E
  | allZero : B = 0 ∧ C = 0 ∧ D = 0 ∧ E = 0 →
      CubicLoadSigmaSupportCone610 A B C D E

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_allZero
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  exact CubicLoadSigmaSupportCone610.allZero ⟨hBz, hCz, hDz, hEz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_E
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hBdeg0 : B.natDegree = 0 := by simp [hBz]
  have hCdeg0 : C.natDegree = 0 := by simp [hCz]
  have hDdeg0 : D.natDegree = 0 := by simp [hDz]
  refine CubicLoadSigmaSupportCone610.sigmaE ?_
  refine ⟨hload, hEne, Or.inl hBz, Or.inl hCz, Or.inl hDz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_D
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hBdeg0 : B.natDegree = 0 := by simp [hBz]
  have hCdeg0 : C.natDegree = 0 := by simp [hCz]
  have hEdeg0 : E.natDegree = 0 := by simp [hEz]
  refine CubicLoadSigmaSupportCone610.sigmaD ?_
  refine ⟨hload, hDne, Or.inl hBz, Or.inl hCz, Or.inl hEz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_DE
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hBdeg0 : B.natDegree = 0 := by simp [hBz]
  have hCdeg0 : C.natDegree = 0 := by simp [hCz]
  by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
  · -- D strictly outranks E (smaller τ)
    refine CubicLoadSigmaSupportCone610.sigmaD ?_
    refine ⟨hload, hDne, Or.inl hBz, Or.inl hCz, Or.inr (by omega)⟩
  · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    · -- E ties D
      refine CubicLoadSigmaSupportCone610.sigmaDE ?_
      refine ⟨hload, hDne, hEne, by omega, Or.inl hBz, Or.inl hCz⟩
    · -- E strictly outranks D
      refine CubicLoadSigmaSupportCone610.sigmaE ?_
      refine ⟨hload, hEne, Or.inl hBz, Or.inl hCz, Or.inr (by omega)⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_C
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hBdeg0 : B.natDegree = 0 := by simp [hBz]
  have hDdeg0 : D.natDegree = 0 := by simp [hDz]
  have hEdeg0 : E.natDegree = 0 := by simp [hEz]
  refine CubicLoadSigmaSupportCone610.sigmaC ?_
  refine ⟨hload, hCne, Or.inl hBz, Or.inl hDz, Or.inl hEz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_CE
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hBdeg0 : B.natDegree = 0 := by simp [hBz]
  have hDdeg0 : D.natDegree = 0 := by simp [hDz]
  by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
  · -- C strictly outranks E (smaller τ)
    refine CubicLoadSigmaSupportCone610.sigmaC ?_
    refine ⟨hload, hCne, Or.inl hBz, Or.inl hDz, Or.inr (by omega)⟩
  · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
    · -- E ties C
      refine CubicLoadSigmaSupportCone610.sigmaCE ?_
      refine ⟨hload, hCne, hEne, by omega, Or.inl hBz, Or.inl hDz⟩
    · -- E strictly outranks C
      refine CubicLoadSigmaSupportCone610.sigmaE ?_
      refine ⟨hload, hEne, Or.inl hBz, Or.inr (by omega), Or.inl hDz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_CD
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hBdeg0 : B.natDegree = 0 := by simp [hBz]
  have hEdeg0 : E.natDegree = 0 := by simp [hEz]
  by_cases hlt : A.natDegree + 2 * D.natDegree < 3 * C.natDegree
  · -- C strictly outranks D (smaller τ)
    refine CubicLoadSigmaSupportCone610.sigmaC ?_
    refine ⟨hload, hCne, Or.inl hBz, Or.inr (by omega), Or.inl hEz⟩
  · by_cases heq : A.natDegree + 2 * D.natDegree = 3 * C.natDegree
    · -- D ties C
      refine CubicLoadSigmaSupportCone610.sigmaCD ?_
      refine ⟨hload, hCne, hDne, by omega, Or.inl hBz, Or.inl hEz⟩
    · -- D strictly outranks C
      refine CubicLoadSigmaSupportCone610.sigmaD ?_
      refine ⟨hload, hDne, Or.inl hBz, Or.inr (by omega), Or.inl hEz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_CDE
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hBdeg0 : B.natDegree = 0 := by simp [hBz]
  by_cases hlt : A.natDegree + 2 * D.natDegree < 3 * C.natDegree
  · -- C strictly outranks D (smaller τ)
    by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
    · -- C strictly outranks E (smaller τ)
      refine CubicLoadSigmaSupportCone610.sigmaC ?_
      refine ⟨hload, hCne, Or.inl hBz, Or.inr (by omega), Or.inr (by omega)⟩
    · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
      · -- E ties C
        refine CubicLoadSigmaSupportCone610.sigmaCE ?_
        refine ⟨hload, hCne, hEne, by omega, Or.inl hBz, Or.inr (by omega)⟩
      · -- E strictly outranks C
        refine CubicLoadSigmaSupportCone610.sigmaE ?_
        refine ⟨hload, hEne, Or.inl hBz, Or.inr (by omega), Or.inr (by omega)⟩
  · by_cases heq : A.natDegree + 2 * D.natDegree = 3 * C.natDegree
    · -- D ties C
      by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
      · -- C strictly outranks E (smaller τ)
        refine CubicLoadSigmaSupportCone610.sigmaCD ?_
        refine ⟨hload, hCne, hDne, by omega, Or.inl hBz, Or.inr (by omega)⟩
      · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
        · -- E ties CD
          refine CubicLoadSigmaSupportCone610.sigmaCDE ?_
          refine ⟨hload, hCne, hDne, hEne, by omega, by omega, Or.inl hBz⟩
        · -- E strictly outranks CD
          refine CubicLoadSigmaSupportCone610.sigmaE ?_
          refine ⟨hload, hEne, Or.inl hBz, Or.inr (by omega), Or.inr (by omega)⟩
    · -- D strictly outranks C
      by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      · -- D strictly outranks E (smaller τ)
        refine CubicLoadSigmaSupportCone610.sigmaD ?_
        refine ⟨hload, hDne, Or.inl hBz, Or.inr (by omega), Or.inr (by omega)⟩
      · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
        · -- E ties D
          refine CubicLoadSigmaSupportCone610.sigmaDE ?_
          refine ⟨hload, hDne, hEne, by omega, Or.inl hBz, Or.inr (by omega)⟩
        · -- E strictly outranks D
          refine CubicLoadSigmaSupportCone610.sigmaE ?_
          refine ⟨hload, hEne, Or.inl hBz, Or.inr (by omega), Or.inr (by omega)⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_B
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hCdeg0 : C.natDegree = 0 := by simp [hCz]
  have hDdeg0 : D.natDegree = 0 := by simp [hDz]
  have hEdeg0 : E.natDegree = 0 := by simp [hEz]
  refine CubicLoadSigmaSupportCone610.sigmaB ?_
  refine ⟨hload, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_BE
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hCdeg0 : C.natDegree = 0 := by simp [hCz]
  have hDdeg0 : D.natDegree = 0 := by simp [hDz]
  by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
  · -- B strictly outranks E (smaller τ)
    refine CubicLoadSigmaSupportCone610.sigmaB ?_
    refine ⟨hload, hBne, Or.inl hCz, Or.inl hDz, Or.inr (by omega)⟩
  · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
    · -- E ties B
      refine CubicLoadSigmaSupportCone610.sigmaBE ?_
      refine ⟨hload, hBne, hEne, by omega, Or.inl hCz, Or.inl hDz⟩
    · -- E strictly outranks B
      refine CubicLoadSigmaSupportCone610.sigmaE ?_
      refine ⟨hload, hEne, Or.inr (by omega), Or.inl hCz, Or.inl hDz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_BD
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hCdeg0 : C.natDegree = 0 := by simp [hCz]
  have hEdeg0 : E.natDegree = 0 := by simp [hEz]
  by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
  · -- B strictly outranks D (smaller τ)
    refine CubicLoadSigmaSupportCone610.sigmaB ?_
    refine ⟨hload, hBne, Or.inl hCz, Or.inr (by omega), Or.inl hEz⟩
  · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
    · -- D ties B
      refine CubicLoadSigmaSupportCone610.sigmaBD ?_
      refine ⟨hload, hBne, hDne, by omega, Or.inl hCz, Or.inl hEz⟩
    · -- D strictly outranks B
      refine CubicLoadSigmaSupportCone610.sigmaD ?_
      refine ⟨hload, hDne, Or.inr (by omega), Or.inl hCz, Or.inl hEz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_BDE
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hCdeg0 : C.natDegree = 0 := by simp [hCz]
  by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
  · -- B strictly outranks D (smaller τ)
    by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
    · -- B strictly outranks E (smaller τ)
      refine CubicLoadSigmaSupportCone610.sigmaB ?_
      refine ⟨hload, hBne, Or.inl hCz, Or.inr (by omega), Or.inr (by omega)⟩
    · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
      · -- E ties B
        refine CubicLoadSigmaSupportCone610.sigmaBE ?_
        refine ⟨hload, hBne, hEne, by omega, Or.inl hCz, Or.inr (by omega)⟩
      · -- E strictly outranks B
        refine CubicLoadSigmaSupportCone610.sigmaE ?_
        refine ⟨hload, hEne, Or.inr (by omega), Or.inl hCz, Or.inr (by omega)⟩
  · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
    · -- D ties B
      by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
      · -- B strictly outranks E (smaller τ)
        refine CubicLoadSigmaSupportCone610.sigmaBD ?_
        refine ⟨hload, hBne, hDne, by omega, Or.inl hCz, Or.inr (by omega)⟩
      · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
        · -- E ties BD
          refine CubicLoadSigmaSupportCone610.sigmaBDE ?_
          refine ⟨hload, hBne, hDne, hEne, by omega, by omega, Or.inl hCz⟩
        · -- E strictly outranks BD
          refine CubicLoadSigmaSupportCone610.sigmaE ?_
          refine ⟨hload, hEne, Or.inr (by omega), Or.inl hCz, Or.inr (by omega)⟩
    · -- D strictly outranks B
      by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      · -- D strictly outranks E (smaller τ)
        refine CubicLoadSigmaSupportCone610.sigmaD ?_
        refine ⟨hload, hDne, Or.inr (by omega), Or.inl hCz, Or.inr (by omega)⟩
      · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
        · -- E ties D
          refine CubicLoadSigmaSupportCone610.sigmaDE ?_
          refine ⟨hload, hDne, hEne, by omega, Or.inr (by omega), Or.inl hCz⟩
        · -- E strictly outranks D
          refine CubicLoadSigmaSupportCone610.sigmaE ?_
          refine ⟨hload, hEne, Or.inr (by omega), Or.inl hCz, Or.inr (by omega)⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_BC
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hDdeg0 : D.natDegree = 0 := by simp [hDz]
  have hEdeg0 : E.natDegree = 0 := by simp [hEz]
  by_cases hlt : 2 * C.natDegree < A.natDegree + 2 * B.natDegree
  · -- B strictly outranks C (smaller τ)
    refine CubicLoadSigmaSupportCone610.sigmaB ?_
    refine ⟨hload, hBne, Or.inr (by omega), Or.inl hDz, Or.inl hEz⟩
  · by_cases heq : 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    · -- C ties B
      refine CubicLoadSigmaSupportCone610.sigmaBC ?_
      refine ⟨hload, hBne, hCne, by omega, Or.inl hDz, Or.inl hEz⟩
    · -- C strictly outranks B
      refine CubicLoadSigmaSupportCone610.sigmaC ?_
      refine ⟨hload, hCne, Or.inr (by omega), Or.inl hDz, Or.inl hEz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_BCE
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hDdeg0 : D.natDegree = 0 := by simp [hDz]
  by_cases hlt : 2 * C.natDegree < A.natDegree + 2 * B.natDegree
  · -- B strictly outranks C (smaller τ)
    by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
    · -- B strictly outranks E (smaller τ)
      refine CubicLoadSigmaSupportCone610.sigmaB ?_
      refine ⟨hload, hBne, Or.inr (by omega), Or.inl hDz, Or.inr (by omega)⟩
    · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
      · -- E ties B
        refine CubicLoadSigmaSupportCone610.sigmaBE ?_
        refine ⟨hload, hBne, hEne, by omega, Or.inr (by omega), Or.inl hDz⟩
      · -- E strictly outranks B
        refine CubicLoadSigmaSupportCone610.sigmaE ?_
        refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inl hDz⟩
  · by_cases heq : 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    · -- C ties B
      by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
      · -- B strictly outranks E (smaller τ)
        refine CubicLoadSigmaSupportCone610.sigmaBC ?_
        refine ⟨hload, hBne, hCne, by omega, Or.inl hDz, Or.inr (by omega)⟩
      · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
        · -- E ties BC
          refine CubicLoadSigmaSupportCone610.sigmaBCE ?_
          refine ⟨hload, hBne, hCne, hEne, by omega, by omega, Or.inl hDz⟩
        · -- E strictly outranks BC
          refine CubicLoadSigmaSupportCone610.sigmaE ?_
          refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inl hDz⟩
    · -- C strictly outranks B
      by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
      · -- C strictly outranks E (smaller τ)
        refine CubicLoadSigmaSupportCone610.sigmaC ?_
        refine ⟨hload, hCne, Or.inr (by omega), Or.inl hDz, Or.inr (by omega)⟩
      · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
        · -- E ties C
          refine CubicLoadSigmaSupportCone610.sigmaCE ?_
          refine ⟨hload, hCne, hEne, by omega, Or.inr (by omega), Or.inl hDz⟩
        · -- E strictly outranks C
          refine CubicLoadSigmaSupportCone610.sigmaE ?_
          refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inl hDz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_BCD
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  have hEdeg0 : E.natDegree = 0 := by simp [hEz]
  by_cases hlt : 2 * C.natDegree < A.natDegree + 2 * B.natDegree
  · -- B strictly outranks C (smaller τ)
    by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
    · -- B strictly outranks D (smaller τ)
      refine CubicLoadSigmaSupportCone610.sigmaB ?_
      refine ⟨hload, hBne, Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
    · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
      · -- D ties B
        refine CubicLoadSigmaSupportCone610.sigmaBD ?_
        refine ⟨hload, hBne, hDne, by omega, Or.inr (by omega), Or.inl hEz⟩
      · -- D strictly outranks B
        refine CubicLoadSigmaSupportCone610.sigmaD ?_
        refine ⟨hload, hDne, Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
  · by_cases heq : 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    · -- C ties B
      by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
      · -- B strictly outranks D (smaller τ)
        refine CubicLoadSigmaSupportCone610.sigmaBC ?_
        refine ⟨hload, hBne, hCne, by omega, Or.inr (by omega), Or.inl hEz⟩
      · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
        · -- D ties BC
          refine CubicLoadSigmaSupportCone610.sigmaBCD ?_
          refine ⟨hload, hBne, hCne, hDne, by omega, by omega, Or.inl hEz⟩
        · -- D strictly outranks BC
          refine CubicLoadSigmaSupportCone610.sigmaD ?_
          refine ⟨hload, hDne, Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
    · -- C strictly outranks B
      by_cases hlt : A.natDegree + 2 * D.natDegree < 3 * C.natDegree
      · -- C strictly outranks D (smaller τ)
        refine CubicLoadSigmaSupportCone610.sigmaC ?_
        refine ⟨hload, hCne, Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
      · by_cases heq : A.natDegree + 2 * D.natDegree = 3 * C.natDegree
        · -- D ties C
          refine CubicLoadSigmaSupportCone610.sigmaCD ?_
          refine ⟨hload, hCne, hDne, by omega, Or.inr (by omega), Or.inl hEz⟩
        · -- D strictly outranks C
          refine CubicLoadSigmaSupportCone610.sigmaD ?_
          refine ⟨hload, hDne, Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of_live_BCDE
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  have ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩ := hload
  by_cases hlt : 2 * C.natDegree < A.natDegree + 2 * B.natDegree
  · -- B strictly outranks C (smaller τ)
    by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
    · -- B strictly outranks D (smaller τ)
      by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
      · -- B strictly outranks E (smaller τ)
        refine CubicLoadSigmaSupportCone610.sigmaB ?_
        refine ⟨hload, hBne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
        · -- E ties B
          refine CubicLoadSigmaSupportCone610.sigmaBE ?_
          refine ⟨hload, hBne, hEne, by omega, Or.inr (by omega), Or.inr (by omega)⟩
        · -- E strictly outranks B
          refine CubicLoadSigmaSupportCone610.sigmaE ?_
          refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
    · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
      · -- D ties B
        by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
        · -- B strictly outranks E (smaller τ)
          refine CubicLoadSigmaSupportCone610.sigmaBD ?_
          refine ⟨hload, hBne, hDne, by omega, Or.inr (by omega), Or.inr (by omega)⟩
        · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
          · -- E ties BD
            refine CubicLoadSigmaSupportCone610.sigmaBDE ?_
            refine ⟨hload, hBne, hDne, hEne, by omega, by omega, Or.inr (by omega)⟩
          · -- E strictly outranks BD
            refine CubicLoadSigmaSupportCone610.sigmaE ?_
            refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- D strictly outranks B
        by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
        · -- D strictly outranks E (smaller τ)
          refine CubicLoadSigmaSupportCone610.sigmaD ?_
          refine ⟨hload, hDne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
          · -- E ties D
            refine CubicLoadSigmaSupportCone610.sigmaDE ?_
            refine ⟨hload, hDne, hEne, by omega, Or.inr (by omega), Or.inr (by omega)⟩
          · -- E strictly outranks D
            refine CubicLoadSigmaSupportCone610.sigmaE ?_
            refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
  · by_cases heq : 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    · -- C ties B
      by_cases hlt : 4 * D.natDegree < A.natDegree + 6 * B.natDegree
      · -- B strictly outranks D (smaller τ)
        by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
        · -- B strictly outranks E (smaller τ)
          refine CubicLoadSigmaSupportCone610.sigmaBC ?_
          refine ⟨hload, hBne, hCne, by omega, Or.inr (by omega), Or.inr (by omega)⟩
        · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
          · -- E ties BC
            refine CubicLoadSigmaSupportCone610.sigmaBCE ?_
            refine ⟨hload, hBne, hCne, hEne, by omega, by omega, Or.inr (by omega)⟩
          · -- E strictly outranks BC
            refine CubicLoadSigmaSupportCone610.sigmaE ?_
            refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · by_cases heq : 4 * D.natDegree = A.natDegree + 6 * B.natDegree
        · -- D ties BC
          by_cases hlt : 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree
          · -- B strictly outranks E (smaller τ)
            refine CubicLoadSigmaSupportCone610.sigmaBCD ?_
            refine ⟨hload, hBne, hCne, hDne, by omega, by omega, Or.inr (by omega)⟩
          · by_cases heq : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree
            · -- E ties BCD
              refine CubicLoadSigmaSupportCone610.sigmaBCDE ?_
              refine ⟨hload, hBne, hCne, hDne, hEne, by omega, by omega, by omega⟩
            · -- E strictly outranks BCD
              refine CubicLoadSigmaSupportCone610.sigmaE ?_
              refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- D strictly outranks BC
          by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
          · -- D strictly outranks E (smaller τ)
            refine CubicLoadSigmaSupportCone610.sigmaD ?_
            refine ⟨hload, hDne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
            · -- E ties D
              refine CubicLoadSigmaSupportCone610.sigmaDE ?_
              refine ⟨hload, hDne, hEne, by omega, Or.inr (by omega), Or.inr (by omega)⟩
            · -- E strictly outranks D
              refine CubicLoadSigmaSupportCone610.sigmaE ?_
              refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
    · -- C strictly outranks B
      by_cases hlt : A.natDegree + 2 * D.natDegree < 3 * C.natDegree
      · -- C strictly outranks D (smaller τ)
        by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
        · -- C strictly outranks E (smaller τ)
          refine CubicLoadSigmaSupportCone610.sigmaC ?_
          refine ⟨hload, hCne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
          · -- E ties C
            refine CubicLoadSigmaSupportCone610.sigmaCE ?_
            refine ⟨hload, hCne, hEne, by omega, Or.inr (by omega), Or.inr (by omega)⟩
          · -- E strictly outranks C
            refine CubicLoadSigmaSupportCone610.sigmaE ?_
            refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · by_cases heq : A.natDegree + 2 * D.natDegree = 3 * C.natDegree
        · -- D ties C
          by_cases hlt : 2 * E.natDegree < 3 * C.natDegree
          · -- C strictly outranks E (smaller τ)
            refine CubicLoadSigmaSupportCone610.sigmaCD ?_
            refine ⟨hload, hCne, hDne, by omega, Or.inr (by omega), Or.inr (by omega)⟩
          · by_cases heq : 2 * E.natDegree = 3 * C.natDegree
            · -- E ties CD
              refine CubicLoadSigmaSupportCone610.sigmaCDE ?_
              refine ⟨hload, hCne, hDne, hEne, by omega, by omega, Or.inr (by omega)⟩
            · -- E strictly outranks CD
              refine CubicLoadSigmaSupportCone610.sigmaE ?_
              refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- D strictly outranks C
          by_cases hlt : 2 * E.natDegree < A.natDegree + 2 * D.natDegree
          · -- D strictly outranks E (smaller τ)
            refine CubicLoadSigmaSupportCone610.sigmaD ?_
            refine ⟨hload, hDne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · by_cases heq : 2 * E.natDegree = A.natDegree + 2 * D.natDegree
            · -- E ties D
              refine CubicLoadSigmaSupportCone610.sigmaDE ?_
              refine ⟨hload, hDne, hEne, by omega, Or.inr (by omega), Or.inr (by omega)⟩
            · -- E strictly outranks D
              refine CubicLoadSigmaSupportCone610.sigmaE ?_
              refine ⟨hload, hEne, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaSupportCone610_of
    (A B C D E : k[X])
    (hload : cubicLoadCompetes610 A B C D E) :
    CubicLoadSigmaSupportCone610 A B C D E := by
  by_cases hBz : B = 0
  · -- B vanishes
    by_cases hCz : C = 0
    · -- C vanishes
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          exact cubicLoadSigmaSupportCone610_of_allZero A B C D E hload hBz hCz hDz hEz
        · -- E lives
          exact cubicLoadSigmaSupportCone610_of_live_E A B C D E hload hBz hCz hDz hEz
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          exact cubicLoadSigmaSupportCone610_of_live_D A B C D E hload hBz hCz hDz hEz
        · -- E lives
          exact cubicLoadSigmaSupportCone610_of_live_DE A B C D E hload hBz hCz hDz hEz
    · -- C lives
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          exact cubicLoadSigmaSupportCone610_of_live_C A B C D E hload hBz hCz hDz hEz
        · -- E lives
          exact cubicLoadSigmaSupportCone610_of_live_CE A B C D E hload hBz hCz hDz hEz
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          exact cubicLoadSigmaSupportCone610_of_live_CD A B C D E hload hBz hCz hDz hEz
        · -- E lives
          exact cubicLoadSigmaSupportCone610_of_live_CDE A B C D E hload hBz hCz hDz hEz
  · -- B lives
    by_cases hCz : C = 0
    · -- C vanishes
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          exact cubicLoadSigmaSupportCone610_of_live_B A B C D E hload hBz hCz hDz hEz
        · -- E lives
          exact cubicLoadSigmaSupportCone610_of_live_BE A B C D E hload hBz hCz hDz hEz
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          exact cubicLoadSigmaSupportCone610_of_live_BD A B C D E hload hBz hCz hDz hEz
        · -- E lives
          exact cubicLoadSigmaSupportCone610_of_live_BDE A B C D E hload hBz hCz hDz hEz
    · -- C lives
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          exact cubicLoadSigmaSupportCone610_of_live_BC A B C D E hload hBz hCz hDz hEz
        · -- E lives
          exact cubicLoadSigmaSupportCone610_of_live_BCE A B C D E hload hBz hCz hDz hEz
      · -- D lives
        by_cases hEz : E = 0
        · -- E vanishes
          exact cubicLoadSigmaSupportCone610_of_live_BCD A B C D E hload hBz hCz hDz hEz
        · -- E lives
          exact cubicLoadSigmaSupportCone610_of_live_BCDE A B C D E hload hBz hCz hDz hEz

end CubicLoadSigmaCones610

/-! ## §3.6 Degenerate corner `B = D = 0` -/

section CubicLoadCompeteBDZero610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem cubicLoadCompete_BD_zero_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hB : B = 0) (hD : D = 0) (hl : l = 0)
    (hbeta : beta = 0) (hdelta : delta = 0) (hzeta : zeta = 0)
    (htheta : theta = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E) =
        Polynomial.C (j / t)) : False := by
  rw [degreeZeroPrimitiveCubic610_eq_flat] at hder
  subst hB; subst hD; subst hl; subst hbeta; subst hdelta; subst hzeta
  subst htheta
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  simp only [degreeZeroPrimitiveCubicFlat610, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    neg_zero, sub_self, derivative_zero] at hder
  exact hjdiv (by simpa using (Polynomial.C_eq_zero.mp hder.symm))

end CubicLoadCompeteBDZero610

/-! ## Residual 6 -/

section CubicLoadLadderAssembly610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Honest leftover after the N₁ ladder predicates, the load-compete
σ-argmin exhaust, and the `B = D = 0` Pi identity.

Closed relative to residual 5: the four N₁ column implications
`cubicN1{Beta,Delta,Zeta,Theta}Top610 → {β,δ,ζ,θ} = 0`, the four
cleared band disjunctions, and `CubicLoadSigmaSupportCone610`.  The
15 cones are not killed here (Files B/C).  Next unused row: per-cone
letter-face rest bounds on the load-compete side.  No finite-root
shortcut is used. -/
theorem normalized610ScaleZero_cubicResidual6
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C D E : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
            eta theta A B C D E) =
        Polynomial.C (j / t) ∧
      (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      CubicRatioConeA610 A B C D E ∧
      cubicLoadCompetes610 A B C D E ∧
      l = 0 ∧
      (cubicKappaBetaTop610 A B C D E → beta = 0) ∧
      (cubicKappaDeltaTop610 A B C D E → delta = 0) ∧
      (cubicKappaZetaTop610 A B C D E → zeta = 0) ∧
      (cubicN1BetaTop610 A B C D E → beta = 0) ∧
      (cubicN1DeltaTop610 A B C D E → delta = 0) ∧
      (cubicN1ZetaTop610 A B C D E → zeta = 0) ∧
      (cubicN1ThetaTop610 A B C D E → theta = 0) ∧
      (beta = 0 ∨
        7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree) ∧
      (delta = 0 ∨
        7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree) ∧
      (zeta = 0 ∨
        9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
        12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
        10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
        12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree) ∧
      (theta = 0 ∨
        7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree) ∧
      CubicLoadSigmaSupportCone610 A B C D E := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
      hload, hl0, hkapB, hkapD, hkapZ⟩ :=
    normalized610ScaleZero_cubicResidual5 hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA, hload,
    hl0, hkapB, hkapD, hkapZ, ?hbN1, ?hdN1, ?hzN1, ?htN1, ?hbBand, ?hdBand,
    ?hzBand, ?htBand, ?hexh⟩
  · intro htop
    exact cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
      A B C D E htop hl0 hmuDeg hkapDeg
  · intro htop
    exact cubicN1_delta_eq_zero l alpha beta delta epsilon zeta eta theta
      A B C D E htop hl0
      (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
        A B C D E (cubicN1DeltaTop610_to_betaTop htop) hl0 hmuDeg hkapDeg)
      hmuDeg hkapDeg
  · intro htop
    exact cubicN1_zeta_eq_zero l alpha beta delta epsilon zeta eta theta
      A B C D E htop hl0
      (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
        A B C D E (cubicN1ZetaTop610_to_betaTop htop) hl0 hmuDeg hkapDeg)
      (cubicN1_delta_eq_zero l alpha beta delta epsilon zeta eta theta
        A B C D E (cubicN1ZetaTop610_to_deltaTop htop) hl0
        (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
          A B C D E (cubicN1ZetaTop610_to_betaTop htop) hl0 hmuDeg hkapDeg)
        hmuDeg hkapDeg)
      hmuDeg hkapDeg
  · intro htop
    exact cubicN1_theta_eq_zero l alpha beta delta epsilon zeta eta theta
      A B C D E htop hl0
      (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
        A B C D E (cubicN1ThetaTop610_to_betaTop htop) hl0 hmuDeg hkapDeg)
      (cubicN1_delta_eq_zero l alpha beta delta epsilon zeta eta theta
        A B C D E (cubicN1ThetaTop610_to_deltaTop htop) hl0
        (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
          A B C D E (cubicN1ThetaTop610_to_betaTop htop) hl0 hmuDeg hkapDeg)
        hmuDeg hkapDeg)
      (cubicN1_zeta_eq_zero l alpha beta delta epsilon zeta eta theta
        A B C D E (cubicN1ThetaTop610_to_zetaTop htop) hl0
        (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
          A B C D E (cubicN1ThetaTop610_to_betaTop htop) hl0 hmuDeg hkapDeg)
        (cubicN1_delta_eq_zero l alpha beta delta epsilon zeta eta theta
          A B C D E (cubicN1ThetaTop610_to_deltaTop htop) hl0
          (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
            A B C D E (cubicN1ThetaTop610_to_betaTop htop) hl0 hmuDeg
              hkapDeg)
          hmuDeg hkapDeg)
        hmuDeg hkapDeg)
      hmuDeg hkapDeg
  · exact cubicN1_beta_band_disjunction A B C D E hload
      (fun htop => cubicN1_beta_eq_zero l alpha beta delta epsilon zeta
        eta theta A B C D E htop hl0 hmuDeg hkapDeg)
  · exact cubicN1_delta_band_disjunction A B C D E hload
      (fun htop => cubicN1_delta_eq_zero l alpha beta delta epsilon zeta
        eta theta A B C D E htop hl0
        (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
          A B C D E (cubicN1DeltaTop610_to_betaTop htop) hl0 hmuDeg
            hkapDeg)
        hmuDeg hkapDeg)
  · exact cubicN1_zeta_band_disjunction A B C D E hload
      (fun htop => cubicN1_zeta_eq_zero l alpha beta delta epsilon zeta
        eta theta A B C D E htop hl0
        (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
          A B C D E (cubicN1ZetaTop610_to_betaTop htop) hl0 hmuDeg hkapDeg)
        (cubicN1_delta_eq_zero l alpha beta delta epsilon zeta eta theta
          A B C D E (cubicN1ZetaTop610_to_deltaTop htop) hl0
          (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
            A B C D E (cubicN1ZetaTop610_to_betaTop htop) hl0 hmuDeg
              hkapDeg)
          hmuDeg hkapDeg)
        hmuDeg hkapDeg)
  · exact cubicN1_theta_band_disjunction A B C D E hload
      (fun htop => cubicN1_theta_eq_zero l alpha beta delta epsilon zeta
        eta theta A B C D E htop hl0
        (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
          A B C D E (cubicN1ThetaTop610_to_betaTop htop) hl0 hmuDeg
            hkapDeg)
        (cubicN1_delta_eq_zero l alpha beta delta epsilon zeta eta theta
          A B C D E (cubicN1ThetaTop610_to_deltaTop htop) hl0
          (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
            A B C D E (cubicN1ThetaTop610_to_betaTop htop) hl0 hmuDeg
              hkapDeg)
          hmuDeg hkapDeg)
        (cubicN1_zeta_eq_zero l alpha beta delta epsilon zeta eta theta
          A B C D E (cubicN1ThetaTop610_to_zetaTop htop) hl0
          (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta theta
            A B C D E (cubicN1ThetaTop610_to_betaTop htop) hl0 hmuDeg
              hkapDeg)
          (cubicN1_delta_eq_zero l alpha beta delta epsilon zeta eta theta
            A B C D E (cubicN1ThetaTop610_to_deltaTop htop) hl0
            (cubicN1_beta_eq_zero l alpha beta delta epsilon zeta eta
              theta A B C D E (cubicN1ThetaTop610_to_betaTop htop) hl0
              hmuDeg hkapDeg)
            hmuDeg hkapDeg)
          hmuDeg hkapDeg)
        hmuDeg hkapDeg)
  · exact cubicLoadSigmaSupportCone610_of A B C D E hload

end CubicLoadLadderAssembly610

#print axioms degreeZeroN1CubicNoLNoBetaA5610_natDegree_lt_of_N1BetaTop
#print axioms cubicN1_beta_eq_zero
#print axioms cubicN1_delta_eq_zero
#print axioms cubicN1_zeta_eq_zero
#print axioms cubicN1_theta_eq_zero
#print axioms cubicLoadSigmaSupportCone610_of
#print axioms cubicLoadCompete_BD_zero_impossible
#print axioms normalized610ScaleZero_cubicResidual6

end Max11DegreeRoutes
