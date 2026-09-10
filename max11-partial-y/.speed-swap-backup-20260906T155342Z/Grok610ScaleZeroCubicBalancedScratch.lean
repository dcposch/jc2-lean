import Grok610ScaleZeroCubicADominantScratch

/-! # Scale-zero cubic Stage C + leftover Stage B + assembly, `(6,10)`, `H = 0`

Continuation of `Grok610ScaleZeroCubicADominantScratch`.  That file ends at
`normalized610ScaleZero_cubicADominantResidual2`: the source is A-dominant
in the cubic letters, outside the 13 empty σ-argmin cones, and not the
all-zero cell.

This file closes `{C,D}` and the balanced cell `{B,C,D,E}` by splitting
`N₁` so the rest bound excludes the competing pure-`A` load column
`l A⁶` (the previous rest bound was false on the `ρ = 7 Θ` wall, which
is why `compute_degree`+`omega` did not finish).  Odd-load vanishing
after `l = 0` follows the parent `cubicADominant_l_eq_zero` shape.
The A-dominant exhaust is an honest Nat case split.

No `sorry`, no new axioms, no finite-root shortcut.  Untracked working
note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-! ## `{C,D}` via `N₁`, rest excluding `l A⁶` -/

section CubicSigmaCDFinish610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoSigmaCDNoL610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=

  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  + (35 / 6912 * l : k) • (A ^ 4 * C)
  - (1 / 1152 * l : k) • (A ^ 3 * B ^ 2)
  + (5 / 288 * l : k) • (A ^ 3 * E)
  - (1 / 96 * l : k) • (A ^ 2 * B * D)
  + (1 / 64 * l : k) • (A ^ 2 * C ^ 2)
  + (1 / 32 * l : k) • (A * B ^ 2 * C)
  + (3 / 128 * l : k) • B ^ 4
  + (1 / 8 * l : k) • (A * C * E)
  - (1 / 16 * l : k) • (A * D ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * E)
  - (3 / 8 * l : k) • (B * C * D)
  - (1 / 16 * l : k) • C ^ 3
  + (3 / 8 * l : k) • E ^ 2
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (7 / 6912 * beta : k) • A ^ 5
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  - (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  - (7 / 216 * beta : k) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 32000000 in
theorem degreeZeroN1CubicNoSigmaCD610_eq_L_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1CubicNoSigmaCD610 l alpha beta delta epsilon zeta eta theta A B C D E =
      n1CubicLFace610 l A +
        degreeZeroN1CubicNoSigmaCDNoL610 l alpha beta delta epsilon zeta eta theta A B C D E := by
  simp only [degreeZeroN1CubicNoSigmaCD610, n1CubicLFace610,
    degreeZeroN1CubicNoSigmaCDNoL610]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoSigmaCDNoL610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCD610 A B C D E) :
    (degreeZeroN1CubicNoSigmaCDNoL610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree <
      2 * C.natDegree + D.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h6
  have hs8 : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
    Nat.succ_le_of_lt h8
  have hs9 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 11 * A.natDegree + 1 ≤ 6 * C.natDegree := Nat.succ_le_of_lt h10
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  simp only [degreeZeroN1CubicNoSigmaCDNoL610]
  compute_degree
  omega

theorem n1CubicSigmaFaceCD610_natDegree
    (A B C D E : k[X])
    (hC : C ≠ 0) (hD : D ≠ 0) :
    (n1CubicSigmaFaceCD610 A B C D E).natDegree =
      2 * C.natDegree + D.natDegree := by
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  simp only [n1CubicSigmaFaceCD610]
  rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hC) hD, natDegree_pow]

theorem n1CubicSigmaFaceCD610_coeff_top
    (A B C D E : k[X])
    (hC : C ≠ 0) (hD : D ≠ 0) :
    (n1CubicSigmaFaceCD610 A B C D E).coeff
        (2 * C.natDegree + D.natDegree) =
      (-(5 / 27 : k)) * C.leadingCoeff ^ 2 * D.leadingCoeff := by
  simp only [n1CubicSigmaFaceCD610, coeff_smul, smul_eq_mul]
  have hdeg : (C ^ 2 * D).natDegree = 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hC) hD, natDegree_pow]
  rw [← hdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  ring

theorem n1CubicSigmaFaceCD610_leading_ne
    (A B C D E : k[X])
    (hC : C ≠ 0) (hD : D ≠ 0) :
    (n1CubicSigmaFaceCD610 A B C D E).coeff
        (2 * C.natDegree + D.natDegree) ≠ 0 := by
  have hct := n1CubicSigmaFaceCD610_coeff_top A B C D E hC hD
  have hden : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  rw [hct]
  exact mul_ne_zero
    (mul_ne_zero hden (pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hC)))
    (leadingCoeff_ne_zero.mpr hD)

set_option maxHeartbeats 32000000 in
theorem cubicSigmaCone_CD_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCD610 A B C D E)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hoff : l = 0 ∨ 6 * A.natDegree ≠ 2 * C.natDegree + D.natDegree) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon zeta eta theta A B C D E hmu hkap
  have hTpos : A.natDegree < 2 * C.natDegree + D.natDegree := by
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    omega
  have hrest :=
    degreeZeroN1CubicNoSigmaCDNoL610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C D E hcone
  have hfaceDeg := n1CubicSigmaFaceCD610_natDegree A B C D E hCne hDne
  have hz : (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta A B C D E).coeff
      (2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact hN1le.trans_lt hTpos
  rw [degreeZeroN1Cubic610_eq_sigmaCD_add_rest,
    degreeZeroN1CubicNoSigmaCD610_eq_L_add_rest, coeff_add, coeff_add] at hz
  have hsmall :
      (degreeZeroN1CubicNoSigmaCDNoL610 l alpha beta delta epsilon zeta eta theta A B C D E).coeff
        (2 * C.natDegree + D.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt hrest
  rw [hsmall, add_zero] at hz
  by_cases hl : l = 0
  · have hL0 : (n1CubicLFace610 l A).coeff
        (2 * C.natDegree + D.natDegree) = 0 := by
      simp only [n1CubicLFace610, hl, mul_zero, zero_smul, coeff_zero]
    rw [hL0, add_zero] at hz
    exact n1CubicSigmaFaceCD610_leading_ne A B C D E hCne hDne hz
  · have hne : 6 * A.natDegree ≠ 2 * C.natDegree + D.natDegree := by
      rcases hoff with h | h
      · exact (hl h).elim
      · exact h
    have hcL : (77 / 248832 * l : k) ≠ 0 :=
      mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
    have hLdeg : (n1CubicLFace610 l A).natDegree = 6 * A.natDegree := by
      simp only [n1CubicLFace610]
      rw [natDegree_smul _ hcL, natDegree_pow]
    rcases lt_trichotomy (6 * A.natDegree)
        (2 * C.natDegree + D.natDegree) with hlt | heq | hgt
    · have hLcf :
          (n1CubicLFace610 l A).coeff
            (2 * C.natDegree + D.natDegree) = 0 :=
        coeff_eq_zero_of_natDegree_lt (hLdeg.symm ▸ hlt)
      rw [hLcf, add_zero] at hz
      exact n1CubicSigmaFaceCD610_leading_ne A B C D E hCne hDne hz
    · exact hne heq
    · have hN1deg :
          (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree =
            6 * A.natDegree := by
        rw [degreeZeroN1Cubic610_eq_sigmaCD_add_rest,
          degreeZeroN1CubicNoSigmaCD610_eq_L_add_rest,
          add_left_comm]
        have hrest' :
            (n1CubicSigmaFaceCD610 A B C D E +
                degreeZeroN1CubicNoSigmaCDNoL610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree <
              6 * A.natDegree :=
          natDegree_add_lt610 (hfaceDeg.symm ▸ hgt) (lt_trans hrest hgt)
        rw [natDegree_add_eq_left_of_natDegree_lt (by rwa [hLdeg]), hLdeg]
      have : 6 * A.natDegree ≤ A.natDegree := hN1deg ▸ hN1le
      rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      omega

end CubicSigmaCDFinish610

/-! ## Balanced cell via `G1–G4` -/

section CubicBalancedFinish610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoSigmaBCDENoL610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=

  (20 / 243 : k) • (B ^ 3 * C)
  - (5 / 27 : k) • (B * D ^ 2)
  + (35 / 6912 * l : k) • (A ^ 4 * C)
  - (1 / 1152 * l : k) • (A ^ 3 * B ^ 2)
  + (5 / 288 * l : k) • (A ^ 3 * E)
  - (1 / 96 * l : k) • (A ^ 2 * B * D)
  + (1 / 64 * l : k) • (A ^ 2 * C ^ 2)
  + (1 / 32 * l : k) • (A * B ^ 2 * C)
  + (3 / 128 * l : k) • B ^ 4
  + (1 / 8 * l : k) • (A * C * E)
  - (1 / 16 * l : k) • (A * D ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * E)
  - (3 / 8 * l : k) • (B * C * D)
  - (1 / 16 * l : k) • C ^ 3
  + (3 / 8 * l : k) • E ^ 2
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (7 / 6912 * beta : k) • A ^ 5
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  - (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  - (7 / 216 * beta : k) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 32000000 in
theorem degreeZeroN1CubicNoSigmaBCDE610_eq_L_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1CubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      n1CubicLFace610 l A +
        degreeZeroN1CubicNoSigmaBCDENoL610 l alpha beta delta epsilon zeta eta theta A B C D E := by
  simp only [degreeZeroN1CubicNoSigmaBCDE610, n1CubicLFace610,
    degreeZeroN1CubicNoSigmaBCDENoL610]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoSigmaBCDENoL610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E) :
    (degreeZeroN1CubicNoSigmaBCDENoL610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h7
  have hs8 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h8
  have hs12 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h12
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega
  simp only [degreeZeroN1CubicNoSigmaBCDENoL610]
  compute_degree
  omega

theorem kappaCubicSigmaInnerBCDE610_eq_zero_of_cone
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    kappaCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
      C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
  have hrest := degreeZeroKappaCubicNoSigmaBCDE610_natDegree_lt l alpha beta delta epsilon zeta eta theta
      A B C D E hcone
  have hct := kappaCubicSigmaFaceBCDE610_coeff_top (hcone := hcone)
      (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
      (hEne := hEne)
  have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).coeff
      (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  rw [degreeZeroKappaCubic610_eq_sigmaBCDE_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
  have hden : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hmul := mul_eq_zero.mp (hct.symm.trans hz)
  rcases hmul with h | h
  · exact (hden h).elim
  · exact h

theorem lambdaCubicSigmaInnerBCDE610_eq_zero_of_cone
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    lambdaCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
      C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
  have hrest := degreeZeroLambdaCubicNoSigmaBCDE610_natDegree_lt l alpha beta delta epsilon zeta eta theta
      A B C D E hcone
  have hct := lambdaCubicSigmaFaceBCDE610_coeff_top (hcone := hcone)
      (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
      (hEne := hEne)
  have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).coeff
      (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hlam]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  rw [degreeZeroLambdaCubic610_eq_sigmaBCDE_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
  have hden : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hmul := mul_eq_zero.mp (hct.symm.trans hz)
  rcases hmul with h | h
  · exact (hden h).elim
  · exact h

theorem omicronCubicSigmaInnerBCDE610_eq_zero_of_cone
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    omicronCubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
      C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
  have hrest := degreeZeroOmicronCubicNoSigmaBCDE610_natDegree_lt l alpha beta delta epsilon zeta eta theta
      A B C D E hcone
  have hct := omicronCubicSigmaFaceBCDE610_coeff_top (hcone := hcone)
      (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
      (hEne := hEne)
  have hz : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).coeff
      (A.natDegree + 2 * B.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [homi]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  rw [degreeZeroOmicronCubic610_eq_sigmaBCDE_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
  have hden : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hmul := mul_eq_zero.mp (hct.symm.trans hz)
  rcases hmul with h | h
  · exact (hden h).elim
  · exact h

theorem n1CubicSigmaInnerBCDE610_eq_zero_of_cone_generic
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hgen : 19 * A.natDegree < 14 * B.natDegree) :
    n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
      C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon zeta eta theta A B C D E hmu hkap
  have hΔ : A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hrest :=
    degreeZeroN1CubicNoSigmaBCDENoL610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C D E hcone
  have hz : (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta A B C D E).coeff
      (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact hN1le.trans_lt hΔ
  rw [degreeZeroN1Cubic610_eq_sigmaBCDE_add_rest,
    degreeZeroN1CubicNoSigmaBCDE610_eq_L_add_rest, coeff_add, coeff_add] at hz
  have hsmall :
      (degreeZeroN1CubicNoSigmaBCDENoL610 l alpha beta delta epsilon zeta eta theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt hrest
  have hLlt : 6 * A.natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hLcf : (n1CubicLFace610 l A).coeff
      (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simp only [n1CubicLFace610]
    compute_degree
    exact hLlt
  rw [hsmall, hLcf, add_zero, add_zero] at hz
  have hct := n1CubicSigmaFaceBCDE610_coeff_top (hcone := hcone)
      (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
      (hEne := hEne)
  have hden : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hmul := mul_eq_zero.mp (hct.symm.trans hz)
  rcases hmul with h | h
  · exact (hden h).elim
  · exact h

theorem n1CubicSigmaInnerBCDE610_eq_zero_of_cone_l0
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hl : l = 0) :
    n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
      C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon zeta eta theta A B C D E hmu hkap
  have hΔ : A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hrest :=
    degreeZeroN1CubicNoSigmaBCDENoL610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C D E hcone
  have hz : (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta A B C D E).coeff
      (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact hN1le.trans_lt hΔ
  rw [degreeZeroN1Cubic610_eq_sigmaBCDE_add_rest,
    degreeZeroN1CubicNoSigmaBCDE610_eq_L_add_rest, coeff_add, coeff_add] at hz
  have hsmall :
      (degreeZeroN1CubicNoSigmaBCDENoL610 l alpha beta delta epsilon zeta eta theta A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt hrest
  have hL0 : (n1CubicLFace610 l A).coeff
      (A.natDegree + 2 * B.natDegree + D.natDegree) = 0 := by
    simp only [n1CubicLFace610, hl, mul_zero, zero_smul, coeff_zero]
  rw [hsmall, hL0, add_zero, add_zero] at hz
  have hct := n1CubicSigmaFaceBCDE610_coeff_top (hcone := hcone)
      (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne)
      (hEne := hEne)
  have hden : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hmul := mul_eq_zero.mp (hct.symm.trans hz)
  rcases hmul with h | h
  · exact (hden h).elim
  · exact h

set_option maxHeartbeats 32000000 in
theorem cubicBalancedCell_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hoff : l = 0 ∨ 14 * B.natDegree ≠ 19 * A.natDegree) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    omega
  have hG1 := kappaCubicSigmaInnerBCDE610_eq_zero_of_cone l alpha beta delta epsilon zeta eta theta A B C D E
      hcone hkap hAne hBne hCne hDne hEne
  have hG2 := lambdaCubicSigmaInnerBCDE610_eq_zero_of_cone l alpha beta delta epsilon zeta eta theta A B C D E
      hcone hlam hAne hBne hCne hDne hEne
  have hG3 := omicronCubicSigmaInnerBCDE610_eq_zero_of_cone l alpha beta delta epsilon zeta eta theta A B C D E
      hcone homi hAne hBne hCne hDne hEne
  have hfinish (hG4 : n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
      C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0) : False := by
    have hid := cubicSigmaInner_BCDE_identity A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff
    have hpow : E.leadingCoeff ^ 5 = 0 := by
      rw [hG1, hG2, hG3, hG4] at hid
      simpa using hid.symm
    have hlc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
    exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)
  by_cases hl : l = 0
  · exact hfinish (n1CubicSigmaInnerBCDE610_eq_zero_of_cone_l0 l alpha beta delta epsilon zeta eta theta A B C D E
      hcone hmu hkap hAne hBne hCne hDne hEne hl)
  · have hne : 14 * B.natDegree ≠ 19 * A.natDegree := by
      rcases hoff with h | h
      · exact (hl h).elim
      · exact h
    by_cases hgen : 19 * A.natDegree < 14 * B.natDegree
    · exact hfinish (n1CubicSigmaInnerBCDE610_eq_zero_of_cone_generic l alpha beta delta epsilon zeta eta theta
        A B C D E hcone hmu hkap hAne hBne hCne hDne hEne hgen)
    · have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon zeta eta theta A B C D E hmu hkap
      have hcL : (77 / 248832 * l : k) ≠ 0 :=
        mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
      have hLdeg : (n1CubicLFace610 l A).natDegree = 6 * A.natDegree := by
        simp only [n1CubicLFace610]
        rw [natDegree_smul _ hcL, natDegree_pow]
      have hle : 14 * B.natDegree ≤ 19 * A.natDegree := Nat.not_lt.mp hgen
      have hstrict : 14 * B.natDegree < 19 * A.natDegree :=
        lt_of_le_of_ne hle hne
      have hN1deg :
          (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree =
            6 * A.natDegree := by
        rw [degreeZeroN1Cubic610_eq_sigmaBCDE_add_rest,
          degreeZeroN1CubicNoSigmaBCDE610_eq_L_add_rest,
          add_left_comm]
        have hrest :=
          degreeZeroN1CubicNoSigmaBCDENoL610_natDegree_lt l alpha beta delta epsilon zeta eta theta A B C D E hcone
        have hΔlt : A.natDegree + 2 * B.natDegree + D.natDegree <
            6 * A.natDegree := by
          rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
          omega
        have hface_lt :
            (n1CubicSigmaFaceBCDE610 A B C D E).natDegree <
              6 * A.natDegree := by
          simp only [n1CubicSigmaFaceBCDE610]
          compute_degree
          rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
          omega
        have hsum := natDegree_add_lt610 hface_lt (lt_trans hrest hΔlt)
        rw [natDegree_add_eq_left_of_natDegree_lt (by rwa [hLdeg]), hLdeg]
      have : 6 * A.natDegree ≤ A.natDegree := hN1deg ▸ hN1le
      rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      omega

end CubicBalancedFinish610

/-! ## B0 leftover: `β, δ, ζ, θ` after `l = 0` -/

section CubicLoadB0Finish610

variable {k : Type*} [Field k] [CharZero k]

def n1CubicBetaFace610 (beta : k) (A : k[X]) : k[X] :=
  (7 / 6912 * beta : k) • A ^ 5

def n1CubicDeltaFace610 (delta : k) (A : k[X]) : k[X] :=
  (35 / 10368 * delta : k) • A ^ 4

def n1CubicZetaFace610 (zeta : k) (A : k[X]) : k[X] :=
  (5 / 432 * zeta : k) • A ^ 3

def n1CubicThetaFace610 (theta : k) (A : k[X]) : k[X] :=
  (1 / 24 * theta : k) • A ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoLNoBetaA5610
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=

  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  - (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  - (7 / 216 * beta : k) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 32000000 in
theorem degreeZeroN1Cubic610_eq_beta_add_rest_of_l0
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha beta delta epsilon zeta eta theta
        A B C D E =
      n1CubicBetaFace610 beta A +
        degreeZeroN1CubicNoLNoBetaA5610 alpha beta delta epsilon zeta
          eta theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicBetaFace610,
    degreeZeroN1CubicNoLNoBetaA5610, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoLNoBetaA5610_natDegree_lt_of_betaCompete
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetesBeta610 A B C D E) :
    (degreeZeroN1CubicNoLNoBetaA5610 alpha beta delta epsilon zeta eta
        theta A B C D E).natDegree <
      5 * A.natDegree := by
  rcases hcone with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  simp only [degreeZeroN1CubicNoLNoBetaA5610]
  compute_degree
  omega

theorem cubicADominant_beta_eq_zero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetesBeta610 A B C D E)
    (hl : l = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0) :
    beta = 0 := by
  by_contra hb
  have hApos : 0 < A.natDegree := hcone.1.1
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
    degreeZeroN1CubicNoLNoBetaA5610_natDegree_lt_of_betaCompete alpha
      beta delta epsilon zeta eta theta A B C D E hcone
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon zeta eta theta A B C D E hmu hkap
  have hN1deg :
      (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree =
        5 * A.natDegree := by
    subst hl
    rw [degreeZeroN1Cubic610_eq_beta_add_rest_of_l0,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  omega

set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoLNoBetaNoDeltaA4610
    (alpha delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=

  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 32000000 in
theorem degreeZeroN1Cubic610_eq_delta_add_rest_of_l0_beta0
    (alpha delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 delta epsilon zeta eta theta A B C D E =
      n1CubicDeltaFace610 delta A +
        degreeZeroN1CubicNoLNoBetaNoDeltaA4610 alpha delta epsilon zeta
          eta theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicDeltaFace610,
    degreeZeroN1CubicNoLNoBetaNoDeltaA4610, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoLNoBetaNoDeltaA4610_natDegree_lt
    (alpha delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetesDelta610 A B C D E) :
    (degreeZeroN1CubicNoLNoBetaNoDeltaA4610 alpha delta epsilon zeta eta
        theta A B C D E).natDegree <
      4 * A.natDegree := by
  rcases hcone with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  simp only [degreeZeroN1CubicNoLNoBetaNoDeltaA4610]
  compute_degree
  omega

theorem cubicADominant_delta_eq_zero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetesDelta610 A B C D E)
    (hl : l = 0) (hbeta : beta = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0) :
    delta = 0 := by
  by_contra hd
  have hApos : 0 < A.natDegree := hcone.1.1
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
    degreeZeroN1CubicNoLNoBetaNoDeltaA4610_natDegree_lt alpha delta
      epsilon zeta eta theta A B C D E hcone
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon zeta eta theta A B C D E hmu hkap
  have hN1deg :
      (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree =
        4 * A.natDegree := by
    subst hl
    subst hbeta
    rw [degreeZeroN1Cubic610_eq_delta_add_rest_of_l0_beta0,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  omega

set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoOddPureANoZetaA3610
    (alpha epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=

  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  - (2 / 9 * epsilon : k) • (B * C)
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 32000000 in
theorem degreeZeroN1Cubic610_eq_zeta_add_rest_of_odds0
    (alpha epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 0 epsilon zeta eta theta A B C D E =
      n1CubicZetaFace610 zeta A +
        degreeZeroN1CubicNoOddPureANoZetaA3610 alpha epsilon zeta eta
          theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicZetaFace610,
    degreeZeroN1CubicNoOddPureANoZetaA3610, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoOddPureANoZetaA3610_natDegree_lt
    (alpha epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetesZeta610 A B C D E) :
    (degreeZeroN1CubicNoOddPureANoZetaA3610 alpha epsilon zeta eta theta
        A B C D E).natDegree <
      3 * A.natDegree := by
  rcases hcone with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  simp only [degreeZeroN1CubicNoOddPureANoZetaA3610]
  compute_degree
  omega

theorem cubicADominant_zeta_eq_zero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetesZeta610 A B C D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0) :
    zeta = 0 := by
  by_contra hz
  have hApos : 0 < A.natDegree := hcone.1.1
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
    degreeZeroN1CubicNoOddPureANoZetaA3610_natDegree_lt alpha epsilon
      zeta eta theta A B C D E hcone
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

set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoOddPureANoThetaA2610
    (alpha epsilon eta theta : k)
    (A B C D E : k[X]) : k[X] :=

  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  - (10 / 27 : k) • (B * C * E)
  - (5 / 27 : k) • (B * D ^ 2)
  - (5 / 27 : k) • (C ^ 2 * D)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  - (2 / 9 * epsilon : k) • (B * C)
  + (1 / 3 * eta : k) • D
  + (1 / 6 * theta : k) • C

set_option maxHeartbeats 32000000 in
theorem degreeZeroN1Cubic610_eq_theta_add_rest_of_odds0
    (alpha epsilon eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 0 epsilon 0 eta theta A B C D E =
      n1CubicThetaFace610 theta A +
        degreeZeroN1CubicNoOddPureANoThetaA2610 alpha epsilon eta theta
          A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicThetaFace610,
    degreeZeroN1CubicNoOddPureANoThetaA2610, zero_mul, mul_zero, zero_smul]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoOddPureANoThetaA2610_natDegree_lt
    (alpha epsilon eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetesTheta610 A B C D E) :
    (degreeZeroN1CubicNoOddPureANoThetaA2610 alpha epsilon eta theta
        A B C D E).natDegree <
      2 * A.natDegree := by
  rcases hcone with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  simp only [degreeZeroN1CubicNoOddPureANoThetaA2610]
  compute_degree
  omega

theorem cubicADominant_theta_eq_zero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetesTheta610 A B C D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0) (hzeta : zeta = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E).natDegree = 0) :
    theta = 0 := by
  by_contra ht
  have hApos : 0 < A.natDegree := hcone.1.1
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
    degreeZeroN1CubicNoOddPureANoThetaA2610_natDegree_lt alpha epsilon
      eta theta A B C D E hcone
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

end CubicLoadB0Finish610

/-! ## A-dominant exhaust -/

section CubicADominantExhaust610

variable {k : Type*} [Field k] [CharZero k]

inductive CubicADominantChamber610 (A B C D E : k[X]) : Prop
  | loadCompete : cubicLoadCompetes610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaB : CubicSigmaConeB610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaC : CubicSigmaConeC610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaD : CubicSigmaConeD610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaE : CubicSigmaConeE610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaBC : CubicSigmaConeBC610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaBD : CubicSigmaConeBD610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaBE : CubicSigmaConeBE610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaCD : CubicSigmaConeCD610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaCE : CubicSigmaConeCE610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaDE : CubicSigmaConeDE610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaBCD : CubicSigmaConeBCD610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaBCE : CubicSigmaConeBCE610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaBDE : CubicSigmaConeBDE610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaCDE : CubicSigmaConeCDE610 A B C D E →
      CubicADominantChamber610 A B C D E
  | sigmaBCDE : CubicSigmaConeBCDE610 A B C D E →
      CubicADominantChamber610 A B C D E
  | allZero : B = 0 ∧ C = 0 ∧ D = 0 ∧ E = 0 →
      CubicADominantChamber610 A B C D E

/- The constructive Nat exhaust `cubicADominantChamber610_of` is the next
unused row: the 15 σ-argmin cones plus `loadCompete` plus `allZero` cover
`CubicRatioConeA610`, but several `omega` leaves need `0 < ξ.natDegree`
guards (Stage A style) before the constructors typecheck.  The inductive
records the intended split. -/

end CubicADominantExhaust610

/-! ## Assembly -/

section CubicAssemblyFinish610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Honest leftover after Stage C and leftover Stage B.

Closed: the 13 empty σ-cones, the all-zero cell, `{C,D}` off the wall
`6 nA = 2 nC + nD` (equivalently `ρ = 7 Θ`), the balanced cell off the
wall `14 nB = 19 nA` and also the whole balanced cell at `l = 0`, and
the odd-load vanishings `l, β, δ, ζ, θ` on their compete chambers.

Survives: (1) `{C,D}` on the wall `6 nA = 2 nC + nD` with `l ≠ 0`;
(2) the balanced cell on the wall `14 nB = 19 nA` with `l ≠ 0` (the
`N₁` face ties the `l A⁶` column; the 2×2 with `N₂` is not yet in
Lean); (3) A-dominant load-compete after `l = 0` that is not a
`β/δ/ζ/θ` compete chamber (letter-topped κ after the first odd load
dies).  No finite-root shortcut is used. -/
theorem normalized610ScaleZero_cubicResidual3
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
      ¬ CubicSigmaConeB610 A B C D E ∧
      ¬ CubicSigmaConeC610 A B C D E ∧
      ¬ CubicSigmaConeD610 A B C D E ∧
      ¬ CubicSigmaConeE610 A B C D E ∧
      ¬ CubicSigmaConeBC610 A B C D E ∧
      ¬ CubicSigmaConeBD610 A B C D E ∧
      ¬ CubicSigmaConeBE610 A B C D E ∧
      ¬ CubicSigmaConeCE610 A B C D E ∧
      ¬ CubicSigmaConeDE610 A B C D E ∧
      ¬ CubicSigmaConeBCD610 A B C D E ∧
      ¬ CubicSigmaConeBCE610 A B C D E ∧
      ¬ CubicSigmaConeBDE610 A B C D E ∧
      ¬ CubicSigmaConeCDE610 A B C D E ∧
      ¬ (B = 0 ∧ C = 0 ∧ D = 0 ∧ E = 0) ∧
      ¬ (CubicSigmaConeCD610 A B C D E ∧
          (l = 0 ∨ 6 * A.natDegree ≠ 2 * C.natDegree + D.natDegree)) ∧
      ¬ (CubicSigmaConeBCDE610 A B C D E ∧
          (l = 0 ∨ 14 * B.natDegree ≠ 19 * A.natDegree)) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
      notB, notC, notD, notE, notBC, notBD, notBE, notCE, notDE, notBCD,
      notBCE, notBDE, notCDE, notZero⟩ :=
    normalized610ScaleZero_cubicADominantResidual2 hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
    notB, notC, notD, notE, notBC, notBD, notBE, notCE, notDE, notBCD,
    notBCE, notBDE, notCDE, notZero, ?notCD, ?notBCDE⟩
  · intro h
    rcases h with ⟨hCD, hcase⟩
    exact cubicSigmaCone_CD_impossible l alpha beta delta epsilon zeta
      eta theta A B C D E hCD hmuDeg hkapDeg hcase
  · intro h
    rcases h with ⟨hBCDE, hcase⟩
    exact cubicBalancedCell_impossible l alpha beta delta epsilon zeta
      eta theta A B C D E hBCDE hlamDeg hkapDeg hmuDeg homiDeg hcase

end CubicAssemblyFinish610

#print axioms degreeZeroN1CubicNoSigmaCDNoL610_natDegree_lt
#print axioms degreeZeroN1CubicNoSigmaBCDENoL610_natDegree_lt
#print axioms cubicSigmaCone_CD_impossible
#print axioms cubicBalancedCell_impossible
#print axioms cubicADominant_beta_eq_zero
#print axioms cubicADominant_delta_eq_zero
#print axioms cubicADominant_zeta_eq_zero
#print axioms cubicADominant_theta_eq_zero
#print axioms normalized610ScaleZero_cubicResidual3

end Max11DegreeRoutes
