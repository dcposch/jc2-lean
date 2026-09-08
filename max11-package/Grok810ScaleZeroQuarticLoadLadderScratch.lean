import Grok810ScaleZeroQuarticSigmaLadderScratch

/-! # Scale-zero quartic κ load ladder, `(8,10)`, cone `A` (File A2)

Continuation of `Grok810ScaleZeroQuarticSigmaLadderScratch` (File A,
commit b32bd96).  That file proves the `l` kill `quarticSigma_l_eq_zero`
(κ carrier: the pure-`A` column `63/262144 · l · A^5` tops κ when
`2s > a`) and the band disjunctions, but not the kills for `β, δ, ζ, θ`.

Plan `Grok810ScaleZeroQuarticSigmaLadderPlanScratch.md` §1.3 / §2.1 / §2.2
and `~/lean/tools/sigma810/FILES_BC_MANIFEST.md` Blockers item 1: the
forced ladder `l → β → δ → ζ → θ`.  Each kill assumes the earlier odd
loads are already 0, which removes their columns from κ.  κ's load-free
part has cost ≥ `2s`, so with `l = 0` the `β` column `35/32768 · β · A^4`
strictly tops κ iff `2s > 3a`, the `δ` column `5/1024 · δ · A^3` iff
`2s > 5a`, the `ζ` column `3/128 · ζ · A^2` iff `2s > 7a`, and the `θ`
column `1/8 · θ · A` iff `2s > 9a`.

`γ, ε, η` columns of κ have letters `γ: BC, F`, `ε: D`, `η: B` and are
dominated on each Top predicate; the one extra side condition is
`F.natDegree < A.natDegree` on the `θ` Top (so `γ · F` sits strictly
below `θ · A`; `ε · D` follows from `4 * D.natDegree < A.natDegree`,
`η · B` vanishes with `B = 0`).

`QuarticKappaLoadTop{Beta,Delta,Zeta}810` and all fifteen
`QuarticN2LoadTop*` predicates on the three `k = 3` cones already live
in File A; this file defines `QuarticKappaLoadTopTheta810` and the four
κ-column rest/identity/bound/kill packages.

Does not prove the `N₂` kills, does not close Files B/C, and does not
close corner H (`γ/ε/η`).  No `sorry`, no new axioms, no finite-root
shortcut.  Untracked working note.
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

variable {k : Type*} [Field k] [CharZero k]

section QuarticKappaLoadLadder810

/-! ### `beta` column (degree 4 `a`, kill when `2s > 3 a`) -/

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoBetaColumn1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoBetaColumn2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * gamma : k)) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (5 / 1024 * delta : k) • A ^ 3
  + (5 / 64 * delta : k) • (A * C)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E
  + (1 / 2 * epsilon : k) • D
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

def degreeZeroKappaQuarticNoBetaColumn810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroKappaQuarticNoBetaColumn1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroKappaQuarticNoBetaColumn2810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoBetaColumn1810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 3 * A.natDegree)
    (hCt : 4 * C.natDegree < 5 * A.natDegree)
    (hDt : 4 * D.natDegree < 7 * A.natDegree)
    (hEt : 4 * E.natDegree < 9 * A.natDegree)
    (hFt : 4 * F.natDegree < 11 * A.natDegree)
    (hGt : 4 * G.natDegree < 13 * A.natDegree) :
    (degreeZeroKappaQuarticNoBetaColumn1810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * A.natDegree := by
  have hApos1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hAB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hAC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hAD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hAE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hAF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hAF
  have hAG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hAG
  have hBt1 : 4 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBt
  have hCt1 : 4 * C.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hCt
  have hDt1 : 4 * D.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hDt
  have hEt1 : 4 * E.natDegree + 1 ≤ 9 * A.natDegree := Nat.succ_le_of_lt hEt
  have hFt1 : 4 * F.natDegree + 1 ≤ 11 * A.natDegree := Nat.succ_le_of_lt hFt
  have hGt1 : 4 * G.natDegree + 1 ≤ 13 * A.natDegree := Nat.succ_le_of_lt hGt
  simp only [degreeZeroKappaQuarticNoBetaColumn1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoBetaColumn2810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 3 * A.natDegree)
    (hCt : 4 * C.natDegree < 5 * A.natDegree)
    (hDt : 4 * D.natDegree < 7 * A.natDegree)
    (hEt : 4 * E.natDegree < 9 * A.natDegree)
    (hFt : 4 * F.natDegree < 11 * A.natDegree)
    (hGt : 4 * G.natDegree < 13 * A.natDegree) :
    (degreeZeroKappaQuarticNoBetaColumn2810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * A.natDegree := by
  have hApos1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hAB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hAC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hAD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hAE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hAF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hAF
  have hAG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hAG
  have hBt1 : 4 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBt
  have hCt1 : 4 * C.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hCt
  have hDt1 : 4 * D.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hDt
  have hEt1 : 4 * E.natDegree + 1 ≤ 9 * A.natDegree := Nat.succ_le_of_lt hEt
  have hFt1 : 4 * F.natDegree + 1 ≤ 11 * A.natDegree := Nat.succ_le_of_lt hFt
  have hGt1 : 4 * G.natDegree + 1 ≤ 13 * A.natDegree := Nat.succ_le_of_lt hGt
  simp only [degreeZeroKappaQuarticNoBetaColumn2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoBetaColumn810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 3 * A.natDegree)
    (hCt : 4 * C.natDegree < 5 * A.natDegree)
    (hDt : 4 * D.natDegree < 7 * A.natDegree)
    (hEt : 4 * E.natDegree < 9 * A.natDegree)
    (hFt : 4 * F.natDegree < 11 * A.natDegree)
    (hGt : 4 * G.natDegree < 13 * A.natDegree) :
    (degreeZeroKappaQuarticNoBetaColumn810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * A.natDegree := by
  have h1 :=
    degreeZeroKappaQuarticNoBetaColumn1810_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt hEt hFt hGt
  have h2 :=
    degreeZeroKappaQuarticNoBetaColumn2810_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt hEt hFt hGt
  have hall := natDegree_add_lt810 h1 h2
  simp only [degreeZeroKappaQuarticNoBetaColumn810]
  exact hall

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_betaColumn_add_rest
    (beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 0 beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      kappaQuarticBetaFace810 beta A +
        degreeZeroKappaQuarticNoBetaColumn810 0 beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticBetaFace810, degreeZeroKappaQuarticNoBetaColumn810, degreeZeroKappaQuarticNoBetaColumn1810, degreeZeroKappaQuarticNoBetaColumn2810, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, pow_one]
  module

theorem quarticKappaLoadTopBeta810_bounds
    {A B C D E F G : k[X]}
    (h : QuarticKappaLoadTopBeta810 A B C D E F G) :
    0 < A.natDegree ∧
      2 * B.natDegree < 3 * A.natDegree ∧
      C.natDegree < 2 * A.natDegree ∧
      2 * D.natDegree < 5 * A.natDegree ∧
      E.natDegree < 3 * A.natDegree ∧
      2 * F.natDegree < 7 * A.natDegree ∧
      G.natDegree < 4 * A.natDegree ∧
      4 * B.natDegree < 3 * A.natDegree ∧
      4 * C.natDegree < 5 * A.natDegree ∧
      4 * D.natDegree < 7 * A.natDegree ∧
      4 * E.natDegree < 9 * A.natDegree ∧
      4 * F.natDegree < 11 * A.natDegree ∧
      4 * G.natDegree < 13 * A.natDegree := by
  rcases h with ⟨hA, hB, hC, hD, hE, hF, hG⟩
  rcases hA with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hBt : 4 * B.natDegree < 3 * A.natDegree := by
    rcases hB with h0 | hlt
    · have : B.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hCt : 4 * C.natDegree < 5 * A.natDegree := by
    rcases hC with h0 | hlt
    · have : C.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hDt : 4 * D.natDegree < 7 * A.natDegree := by
    rcases hD with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hEt : 4 * E.natDegree < 9 * A.natDegree := by
    rcases hE with h0 | hlt
    · have : E.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hFt : 4 * F.natDegree < 11 * A.natDegree := by
    rcases hF with h0 | hlt
    · have : F.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hGt : 4 * G.natDegree < 13 * A.natDegree := by
    rcases hG with h0 | hlt
    · have : G.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  refine ⟨hApos, by omega, by omega, by omega, by omega, by omega, by omega, hBt, hCt, hDt, hEt, hFt, hGt⟩

set_option maxHeartbeats 64000000 in
/-- κ-column kill for `beta`: cone A, `QuarticKappaLoadTopBeta810` (`2s > 3 a`),
the earlier odd loads already 0, and `natDegree κ = 0`. -/
theorem quarticSigma_beta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticKappaLoadTopBeta810 A B C D E F G)
    (hl : l = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree = 0) :
    beta = 0 := by
  by_contra hne
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG, hBt, hCt, hDt, hEt, hFt, hGt⟩ :=
    quarticKappaLoadTopBeta810_bounds htop
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (35 / 32768 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (kappaQuarticBetaFace810 beta A).natDegree = 4 * A.natDegree := by
    simp only [kappaQuarticBetaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroKappaQuarticNoBetaColumn810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt hEt hFt hGt
  subst hl
  rw [degreeZeroKappaQuartic810_eq_betaColumn_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hkap
  omega

/-! ### `delta` column (degree 3 `a`, kill when `2s > 5 a`) -/

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoDeltaColumn1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoDeltaColumn2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • (A * C)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E
  + (1 / 2 * epsilon : k) • D
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

def degreeZeroKappaQuarticNoDeltaColumn810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroKappaQuarticNoDeltaColumn1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroKappaQuarticNoDeltaColumn2810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoDeltaColumn1810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < A.natDegree)
    (hCt : 4 * C.natDegree < 3 * A.natDegree)
    (hDt : 4 * D.natDegree < 5 * A.natDegree)
    (hEt : 4 * E.natDegree < 7 * A.natDegree)
    (hFt : 4 * F.natDegree < 9 * A.natDegree)
    (hGt : 4 * G.natDegree < 11 * A.natDegree) :
    (degreeZeroKappaQuarticNoDeltaColumn1810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * A.natDegree := by
  have hApos1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hAB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hAC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hAD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hAE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hAF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hAF
  have hAG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hAG
  have hBt1 : 4 * B.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hBt
  have hCt1 : 4 * C.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hCt
  have hDt1 : 4 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDt
  have hEt1 : 4 * E.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hEt
  have hFt1 : 4 * F.natDegree + 1 ≤ 9 * A.natDegree := Nat.succ_le_of_lt hFt
  have hGt1 : 4 * G.natDegree + 1 ≤ 11 * A.natDegree := Nat.succ_le_of_lt hGt
  simp only [degreeZeroKappaQuarticNoDeltaColumn1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoDeltaColumn2810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < A.natDegree)
    (hCt : 4 * C.natDegree < 3 * A.natDegree)
    (hDt : 4 * D.natDegree < 5 * A.natDegree)
    (hEt : 4 * E.natDegree < 7 * A.natDegree)
    (hFt : 4 * F.natDegree < 9 * A.natDegree)
    (hGt : 4 * G.natDegree < 11 * A.natDegree) :
    (degreeZeroKappaQuarticNoDeltaColumn2810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * A.natDegree := by
  have hApos1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hAB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hAC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hAD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hAE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hAF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hAF
  have hAG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hAG
  have hBt1 : 4 * B.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hBt
  have hCt1 : 4 * C.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hCt
  have hDt1 : 4 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDt
  have hEt1 : 4 * E.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hEt
  have hFt1 : 4 * F.natDegree + 1 ≤ 9 * A.natDegree := Nat.succ_le_of_lt hFt
  have hGt1 : 4 * G.natDegree + 1 ≤ 11 * A.natDegree := Nat.succ_le_of_lt hGt
  simp only [degreeZeroKappaQuarticNoDeltaColumn2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoDeltaColumn810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < A.natDegree)
    (hCt : 4 * C.natDegree < 3 * A.natDegree)
    (hDt : 4 * D.natDegree < 5 * A.natDegree)
    (hEt : 4 * E.natDegree < 7 * A.natDegree)
    (hFt : 4 * F.natDegree < 9 * A.natDegree)
    (hGt : 4 * G.natDegree < 11 * A.natDegree) :
    (degreeZeroKappaQuarticNoDeltaColumn810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * A.natDegree := by
  have h1 :=
    degreeZeroKappaQuarticNoDeltaColumn1810_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt hEt hFt hGt
  have h2 :=
    degreeZeroKappaQuarticNoDeltaColumn2810_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt hEt hFt hGt
  have hall := natDegree_add_lt810 h1 h2
  simp only [degreeZeroKappaQuarticNoDeltaColumn810]
  exact hall

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_deltaColumn_add_rest
    (gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 0 0 gamma delta epsilon zeta eta theta
        A B C D E F G =
      kappaQuarticDeltaFace810 delta A +
        degreeZeroKappaQuarticNoDeltaColumn810 0 0 gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticDeltaFace810, degreeZeroKappaQuarticNoDeltaColumn810, degreeZeroKappaQuarticNoDeltaColumn1810, degreeZeroKappaQuarticNoDeltaColumn2810, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, pow_one]
  module

theorem quarticKappaLoadTopDelta810_bounds
    {A B C D E F G : k[X]}
    (h : QuarticKappaLoadTopDelta810 A B C D E F G) :
    0 < A.natDegree ∧
      2 * B.natDegree < 3 * A.natDegree ∧
      C.natDegree < 2 * A.natDegree ∧
      2 * D.natDegree < 5 * A.natDegree ∧
      E.natDegree < 3 * A.natDegree ∧
      2 * F.natDegree < 7 * A.natDegree ∧
      G.natDegree < 4 * A.natDegree ∧
      4 * B.natDegree < A.natDegree ∧
      4 * C.natDegree < 3 * A.natDegree ∧
      4 * D.natDegree < 5 * A.natDegree ∧
      4 * E.natDegree < 7 * A.natDegree ∧
      4 * F.natDegree < 9 * A.natDegree ∧
      4 * G.natDegree < 11 * A.natDegree := by
  rcases h with ⟨hA, hB, hC, hD, hE, hF, hG⟩
  rcases hA with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hBt : 4 * B.natDegree < A.natDegree := by
    rcases hB with h0 | hlt
    · have : B.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hCt : 4 * C.natDegree < 3 * A.natDegree := by
    rcases hC with h0 | hlt
    · have : C.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hDt : 4 * D.natDegree < 5 * A.natDegree := by
    rcases hD with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hEt : 4 * E.natDegree < 7 * A.natDegree := by
    rcases hE with h0 | hlt
    · have : E.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hFt : 4 * F.natDegree < 9 * A.natDegree := by
    rcases hF with h0 | hlt
    · have : F.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hGt : 4 * G.natDegree < 11 * A.natDegree := by
    rcases hG with h0 | hlt
    · have : G.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  refine ⟨hApos, by omega, by omega, by omega, by omega, by omega, by omega, hBt, hCt, hDt, hEt, hFt, hGt⟩

set_option maxHeartbeats 64000000 in
/-- κ-column kill for `delta`: cone A, `QuarticKappaLoadTopDelta810` (`2s > 5 a`),
the earlier odd loads already 0, and `natDegree κ = 0`. -/
theorem quarticSigma_delta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticKappaLoadTopDelta810 A B C D E F G)
    (hl : l = 0)
    (hbeta : beta = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree = 0) :
    delta = 0 := by
  by_contra hne
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG, hBt, hCt, hDt, hEt, hFt, hGt⟩ :=
    quarticKappaLoadTopDelta810_bounds htop
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (5 / 1024 * delta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (kappaQuarticDeltaFace810 delta A).natDegree = 3 * A.natDegree := by
    simp only [kappaQuarticDeltaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroKappaQuarticNoDeltaColumn810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      hApos hAB hAC hAD hAE hAF hAG hBt hCt hDt hEt hFt hGt
  subst hl; subst hbeta
  rw [degreeZeroKappaQuartic810_eq_deltaColumn_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hkap
  omega

/-! ### `zeta` column (degree 2 `a`, kill when `2s > 7 a`) -/

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoZetaColumn810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (1 / 2 * epsilon : k) • D
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoZetaColumn810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBz : B = 0)
    (hBn : B.natDegree = 0)
    (hCt : 4 * C.natDegree < A.natDegree)
    (hDt : 4 * D.natDegree < 3 * A.natDegree)
    (hEt : 4 * E.natDegree < 5 * A.natDegree)
    (hFt : 4 * F.natDegree < 7 * A.natDegree)
    (hGt : 4 * G.natDegree < 9 * A.natDegree) :
    (degreeZeroKappaQuarticNoZetaColumn810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree := by
  have hApos1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hAB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hAC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hAD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hAE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hAF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hAF
  have hAG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hAG
  have hBcone1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := by omega
  have hCt1 : 4 * C.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hCt
  have hDt1 : 4 * D.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hDt
  have hEt1 : 4 * E.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hEt
  have hFt1 : 4 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFt
  have hGt1 : 4 * G.natDegree + 1 ≤ 9 * A.natDegree := Nat.succ_le_of_lt hGt
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  simp only [degreeZeroKappaQuarticNoZetaColumn810, hBz,
    hpow2, hpow3, zero_mul, mul_zero, zero_smul, smul_zero,
    add_zero, zero_add, sub_zero, neg_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_zetaColumn_add_rest
    (gamma epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 0 0 gamma 0 epsilon zeta eta theta
        A B C D E F G =
      kappaQuarticZetaFace810 zeta A +
        degreeZeroKappaQuarticNoZetaColumn810 0 0 gamma 0 epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticZetaFace810, degreeZeroKappaQuarticNoZetaColumn810, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, pow_one]
  module

theorem quarticKappaLoadTopZeta810_bounds
    {A B C D E F G : k[X]}
    (h : QuarticKappaLoadTopZeta810 A B C D E F G) :
    0 < A.natDegree ∧
      2 * B.natDegree < 3 * A.natDegree ∧
      C.natDegree < 2 * A.natDegree ∧
      2 * D.natDegree < 5 * A.natDegree ∧
      E.natDegree < 3 * A.natDegree ∧
      2 * F.natDegree < 7 * A.natDegree ∧
      G.natDegree < 4 * A.natDegree ∧
      B = 0 ∧
      B.natDegree = 0 ∧
      4 * C.natDegree < A.natDegree ∧
      4 * D.natDegree < 3 * A.natDegree ∧
      4 * E.natDegree < 5 * A.natDegree ∧
      4 * F.natDegree < 7 * A.natDegree ∧
      4 * G.natDegree < 9 * A.natDegree := by
  rcases h with ⟨hA, hBzpoly, hC, hD, hE, hF, hG⟩
  rcases hA with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hBn : B.natDegree = 0 := by simp [hBzpoly]
  have hCt : 4 * C.natDegree < A.natDegree := by
    rcases hC with h0 | hlt
    · have : C.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hDt : 4 * D.natDegree < 3 * A.natDegree := by
    rcases hD with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hEt : 4 * E.natDegree < 5 * A.natDegree := by
    rcases hE with h0 | hlt
    · have : E.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hFt : 4 * F.natDegree < 7 * A.natDegree := by
    rcases hF with h0 | hlt
    · have : F.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hGt : 4 * G.natDegree < 9 * A.natDegree := by
    rcases hG with h0 | hlt
    · have : G.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  refine ⟨hApos, by omega, by omega, by omega, by omega, by omega, by omega, hBzpoly, hBn, hCt, hDt, hEt, hFt, hGt⟩

set_option maxHeartbeats 64000000 in
/-- κ-column kill for `zeta`: cone A, `QuarticKappaLoadTopZeta810` (`2s > 7 a`),
the earlier odd loads already 0, and `natDegree κ = 0`. -/
theorem quarticSigma_zeta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticKappaLoadTopZeta810 A B C D E F G)
    (hl : l = 0)
    (hbeta : beta = 0)
    (hdelta : delta = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree = 0) :
    zeta = 0 := by
  by_contra hne
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG, hBz, hBn, hCt, hDt, hEt, hFt, hGt⟩ :=
    quarticKappaLoadTopZeta810_bounds htop
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (3 / 128 * zeta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (kappaQuarticZetaFace810 zeta A).natDegree = 2 * A.natDegree := by
    simp only [kappaQuarticZetaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroKappaQuarticNoZetaColumn810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      hApos hAB hAC hAD hAE hAF hAG hBz hBn hCt hDt hEt hFt hGt
  subst hl; subst hbeta; subst hdelta
  rw [degreeZeroKappaQuartic810_eq_zetaColumn_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hkap
  omega

/-! ### `theta` column (degree 1 `a`, kill when `2s > 9 a`) -/

def kappaQuarticThetaFace810 (theta : k) (A : k[X]) : k[X] :=
  (1 / 8 * theta : k) • A

/-- κ kills `theta` when `2s > 9 a`, expanded per letter.
B and C are forced to the zero polynomial (`2 s_B ≤ 6a < 9a`,
`2 s_C ≤ 8a < 9a`).  D,E,G use the live-letter form of `2s > 9a`.
F uses the stricter γ-column domination `F.natDegree < A.natDegree`
(needed so `γ · F` sits strictly below the `θ · A` column; it implies
the raw `2 s_F > 9a` inequality `4 * F.natDegree < 5 * A.natDegree`).
ε·D is dominated by `4 * D.natDegree < A.natDegree`; η·B vanishes with `B = 0`. -/
def QuarticKappaLoadTopTheta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    C = 0 ∧
    (D = 0 ∨ 4 * D.natDegree < A.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 3 * A.natDegree) ∧
    (F = 0 ∨ F.natDegree < A.natDegree) ∧
    (G = 0 ∨ 4 * G.natDegree < 7 * A.natDegree)

set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoThetaColumn810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (1 / 2 * epsilon : k) • D
  + (1 / 4 * eta : k) • B

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoThetaColumn810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBz : B = 0)
    (hBn : B.natDegree = 0)
    (hCz : C = 0)
    (hCn : C.natDegree = 0)
    (hDt : 4 * D.natDegree < A.natDegree)
    (hEt : 4 * E.natDegree < 3 * A.natDegree)
    (hFt : F.natDegree < A.natDegree)
    (hGt : 4 * G.natDegree < 7 * A.natDegree) :
    (degreeZeroKappaQuarticNoThetaColumn810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree := by
  have hApos1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hAB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hAC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hAD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hAE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hAF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hAF
  have hAG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hAG
  have hBcone1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := by omega
  have hCcone1 : C.natDegree + 1 ≤ 2 * A.natDegree := by omega
  have hDt1 : 4 * D.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hDt
  have hEt1 : 4 * E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hEt
  have hFt1 : F.natDegree + 1 ≤ A.natDegree := Nat.succ_le_of_lt hFt
  have hGt1 : 4 * G.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hGt
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  simp only [degreeZeroKappaQuarticNoThetaColumn810, hBz, hCz,
    hpow2, hpow3, zero_mul, mul_zero, zero_smul, smul_zero,
    add_zero, zero_add, sub_zero, neg_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_thetaColumn_add_rest
    (gamma epsilon eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 0 0 gamma 0 epsilon 0 eta theta
        A B C D E F G =
      kappaQuarticThetaFace810 theta A +
        degreeZeroKappaQuarticNoThetaColumn810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticThetaFace810, degreeZeroKappaQuarticNoThetaColumn810, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, pow_one]
  module

theorem quarticKappaLoadTopTheta810_bounds
    {A B C D E F G : k[X]}
    (h : QuarticKappaLoadTopTheta810 A B C D E F G) :
    0 < A.natDegree ∧
      2 * B.natDegree < 3 * A.natDegree ∧
      C.natDegree < 2 * A.natDegree ∧
      2 * D.natDegree < 5 * A.natDegree ∧
      E.natDegree < 3 * A.natDegree ∧
      2 * F.natDegree < 7 * A.natDegree ∧
      G.natDegree < 4 * A.natDegree ∧
      B = 0 ∧
      B.natDegree = 0 ∧
      C = 0 ∧
      C.natDegree = 0 ∧
      4 * D.natDegree < A.natDegree ∧
      4 * E.natDegree < 3 * A.natDegree ∧
      F.natDegree < A.natDegree ∧
      4 * G.natDegree < 7 * A.natDegree := by
  rcases h with ⟨hA, hBzpoly, hCzpoly, hD, hE, hF, hG⟩
  rcases hA with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hBn : B.natDegree = 0 := by simp [hBzpoly]
  have hCn : C.natDegree = 0 := by simp [hCzpoly]
  have hDt : 4 * D.natDegree < A.natDegree := by
    rcases hD with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hEt : 4 * E.natDegree < 3 * A.natDegree := by
    rcases hE with h0 | hlt
    · have : E.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hFt : F.natDegree < A.natDegree := by
    rcases hF with h0 | hlt
    · have : F.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  have hGt : 4 * G.natDegree < 7 * A.natDegree := by
    rcases hG with h0 | hlt
    · have : G.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  refine ⟨hApos, by omega, by omega, by omega, by omega, by omega, by omega, hBzpoly, hBn, hCzpoly, hCn, hDt, hEt, hFt, hGt⟩

set_option maxHeartbeats 64000000 in
/-- κ-column kill for `theta`: cone A, `QuarticKappaLoadTopTheta810` (`2s > 9 a`),
the earlier odd loads already 0, and `natDegree κ = 0`. -/
theorem quarticSigma_theta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticKappaLoadTopTheta810 A B C D E F G)
    (hl : l = 0)
    (hbeta : beta = 0)
    (hdelta : delta = 0)
    (hzeta : zeta = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree = 0) :
    theta = 0 := by
  by_contra hne
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG, hBz, hBn, hCz, hCn, hDt, hEt, hFt, hGt⟩ :=
    quarticKappaLoadTopTheta810_bounds htop
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (1 / 8 * theta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (kappaQuarticThetaFace810 theta A).natDegree = A.natDegree := by
    simp only [kappaQuarticThetaFace810]
    rw [natDegree_smul _ hc]
  have hrest :=
    degreeZeroKappaQuarticNoThetaColumn810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      hApos hAB hAC hAD hAE hAF hAG hBz hBn hCz hCn hDt hEt hFt hGt
  subst hl; subst hbeta; subst hdelta; subst hzeta
  rw [degreeZeroKappaQuartic810_eq_thetaColumn_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hkap
  omega

theorem quarticSigma_theta_band_disjunction
    {theta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaLoadTopTheta810 A B C D E F G → theta = 0) :
    theta = 0 ∨
      B ≠ 0 ∨
      C ≠ 0 ∨
      A.natDegree ≤ 4 * D.natDegree ∨
      3 * A.natDegree ≤ 4 * E.natDegree ∨
      A.natDegree ≤ F.natDegree ∨
      7 * A.natDegree ≤ 4 * G.natDegree := by
  by_cases hB : B = 0
  · by_cases hC : C = 0
    · by_cases hD : 4 * D.natDegree < A.natDegree
      · by_cases hE : 4 * E.natDegree < 3 * A.natDegree
        · by_cases hF : F.natDegree < A.natDegree
          · by_cases hG : 4 * G.natDegree < 7 * A.natDegree
            · exact Or.inl (hkill ⟨hA, hB, hC, Or.inr hD, Or.inr hE,
                Or.inr hF, Or.inr hG⟩)
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · exact Or.inr (Or.inr (Or.inl hC))
  · exact Or.inr (Or.inl hB)

end QuarticKappaLoadLadder810

section QuarticLoadLadderAssembly810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- File A2 gain: the four κ-column kills of the odd-load ladder.

`QuarticKappaLoadTopL810 → l = 0` is File A.  This packages the rest of
the ladder: each subsequent kill assumes the earlier odd loads are 0.
Next unused row: `N₂` kills on the three `k = 3` cones (predicates
already in File A), then Files B/C chamber kills (the β/δ/ζ/θ band
disjunctions are now dischargeable), then corner H (`γ/ε/η`).
Named residual: corner H `B = 0 ∧ s ≥ 4a ∧ S ⊆ {C,D,E} ∧ γ ≠ 0`, and
the `N₂` kills themselves.  No finite-root shortcut. -/
theorem quarticSigma_kappaLoadLadder_kills
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree = 0) :
    (QuarticKappaLoadTopL810 A B C D E F G → l = 0) ∧
      (l = 0 → QuarticKappaLoadTopBeta810 A B C D E F G → beta = 0) ∧
      (l = 0 → beta = 0 → QuarticKappaLoadTopDelta810 A B C D E F G →
        delta = 0) ∧
      (l = 0 → beta = 0 → delta = 0 →
        QuarticKappaLoadTopZeta810 A B C D E F G → zeta = 0) ∧
      (l = 0 → beta = 0 → delta = 0 → zeta = 0 →
        QuarticKappaLoadTopTheta810 A B C D E F G → theta = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro htop
    exact quarticSigma_l_eq_zero l beta gamma delta epsilon zeta eta
      theta A B C D E F G htop hkap
  · intro hl htop
    exact quarticSigma_beta_eq_zero l beta gamma delta epsilon zeta eta
      theta A B C D E F G htop hl hkap
  · intro hl hb htop
    exact quarticSigma_delta_eq_zero l beta gamma delta epsilon zeta eta
      theta A B C D E F G htop hl hb hkap
  · intro hl hb hd htop
    exact quarticSigma_zeta_eq_zero l beta gamma delta epsilon zeta eta
      theta A B C D E F G htop hl hb hd hkap
  · intro hl hb hd hz htop
    exact quarticSigma_theta_eq_zero l beta gamma delta epsilon zeta eta
      theta A B C D E F G htop hl hb hd hz hkap

set_option maxHeartbeats 64000000 in
/-- Honest leftover after File A2 of the σ-defect ladder.

Closed relative to `normalized810ScaleZero_quarticSigmaResidual`: the
κ-column implications `TopL → l = 0`, `l = 0 → TopBeta → β = 0`,
`l = 0 → β = 0 → TopDelta → δ = 0`, `l = 0 → β = 0 → δ = 0 → TopZeta → ζ = 0`,
`l = 0 → β = 0 → δ = 0 → ζ = 0 → TopTheta → θ = 0`, and the matching
band disjunctions.  Files B/C (chamber kills) and File D (even core /
corner H) are not closed.  `N₂` kills on `{B}`, `{C}`, `{B,C}` are not
proved (predicates only).  No finite-root shortcut. -/
theorem normalized810ScaleZero_quarticLoadLadderResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (
        (QuarticRatioConeA810 A B C D E F G ∧
          QuarticSigmaSupportCone810 A B C D E F G ∧
          (QuarticKappaLoadTopL810 A B C D E F G → l = 0) ∧
          (l = 0 → QuarticKappaLoadTopBeta810 A B C D E F G → beta = 0) ∧
          (l = 0 → beta = 0 → QuarticKappaLoadTopDelta810 A B C D E F G →
            delta = 0) ∧
          (l = 0 → beta = 0 → delta = 0 →
            QuarticKappaLoadTopZeta810 A B C D E F G → zeta = 0) ∧
          (l = 0 → beta = 0 → delta = 0 → zeta = 0 →
            QuarticKappaLoadTopTheta810 A B C D E F G → theta = 0) ∧
          ((l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0) ∨
            ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
                E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0)) ∧
          ¬ (B = 0 ∧ D = 0 ∧ F = 0 ∧ 0 < C.natDegree ∧
              2 * E.natDegree < 3 * C.natDegree ∧
              G.natDegree < 2 * C.natDegree) ∧
          ¬ (B = 0 ∧ D = 0 ∧ F = 0 ∧ 0 < E.natDegree ∧
              3 * C.natDegree < 2 * E.natDegree ∧
              3 * G.natDegree < 2 * E.natDegree)) ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    normalized810ScaleZero_quarticSigmaResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  rcases hdisj with hA | hABCDEFG
  · rcases hA with ⟨hconeA, hexh, hlKill, _hlBand, hconst, hevenC, hevenE⟩
    refine Or.inl ⟨hconeA, hexh, hlKill, ?hb, ?hd, ?hz, ?ht, hconst,
      hevenC, hevenE⟩
    · intro hl htop
      exact quarticSigma_beta_eq_zero l beta gamma delta epsilon zeta eta
        theta A B C D E F G htop hl hkapDeg
    · intro hl hb htop
      exact quarticSigma_delta_eq_zero l beta gamma delta epsilon zeta eta
        theta A B C D E F G htop hl hb hkapDeg
    · intro hl hb hd htop
      exact quarticSigma_zeta_eq_zero l beta gamma delta epsilon zeta eta
        theta A B C D E F G htop hl hb hd hkapDeg
    · intro hl hb hd hz htop
      exact quarticSigma_theta_eq_zero l beta gamma delta epsilon zeta eta
        theta A B C D E F G htop hl hb hd hz hkapDeg
  · exact Or.inr hABCDEFG

end QuarticLoadLadderAssembly810

#print axioms quarticSigma_beta_eq_zero
#print axioms quarticSigma_delta_eq_zero
#print axioms quarticSigma_zeta_eq_zero
#print axioms quarticSigma_theta_eq_zero
#print axioms quarticSigma_kappaLoadLadder_kills
#print axioms normalized810ScaleZero_quarticLoadLadderResidual

end Max11DegreeRoutes
