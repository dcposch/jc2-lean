import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBasePart25Scratch

/-! # Part 26 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`; statements are byte-identical.
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

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
def muQuarticFaceBDEG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoBDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  - (45 / 262144 * l : k) • (A ^ 4 * B)
  - (9 / 8192 * l : k) • (A ^ 3 * D)
  - (9 / 8192 * l : k) • (A ^ 2 * B * C)
  + (63 / 8192 * l : k) • (A * B ^ 3)
  - (9 / 1024 * l : k) • (A ^ 2 * F)
  - (9 / 512 * l : k) • (A * B * E)
  - (9 / 512 * l : k) • (A * C * D)
  - (63 / 1024 * l : k) • (B ^ 2 * D)
  - (63 / 1024 * l : k) • (B * C ^ 2)
  + (9 / 64 * l : k) • (B * G)
  + (9 / 64 * l : k) • (C * F)
  + (9 / 64 * l : k) • (D * E)
  - (7 / 8192 * beta : k) • (A ^ 3 * B)
  - (7 / 1024 * beta : k) • (A ^ 2 * D)
  + (7 / 512 * beta : k) • (A * B * C)
  + (21 / 1024 * beta : k) • B ^ 3
  - (7 / 64 * beta : k) • (A * F)
  - (7 / 64 * beta : k) • (B * E)
  - (7 / 64 * beta : k) • (C * D)
  + (3 / 128 * gamma : k) • (A * B ^ 2)
  - (3 / 16 * gamma : k) • (B * D)
  - (3 / 32 * gamma : k) • C ^ 2
  + (3 / 4 * gamma : k) • G
  - (5 / 1024 * delta : k) • (A ^ 2 * B)
  - (5 / 64 * delta : k) • (A * D)
  - (15 / 64 * delta : k) • (B * C)
  + (5 / 8 * delta : k) • F
  - (1 / 8 * epsilon : k) • B ^ 2
  + (1 / 2 * epsilon : k) • E
  - (3 / 64 * zeta : k) • (A * B)
  + (3 / 8 * zeta : k) • D
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_eq_BDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBDEG810 A B C D E F G +
        degreeZeroMuQuarticNoBDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBDEG810, degreeZeroMuQuarticNoBDEG810]
  all_goals module

theorem muQuarticFaceBDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBDEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceBDEG810 A B C D E F G).coeff (4 * B.natDegree) =
      (1 / 2048 : k) * muQuarticInnerBDEG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
  simp only [muQuarticFaceBDEG810, muQuarticInnerBDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4 : (B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
  have hcf_B4 : (B ^ 4).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (4 * B.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4, hcf_B2E, hcf_E2]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceBDEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * D ^ 2)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoBDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (E * F)
  + (105 / 4194304 * l : k) • A ^ 6
  + (135 / 262144 * l : k) • (A ^ 4 * C)
  + (9 / 4096 * l : k) • (A ^ 3 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 4096 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (9 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * F)
  - (9 / 512 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2
  + (7 / 65536 * beta : k) • A ^ 5
  + (7 / 4096 * beta : k) • (A ^ 3 * C)
  - (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 256 * beta : k) • (A * B * D)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2
  + (3 / 128 * gamma : k) • (A * B * C)
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 32 * gamma : k) • (A * F)
  - (3 / 16 * gamma : k) • (B * E)
  - (3 / 16 * gamma : k) • (C * D)
  + (15 / 32768 * delta : k) • A ^ 4
  + (5 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 512 * delta : k) • (A * B ^ 2)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G
  - (1 / 16 * epsilon : k) • (A * D)
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F
  + (1 / 512 * zeta : k) • A ^ 3
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  - (1 / 32 * eta : k) • (A * B)
  + (1 / 4 * eta : k) • D
  + (1 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuartic810_eq_BDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBDEG810 A B C D E F G +
        degreeZeroNuQuarticNoBDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBDEG810, degreeZeroNuQuarticNoBDEG810]
  all_goals module

theorem nuQuarticFaceBDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBDEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceBDEG810 A B C D E F G).coeff (B.natDegree + 2 * D.natDegree) =
      (1 / 128 : k) * nuQuarticInnerBDEG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
  simp only [nuQuarticFaceBDEG810, nuQuarticInnerBDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = B.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
  have hcf_BD2 : ((B * D ^ 2)).coeff (B.natDegree + 2 * D.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DG : ((D * G)).natDegree = B.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hDne hGne]
    omega
  have hcf_DG : ((D * G)).coeff (B.natDegree + 2 * D.natDegree) =
      D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_DG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_BD2, hcf_DG]
  ring

end QuarticKills810

end Max11DegreeRoutes
