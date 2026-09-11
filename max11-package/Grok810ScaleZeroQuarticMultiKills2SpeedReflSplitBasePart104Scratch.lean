import Grok810ScaleZeroQuarticDefsScratch
import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBasePart101Scratch
import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBasePart08Scratch
import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBasePart103Scratch

/-! # Part 29 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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
def kappaQuarticFaceBDFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_BDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBDFG810 A B C D E F G +
        degreeZeroKappaQuarticNoBDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBDFG810, degreeZeroKappaQuarticNoBDFG810]
  all_goals module

theorem kappaQuarticFaceBDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBDFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceBDFG810 A B C D E F G).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 128 : k) * kappaQuarticInnerBDFG810 B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
  simp only [kappaQuarticFaceBDFG810, kappaQuarticInnerBDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hcf_B2D : ((B ^ 2 * D)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BG : ((B * G)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hBne hGne]
    omega
  have hcf_BG : ((B * G)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2D, hcf_BG]
  ring

set_option maxHeartbeats 16000000 in
def muQuarticFaceBDFG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoBDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2
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
theorem degreeZeroMuQuartic810_eq_BDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBDFG810 A B C D E F G +
        degreeZeroMuQuarticNoBDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBDFG810, degreeZeroMuQuarticNoBDFG810]
  all_goals module

theorem muQuarticFaceBDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBDFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceBDFG810 A B C D E F G).coeff (4 * B.natDegree) =
      (1 / 2048 : k) * muQuarticInnerBDFG810 B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
  simp only [muQuarticFaceBDFG810, muQuarticInnerBDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4 : (B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
  have hcf_B4 : (B ^ 4).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_DF : ((D * F)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (4 * B.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B4, hcf_DF]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 30 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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
def nuQuarticFaceBDFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * F)
  - (15 / 128 : k) • (B * D ^ 2)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoBDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
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
theorem degreeZeroNuQuartic810_eq_BDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBDFG810 A B C D E F G +
        degreeZeroNuQuarticNoBDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBDFG810, degreeZeroNuQuarticNoBDFG810]
  all_goals module

theorem nuQuarticFaceBDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBDFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceBDFG810 A B C D E F G).coeff (2 * B.natDegree + F.natDegree) =
      (1 / 128 : k) * nuQuarticInnerBDFG810 B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
  simp only [nuQuarticFaceBDFG810, nuQuarticInnerBDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B2F : ((B ^ 2 * F)).natDegree = 2 * B.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hFne, natDegree_pow]
  have hcf_B2F : ((B ^ 2 * F)).coeff (2 * B.natDegree + F.natDegree) =
      B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 2 * B.natDegree + F.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (2 * B.natDegree + F.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DG : ((D * G)).natDegree = 2 * B.natDegree + F.natDegree := by
    rw [natDegree_mul hDne hGne]
    omega
  have hcf_DG : ((D * G)).coeff (2 * B.natDegree + F.natDegree) =
      D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_DG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2F, hcf_BD2, hcf_DG]
  ring

def kappaQuarticInnerCDEF810 (c d e f : k) : k :=
  5 * c * f + 5 * d * e

def muQuarticInnerCDEF810 (c d e f : k) : k :=
  (-5 : k) * c ^ 3 + 40 * d * f + 20 * e ^ 2

def nuQuarticInnerCDEF810 (c d e f : k) : k :=
  (-15 : k) * c ^ 2 * d + 40 * e * f

def xiQuarticInnerCDEF810 (c d e f : k) : k :=
  (-15 : k) * c ^ 2 * e + (-15 : k) * c * d ^ 2 + 20 * f ^ 2

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 9 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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

def omicronQuarticInnerBCDG810 (b c d g : k) : k :=
  (-21 : k) * b ^ 5 + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-480 : k) * b * c * g + (-160 : k) * d ^ 3

def piQuarticInnerBCDG810 (b c d g : k) : k :=
  (-35 : k) * b ^ 4 * c + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + (-160 : k) * b * d * g + 15 * c ^ 4 + (-80 : k) * c ^ 2 * g + 320 * g ^ 2

def primitiveQuarticInnerBCDG810 (b c d g : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 120 * b ^ 3 * g + 720 * b * c * d ^ 2 + 240 * c ^ 3 * d + (-640 : k) * c * d * g

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCDG_identity
    (b c d g : k) :
    ((-32 / 35 : k) * b ^ 6 * c + (-320 / 49 : k) * b ^ 3 * c ^ 2 * d + (4608 / 245 : k) * b ^ 3 * d * g + (512 / 49 : k) * b ^ 2 * c ^ 4 + (-4096 / 49 : k) * b ^ 2 * c ^ 2 * g + (30720 / 343 : k) * c ^ 3 * d ^ 2 + (-49152 / 343 : k) * c * d ^ 2 * g) * kappaQuarticInnerBCDG810 b c d g +
      ((1 / 35 : k) * b ^ 7 + (-16 / 49 : k) * b ^ 3 * c ^ 3 + (128 / 245 : k) * b ^ 3 * c * g + (-960 / 343 : k) * b * c ^ 2 * d ^ 2 + (13824 / 1715 : k) * b * d ^ 2 * g + (-960 / 343 : k) * c ^ 4 * d + (26624 / 1715 : k) * c ^ 2 * d * g + (-36864 / 1715 : k) * d * g ^ 2) * muQuarticInnerBCDG810 b c d g +
      ((-49152 / 1715 : k) * b * c * d * g + (1280 / 343 : k) * c ^ 5 + (-69632 / 1715 : k) * c ^ 3 * g + (147456 / 1715 : k) * c * g ^ 2) * nuQuarticInnerBCDG810 b c d g =
      b ^ 11 := by
  simp only [kappaQuarticInnerBCDG810, muQuarticInnerBCDG810, nuQuarticInnerBCDG810, xiQuarticInnerBCDG810, omicronQuarticInnerBCDG810, piQuarticInnerBCDG810, primitiveQuarticInnerBCDG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBCDG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBCDG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_BCDG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBCDG810 A B C D E F G +
        degreeZeroKappaQuarticNoBCDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBCDG810, degreeZeroKappaQuarticNoBCDG810]
  all_goals module

theorem kappaQuarticFaceBCDG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceBCDG810 A B C D E F G).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 128 : k) * kappaQuarticInnerBCDG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hGpos, hBC, hBD, hBG, hAlt, hElt, hFlt⟩
  simp only [kappaQuarticFaceBCDG810, kappaQuarticInnerBCDG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hcf_B2D : ((B ^ 2 * D)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BG : ((B * G)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hBne hGne]
    omega
  have hcf_BG : ((B * G)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2D, hcf_BC2, hcf_BG]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 10 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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
def muQuarticFaceBCDG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoBCDG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_BCDG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBCDG810 A B C D E F G +
        degreeZeroMuQuarticNoBCDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBCDG810, degreeZeroMuQuarticNoBCDG810]
  all_goals module

theorem muQuarticFaceBCDG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceBCDG810 A B C D E F G).coeff (4 * B.natDegree) =
      (1 / 2048 : k) * muQuarticInnerBCDG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hGpos, hBC, hBD, hBG, hAlt, hElt, hFlt⟩
  simp only [muQuarticFaceBCDG810, muQuarticInnerBCDG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4 : (B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
  have hcf_B4 : (B ^ 4).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_BCD : ((B * C * D)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    omega
  have hcf_BCD : ((B * C * D)).coeff (4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3 : (C ^ 3).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (4 * B.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CG : ((C * G)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul hCne hGne]
    omega
  have hcf_CG : ((C * G)).coeff (4 * B.natDegree) =
      C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B4, hcf_BCD, hcf_C3, hcf_CG]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceBCDG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoBCDG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
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
theorem degreeZeroNuQuartic810_eq_BCDG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBCDG810 A B C D E F G +
        degreeZeroNuQuarticNoBCDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBCDG810, degreeZeroNuQuarticNoBCDG810]
  all_goals module

theorem nuQuarticFaceBCDG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceBCDG810 A B C D E F G).coeff (3 * B.natDegree + C.natDegree) =
      (1 / 512 : k) * nuQuarticInnerBCDG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hGpos, hBC, hBD, hBG, hAlt, hElt, hFlt⟩
  simp only [nuQuarticFaceBCDG810, nuQuarticInnerBCDG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
  have hcf_B3C : ((B ^ 3 * C)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (3 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DG : ((D * G)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hDne hGne]
    omega
  have hcf_DG : ((D * G)).coeff (3 * B.natDegree + C.natDegree) =
      D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_DG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B3C, hcf_BD2, hcf_C2D, hcf_DG]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 15 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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

def omicronQuarticInnerBCEG810 (b c e g : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + 180 * b * c ^ 3 + (-480 : k) * b * c * g + (-320 : k) * b * e ^ 2

def piQuarticInnerBCEG810 (b c e g : k) : k :=
  (-35 : k) * b ^ 4 * c + 180 * b ^ 2 * c * e + 15 * c ^ 4 + (-80 : k) * c ^ 2 * g + (-160 : k) * c * e ^ 2 + 320 * g ^ 2

def primitiveQuarticInnerBCEG810 (b c e g : k) : k :=
  (-265 : k) * b ^ 3 * c ^ 2 + 120 * b ^ 3 * g + 720 * b * c ^ 2 * e + (-640 : k) * b * e * g

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCEG_identity
    (b c e g : k) :
    ((-139 / 21 : k) * b ^ 2 * c + (536 / 63 : k) * c * e) * kappaQuarticInnerBCEG810 b c e g +
      ((-13 / 28 : k) * b ^ 3 + (10 / 7 : k) * b * e) * muQuarticInnerBCEG810 b c e g +
      ((320 / 63 : k) * g) * nuQuarticInnerBCEG810 b c e g +
      ((16 / 63 : k) * b * c) * xiQuarticInnerBCEG810 b c e g +
      ((-23 / 28 : k) * b ^ 2 + (10 / 7 : k) * e) * omicronQuarticInnerBCEG810 b c e g =
      b ^ 7 := by
  simp only [kappaQuarticInnerBCEG810, muQuarticInnerBCEG810, nuQuarticInnerBCEG810, xiQuarticInnerBCEG810, omicronQuarticInnerBCEG810, piQuarticInnerBCEG810, primitiveQuarticInnerBCEG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBCEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBCEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_BCEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBCEG810 A B C D E F G +
        degreeZeroKappaQuarticNoBCEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBCEG810, degreeZeroKappaQuarticNoBCEG810]
  all_goals module

theorem kappaQuarticFaceBCEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceBCEG810 A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) =
      (1 / 128 : k) * kappaQuarticInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hGpos, hBC, hBE, hBG, hAlt, hDlt, hFlt⟩
  simp only [kappaQuarticFaceBCEG810, kappaQuarticInnerBCEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
  have hcf_BC2 : ((B * C ^ 2)).coeff (B.natDegree + 2 * C.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BG : ((B * G)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne hGne]
    omega
  have hcf_BG : ((B * G)).coeff (B.natDegree + 2 * C.natDegree) =
      B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_BC2, hcf_BG]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 16 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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
def muQuarticFaceBCEG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoBCEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 64 : k) • (B * C * D)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_BCEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBCEG810 A B C D E F G +
        degreeZeroMuQuarticNoBCEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBCEG810, degreeZeroMuQuarticNoBCEG810]
  all_goals module

theorem muQuarticFaceBCEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceBCEG810 A B C D E F G).coeff (4 * B.natDegree) =
      (1 / 2048 : k) * muQuarticInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hGpos, hBC, hBE, hBG, hAlt, hDlt, hFlt⟩
  simp only [muQuarticFaceBCEG810, muQuarticInnerBCEG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_C3 : (C ^ 3).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (4 * B.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CG : ((C * G)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul hCne hGne]
    omega
  have hcf_CG : ((C * G)).coeff (4 * B.natDegree) =
      C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (4 * B.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4, hcf_B2E, hcf_C3, hcf_CG, hcf_E2]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceBCEG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 64 : k) • (B * C * E)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoBCEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
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
theorem degreeZeroNuQuartic810_eq_BCEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBCEG810 A B C D E F G +
        degreeZeroNuQuarticNoBCEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBCEG810, degreeZeroNuQuarticNoBCEG810]
  all_goals module

theorem nuQuarticFaceBCEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceBCEG810 A B C D E F G).coeff (3 * B.natDegree + C.natDegree) =
      (1 / 512 : k) * nuQuarticInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hGpos, hBC, hBE, hBG, hAlt, hDlt, hFlt⟩
  simp only [nuQuarticFaceBCEG810, nuQuarticInnerBCEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
  have hcf_B3C : ((B ^ 3 * C)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  rw [hcf_B3C, hcf_BCE]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 25 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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

def omicronQuarticInnerBDEG810 (b d e g : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + (-320 : k) * b * e ^ 2 + (-160 : k) * d ^ 3

def piQuarticInnerBDEG810 (b d e g : k) : k :=
  45 * b ^ 2 * d ^ 2 + (-80 : k) * b * d * g + (-80 : k) * d ^ 2 * e + 160 * g ^ 2

def primitiveQuarticInnerBDEG810 (b d e g : k) : k :=
  (-125 : k) * b ^ 4 * d + 120 * b ^ 3 * g + 680 * b ^ 2 * d * e + (-640 : k) * b * e * g + (-640 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_BDEG_identity
    (b d e g : k) :
    ((-136 / 105 : k) * d ^ 2) * kappaQuarticInnerBDEG810 b d e g +
      ((-13 / 28 : k) * b ^ 3 + (10 / 7 : k) * b * e) * muQuarticInnerBDEG810 b d e g +
      ((-16 / 35 : k) * b * d + (1472 / 105 : k) * g) * nuQuarticInnerBDEG810 b d e g +
      ((-23 / 28 : k) * b ^ 2 + (10 / 7 : k) * e) * omicronQuarticInnerBDEG810 b d e g +
      ((-368 / 105 : k) * d) * piQuarticInnerBDEG810 b d e g =
      b ^ 7 := by
  simp only [kappaQuarticInnerBDEG810, muQuarticInnerBDEG810, nuQuarticInnerBDEG810, xiQuarticInnerBDEG810, omicronQuarticInnerBDEG810, piQuarticInnerBDEG810, primitiveQuarticInnerBDEG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBDEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_BDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBDEG810 A B C D E F G +
        degreeZeroKappaQuarticNoBDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBDEG810, degreeZeroKappaQuarticNoBDEG810]
  all_goals module

theorem kappaQuarticFaceBDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBDEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceBDEG810 A B C D E F G).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 128 : k) * kappaQuarticInnerBDEG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
  simp only [kappaQuarticFaceBDEG810, kappaQuarticInnerBDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hcf_B2D : ((B ^ 2 * D)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BG : ((B * G)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hBne hGne]
    omega
  have hcf_BG : ((B * G)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DE : ((D * E)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (2 * B.natDegree + D.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2D, hcf_BG, hcf_DE]
  ring

end QuarticKills810

end Max11DegreeRoutes
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
/-! # Part 31 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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

def omicronQuarticInnerCDEF810 (c d e f : k) : k :=
  (-10 : k) * c ^ 2 * f + (-25 : k) * c * d * e + (-5 : k) * d ^ 3

def piQuarticInnerCDEF810 (c d e f : k) : k :=
  15 * c ^ 4 + (-240 : k) * c * d * f + (-160 : k) * c * e ^ 2 + (-160 : k) * d ^ 2 * e

def primitiveQuarticInnerCDEF810 (c d e f : k) : k :=
  15 * c ^ 3 * d + (-80 : k) * c * e * f + (-40 : k) * d ^ 2 * f + (-40 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_CDEF_identity
    (c d e f : k) :
    ((147 / 460 : k) * c * e + (33 / 460 : k) * d ^ 2) * kappaQuarticInnerCDEF810 c d e f +
      ((9 / 920 : k) * c * d) * muQuarticInnerCDEF810 c d e f +
      ((-3 / 920 : k) * c ^ 2) * nuQuarticInnerCDEF810 c d e f +
      ((1 / 20 : k) * f) * xiQuarticInnerCDEF810 c d e f +
      ((33 / 460 : k) * e) * omicronQuarticInnerCDEF810 c d e f =
      f ^ 3 := by
  simp only [kappaQuarticInnerCDEF810, muQuarticInnerCDEF810, nuQuarticInnerCDEF810, xiQuarticInnerCDEF810, omicronQuarticInnerCDEF810, piQuarticInnerCDEF810, primitiveQuarticInnerCDEF810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceCDEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoCDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_CDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCDEF810 A B C D E F G +
        degreeZeroKappaQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceCDEF810, degreeZeroKappaQuarticNoCDEF810]
  all_goals module

theorem kappaQuarticFaceCDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCDEF810 A B C D E F G)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (kappaQuarticFaceCDEF810 A B C D E F G).coeff (C.natDegree + F.natDegree) =
      (1 / 16 : k) * kappaQuarticInnerCDEF810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
  simp only [kappaQuarticFaceCDEF810, kappaQuarticInnerCDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_CF : ((C * F)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hCne hFne]
  have hcf_CF : ((C * F)).coeff (C.natDegree + F.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DE : ((D * E)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (C.natDegree + F.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_CF, hcf_DE]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 32 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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
def muQuarticFaceCDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoCDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
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
theorem degreeZeroMuQuartic810_eq_CDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceCDEF810 A B C D E F G +
        degreeZeroMuQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceCDEF810, degreeZeroMuQuarticNoCDEF810]
  all_goals module

theorem muQuarticFaceCDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCDEF810 A B C D E F G)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (muQuarticFaceCDEF810 A B C D E F G).coeff (3 * C.natDegree) =
      (1 / 128 : k) * muQuarticInnerCDEF810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
  simp only [muQuarticFaceCDEF810, muQuarticInnerCDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C3 : (C ^ 3).natDegree = 3 * C.natDegree := by
    rw [natDegree_pow]
  have hcf_C3 : (C ^ 3).coeff (3 * C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_DF : ((D * F)).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (3 * C.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = 3 * C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (3 * C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_C3, hcf_DF, hcf_E2]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceCDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * D)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoCDEF810
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
  - (15 / 128 : k) • (B * D ^ 2)
  + (5 / 16 : k) • (D * G)
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
theorem degreeZeroNuQuartic810_eq_CDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceCDEF810 A B C D E F G +
        degreeZeroNuQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceCDEF810, degreeZeroNuQuarticNoCDEF810]
  all_goals module

theorem nuQuarticFaceCDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCDEF810 A B C D E F G)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (nuQuarticFaceCDEF810 A B C D E F G).coeff (2 * C.natDegree + D.natDegree) =
      (1 / 128 : k) * nuQuarticInnerCDEF810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
  simp only [nuQuarticFaceCDEF810, nuQuarticInnerCDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
  have hcf_C2D : ((C ^ 2 * D)).coeff (2 * C.natDegree + D.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_EF : ((E * F)).natDegree = 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (2 * C.natDegree + D.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_C2D, hcf_EF]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 17 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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
def xiQuarticFaceBCEG810 (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoBCEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2
  - (45 / 262144 * l : k) • (A ^ 4 * D)
  + (9 / 16384 * l : k) • (A ^ 3 * B * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 3)
  - (9 / 8192 * l : k) • (A ^ 3 * F)
  + (9 / 4096 * l : k) • (A ^ 2 * B * E)
  - (9 / 8192 * l : k) • (A ^ 2 * C * D)
  + (171 / 8192 * l : k) • (A * B ^ 2 * D)
  + (9 / 1024 * l : k) • (A * B * C ^ 2)
  + (63 / 2048 * l : k) • (B ^ 3 * C)
  - (9 / 512 * l : k) • (A * C * F)
  - (9 / 512 * l : k) • (A * D * E)
  - (45 / 1024 * l : k) • (B ^ 2 * F)
  - (27 / 256 * l : k) • (B * C * E)
  - (27 / 512 * l : k) • (B * D ^ 2)
  - (63 / 1024 * l : k) • (C ^ 2 * D)
  + (9 / 64 * l : k) • (D * G)
  + (9 / 64 * l : k) • (E * F)
  - (7 / 8192 * beta : k) • (A ^ 3 * D)
  + (7 / 2048 * beta : k) • (A ^ 2 * B * C)
  - (7 / 1024 * beta : k) • (A * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 2 * F)
  + (7 / 256 * beta : k) • (A * B * E)
  + (7 / 512 * beta : k) • (A * C * D)
  + (49 / 1024 * beta : k) • (B ^ 2 * D)
  + (7 / 128 * beta : k) • (B * C ^ 2)
  - (7 / 64 * beta : k) • (C * F)
  - (7 / 64 * beta : k) • (D * E)
  + (3 / 64 * gamma : k) • (A * B * D)
  + (3 / 32 * gamma : k) • (B ^ 2 * C)
  - (3 / 32 * gamma : k) • (B * F)
  - (3 / 16 * gamma : k) • (C * E)
  - (3 / 32 * gamma : k) • D ^ 2
  - (5 / 1024 * delta : k) • (A ^ 2 * D)
  + (5 / 128 * delta : k) • (A * B * C)
  + (5 / 128 * delta : k) • B ^ 3
  - (5 / 64 * delta : k) • (A * F)
  - (5 / 32 * delta : k) • (B * E)
  - (15 / 64 * delta : k) • (C * D)
  + (1 / 32 * epsilon : k) • (A * B ^ 2)
  - (3 / 16 * epsilon : k) • (B * D)
  - (1 / 8 * epsilon : k) • C ^ 2
  + (1 / 2 * epsilon : k) • G
  - (3 / 64 * zeta : k) • (A * D)
  - (3 / 16 * zeta : k) • (B * C)
  + (3 / 8 * zeta : k) • F
  - (1 / 16 * eta : k) • B ^ 2
  + (1 / 4 * eta : k) • E
  + (1 / 8 * theta : k) • D

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuartic810_eq_BCEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceBCEG810 A B C D E F G +
        degreeZeroXiQuarticNoBCEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceBCEG810, degreeZeroXiQuarticNoBCEG810]
  all_goals module

theorem xiQuarticFaceBCEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (xiQuarticFaceBCEG810 A B C D E F G).coeff (2 * B.natDegree + 2 * C.natDegree) =
      (1 / 512 : k) * xiQuarticInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hGpos, hBC, hBE, hBG, hAlt, hDlt, hFlt⟩
  simp only [xiQuarticFaceBCEG810, xiQuarticInnerBCEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = 2 * B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (2 * B.natDegree + 2 * C.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B2G : ((B ^ 2 * G)).natDegree = 2 * B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hGne, natDegree_pow]
    omega
  have hcf_B2G : ((B ^ 2 * G)).coeff (2 * B.natDegree + 2 * C.natDegree) =
      B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_B2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = 2 * B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (2 * B.natDegree + 2 * C.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_EG : ((E * G)).natDegree = 2 * B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hEne hGne]
    omega
  have hcf_EG : ((E * G)).coeff (2 * B.natDegree + 2 * C.natDegree) =
      E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_EG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2C2, hcf_B2G, hcf_C2E, hcf_EG]
  ring

set_option maxHeartbeats 16000000 in
def omicronQuarticFaceBCEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(21 / 4096 : k)) • B ^ 5
  + (5 / 128 : k) • (B ^ 3 * E)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 64 : k) • (B * E ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoBCEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  - (5 / 128 : k) • (A * D * G)
  - (5 / 128 : k) • (A * E * F)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)
  + (135 / 33554432 * l : k) • A ^ 7
  + (225 / 2097152 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (81 / 262144 * l : k) • (A ^ 4 * E)
  - (9 / 65536 * l : k) • (A ^ 3 * B * D)
  + (99 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  - (45 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (189 / 65536 * l : k) • (A * B ^ 4)
  + (9 / 8192 * l : k) • (A ^ 3 * G)
  - (9 / 4096 * l : k) • (A ^ 2 * B * F)
  + (27 / 8192 * l : k) • (A ^ 2 * C * E)
  + (45 / 4096 * l : k) • (A * B ^ 2 * E)
  + (99 / 4096 * l : k) • (A * B * C * D)
  + (9 / 8192 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 512 * l : k) • (A * C * G)
  - (9 / 256 * l : k) • (A * D * F)
  - (27 / 1024 * l : k) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)
  - (45 / 512 * l : k) • (B * D * E)
  - (45 / 1024 * l : k) • (C ^ 2 * E)
  - (27 / 512 * l : k) • (C * D ^ 2)
  + (9 / 64 * l : k) • (E * G)
  + (9 / 128 * l : k) • F ^ 2
  + (35 / 2097152 * beta : k) • A ^ 6
  + (49 / 131072 * beta : k) • (A ^ 4 * C)
  - (35 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 4096 * beta : k) • (A ^ 2 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)
  - (91 / 8192 * beta : k) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (7 / 512 * beta : k) • (A * C * E)
  + (7 / 512 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2
  + (3 / 2048 * gamma : k) • (A ^ 2 * B * C)
  - (9 / 1024 * gamma : k) • (A * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 2 * F)
  + (3 / 128 * gamma : k) • (A * B * E)
  + (3 / 128 * gamma : k) • (A * C * D)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)
  + (9 / 131072 * delta : k) • A ^ 5
  + (5 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 4096 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 128 * delta : k) • (A * B * D)
  + (5 / 512 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2
  - (1 / 256 * epsilon : k) • (A ^ 2 * D)
  + (1 / 32 * epsilon : k) • (A * B * C)
  + (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 16 * epsilon : k) • (A * F)
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  + (9 / 32768 * zeta : k) • A ^ 4
  + (3 / 1024 * zeta : k) • (A ^ 2 * C)
  + (9 / 512 * zeta : k) • (A * B ^ 2)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G
  - (1 / 512 * eta : k) • (A ^ 2 * B)
  - (1 / 32 * eta : k) • (A * D)
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (1 / 1024 * theta : k) • A ^ 3
  + (1 / 64 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuartic810_eq_BCEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceBCEG810 A B C D E F G +
        degreeZeroOmicronQuarticNoBCEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceBCEG810, degreeZeroOmicronQuarticNoBCEG810]
  all_goals module

theorem omicronQuarticFaceBCEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceBCEG810 A B C D E F G).coeff (5 * B.natDegree) =
      (1 / 4096 : k) * omicronQuarticInnerBCEG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hGpos, hBC, hBE, hBG, hAlt, hDlt, hFlt⟩
  simp only [omicronQuarticFaceBCEG810, omicronQuarticInnerBCEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 5 * B.natDegree := by
    rw [natDegree_pow]
  have hcf_B5 : (B ^ 5).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (5 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCG : ((B * C * G)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hGne, natDegree_mul hBne hCne]
    omega
  have hcf_BCG : ((B * C * G)).coeff (5 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BCG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BE2 : ((B * E ^ 2)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_BE2 : ((B * E ^ 2)).coeff (5 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_BE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B5, hcf_B3E, hcf_BC3, hcf_BCG, hcf_BE2]
  ring

end QuarticKills810

end Max11DegreeRoutes
