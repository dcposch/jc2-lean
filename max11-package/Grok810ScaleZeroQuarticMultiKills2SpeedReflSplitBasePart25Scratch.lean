import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBasePart24Scratch

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
