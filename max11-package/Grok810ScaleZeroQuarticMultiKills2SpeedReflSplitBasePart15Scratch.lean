import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBasePart14Scratch

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
