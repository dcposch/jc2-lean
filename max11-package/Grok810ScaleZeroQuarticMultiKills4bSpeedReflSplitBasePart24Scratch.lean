import Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBasePart23Scratch

/-! # Part 24 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`; statements are byte-identical.
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

def omicronQuarticInnerCDEFG810 (c d e f g : k) : k :=
  (-10 : k) * c ^ 2 * f + (-25 : k) * c * d * e + (-5 : k) * d ^ 3 + 40 * f * g

def piQuarticInnerCDEFG810 (c d e f g : k) : k :=
  15 * c ^ 4 + (-80 : k) * c ^ 2 * g + (-240 : k) * c * d * f + (-160 : k) * c * e ^ 2 + (-160 : k) * d ^ 2 * e + 320 * g ^ 2

def primitiveQuarticInnerCDEFG810 (c d e f g : k) : k :=
  15 * c ^ 3 * d + (-40 : k) * c * d * g + (-80 : k) * c * e * f + (-40 : k) * d ^ 2 * f + (-40 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_CDEFG_identity
    (c d e f g : k) :
    ((-37 / 140 : k) * c * e + (13 / 140 : k) * d ^ 2) * kappaQuarticInnerCDEFG810 c d e f g +
      ((-3 / 280 : k) * c * d) * muQuarticInnerCDEFG810 c d e f g +
      ((-9 / 280 : k) * c ^ 2 + (-1 / 35 : k) * g) * nuQuarticInnerCDEFG810 c d e f g +
      ((1 / 20 : k) * f) * xiQuarticInnerCDEFG810 c d e f g +
      ((-3 / 140 : k) * e) * omicronQuarticInnerCDEFG810 c d e f g +
      ((1 / 280 : k) * d) * piQuarticInnerCDEFG810 c d e f g +
      ((-11 / 280 : k) * c) * primitiveQuarticInnerCDEFG810 c d e f g =
      f ^ 3 := by
  simp only [kappaQuarticInnerCDEFG810, muQuarticInnerCDEFG810, nuQuarticInnerCDEFG810, xiQuarticInnerCDEFG810, omicronQuarticInnerCDEFG810, piQuarticInnerCDEFG810, primitiveQuarticInnerCDEFG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoCDEFG810
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
theorem degreeZeroKappaQuartic810_eq_CDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCDEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceCDEFG810, degreeZeroKappaQuarticNoCDEFG810]
  all_goals module

theorem kappaQuarticFaceCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceCDEFG810 A B C D E F G).coeff (C.natDegree + F.natDegree) =
      (1 / 16 : k) * kappaQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  simp only [kappaQuarticFaceCDEFG810, kappaQuarticInnerCDEFG810, coeff_add, coeff_sub, coeff_smul,
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
