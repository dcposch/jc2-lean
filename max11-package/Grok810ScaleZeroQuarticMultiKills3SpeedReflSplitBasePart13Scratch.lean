import Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitBasePart12Scratch

/-! # Part 13 of `Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitBaseScratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitBaseScratch`; statements are byte-identical.
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

def omicronQuarticInnerABCEF810 (a b c e f : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * c * f + (-1120 : k) * a * b ^ 3 * c + 1600 * a * b ^ 2 * f + 1920 * a * b * c * e + (-2560 : k) * a * e * f + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + 2880 * b * c ^ 3 + (-5120 : k) * b * e ^ 2 + (-5120 : k) * c ^ 2 * f

def piQuarticInnerABCEF810 (a b c e f : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-360 : k) * a * b ^ 2 * c ^ 2 + 640 * a * b * c * f + (-1280 : k) * a * f ^ 2 + (-560 : k) * b ^ 4 * c + 800 * b ^ 3 * f + 2880 * b ^ 2 * c * e + (-3840 : k) * b * e * f + 240 * c ^ 4 + (-2560 : k) * c * e ^ 2

def primitiveQuarticInnerABCEF810 (a b c e f : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * c * f + 120 * a ^ 2 * b ^ 3 * c + (-160 : k) * a ^ 2 * b ^ 2 * f + 960 * a ^ 2 * b * c * e + (-1280 : k) * a ^ 2 * e * f + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + (-960 : k) * a * b * c ^ 3 + 5120 * a * b * e ^ 2 + (-8480 : k) * b ^ 3 * c ^ 2 + 21760 * b ^ 2 * c * f + 23040 * b * c ^ 2 * e + (-20480 : k) * b * f ^ 2 + (-40960 : k) * c * e * f

set_option maxHeartbeats 32000000 in
theorem quarticInner_ABCEF_identity
    (a b c e f : k) :
    ((18809 / 73195520 : k) * a ^ 3 * b * c + (-4451191 / 5270077440 : k) * a ^ 3 * f + (2883677 / 15458893824 : k) * a ^ 2 * b ^ 3 + (-6109073 / 2635038720 : k) * a ^ 2 * b * e + (148514633 / 28985425920 : k) * a * b * c ^ 2 + (-517897 / 40257536 : k) * a * c * f + (17547061 / 1449271296 : k) * b ^ 3 * c + (-155492563 / 7246356480 : k) * b ^ 2 * f + (-10946539 / 226448640 : k) * b * c * e + (1581403 / 45289728 : k) * e * f) * kappaQuarticInnerABCEF810 a b c e f +
      ((157389 / 402575360 : k) * a * b ^ 2 * c + (-166879 / 301931520 : k) * a * b * f + (-17803 / 37741440 : k) * a * c * e + (21 / 81920 : k) * b ^ 4 + (-41 / 10240 : k) * b ^ 2 * e + (79 / 571840 : k) * c ^ 3 + (1 / 320 : k) * e ^ 2) * muQuarticInnerABCEF810 a b c e f +
      ((656303 / 3623178240 : k) * a ^ 2 * b * c + (-32642611 / 57970851840 : k) * a ^ 2 * f + (-15886613 / 14492712960 : k) * a * b * e + (5563793 / 3220602880 : k) * b * c ^ 2 + (-669547 / 113224320 : k) * c * f) * nuQuarticInnerABCEF810 a b c e f +
      ((302651 / 3623178240 : k) * a ^ 2 * b ^ 2 + (17803 / 181158912 : k) * a * c ^ 2 + (94829 / 82344960 : k) * b ^ 2 * c + (-62119 / 16468992 : k) * b * f + (-6941 / 5146560 : k) * c * e) * xiQuarticInnerABCEF810 a b c e f +
      ((109897 / 1449271296 : k) * a * b * c + (-860263 / 3864723456 : k) * a * f + (7 / 262144 : k) * b ^ 3 + (-13 / 32768 : k) * b * e) * omicronQuarticInnerABCEF810 a b c e f +
      ((219227 / 7246356480 : k) * a * b ^ 2 + (-17803 / 301931520 : k) * a * e + (79 / 1715520 : k) * c ^ 2) * piQuarticInnerABCEF810 a b c e f +
      ((-62119 / 1054015488 : k) * f) * primitiveQuarticInnerABCEF810 a b c e f =
      e ^ 4 := by
  simp only [kappaQuarticInnerABCEF810, muQuarticInnerABCEF810, nuQuarticInnerABCEF810, xiQuarticInnerABCEF810, omicronQuarticInnerABCEF810, piQuarticInnerABCEF810, primitiveQuarticInnerABCEF810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABCEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABCEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_ABCEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABCEF810 A B C D E F G +
        degreeZeroKappaQuarticNoABCEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABCEF810, degreeZeroKappaQuarticNoABCEF810]
  all_goals module

theorem kappaQuarticFaceABCEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (kappaQuarticFaceABCEF810 A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 512 : k) * kappaQuarticInnerABCEF810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hAB, hAC, hAE, hAF, hDlt, hGlt⟩
  simp only [kappaQuarticFaceABCEF810, kappaQuarticInnerABCEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CF : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    omega
  have hcf_CF : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_BC2, hcf_CF]
  ring

end QuarticKills810

end Max11DegreeRoutes
