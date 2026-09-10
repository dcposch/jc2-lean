import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBasePart08Scratch

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
