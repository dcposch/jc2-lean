import Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitBasePart08Scratch

/-! # Part 9 of `Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitBaseScratch`.

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

def omicronQuarticInnerABCDG810 (a b c d g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * b * g + (-1120 : k) * a * b ^ 3 * c + 2240 * a * b * d ^ 2 + 960 * a * c ^ 2 * d + (-2560 : k) * a * d * g + (-336 : k) * b ^ 5 + 8640 * b ^ 2 * c * d + 2880 * b * c ^ 3 + (-7680 : k) * b * c * g + (-2560 : k) * d ^ 3

def piQuarticInnerABCDG810 (a b c d g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + (-360 : k) * a * b ^ 2 * c ^ 2 + 320 * a * b ^ 2 * g + 640 * a * c * d ^ 2 + (-560 : k) * b ^ 4 * c + 1440 * b ^ 2 * d ^ 2 + 2880 * b * c ^ 2 * d + (-2560 : k) * b * d * g + 240 * c ^ 4 + (-1280 : k) * c ^ 2 * g + 5120 * g ^ 2

def primitiveQuarticInnerABCDG810 (a b c d g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * b * g + 120 * a ^ 2 * b ^ 3 * c + (-800 : k) * a ^ 2 * b * d ^ 2 + 480 * a ^ 2 * c ^ 2 * d + (-1280 : k) * a ^ 2 * d * g + 520 * a * b ^ 5 + (-8640 : k) * a * b ^ 2 * c * d + (-960 : k) * a * b * c ^ 3 + 2560 * a * b * c * g + 2560 * a * d ^ 3 + (-4000 : k) * b ^ 4 * d + (-8480 : k) * b ^ 3 * c ^ 2 + 3840 * b ^ 3 * g + 23040 * b * c * d ^ 2 + 7680 * c ^ 3 * d + (-20480 : k) * c * d * g

set_option maxHeartbeats 32000000 in
theorem quarticInner_ABCDG_identity
    (a b c d g : k) :
    ((2393289 / 16971673600 : k) * a ^ 4 * b ^ 2 + (-8088391 / 4242918400 : k) * a ^ 3 * b * d + (-5695131 / 4242918400 : k) * a ^ 3 * c ^ 2 + (404421 / 106072960 : k) * a ^ 3 * g + (39964389 / 8485836800 : k) * a ^ 2 * b ^ 2 * c + (-1119660827 / 95465664000 : k) * a ^ 2 * d ^ 2 + (2636029687 / 763725312000 : k) * a * b ^ 4 + (-51812979 / 662956000 : k) * a * b * c * d + (-169615603 / 6818976000 : k) * a * c ^ 3 + (75166363 / 852372000 : k) * a * c * g + (2482611 / 662956000 : k) * b ^ 3 * d + (-7352449 / 227299200 : k) * b ^ 2 * c ^ 2 + (10904 / 20717375 : k) * b ^ 2 * g + (-226460681 / 1988868000 : k) * c * d ^ 2) * kappaQuarticInnerABCDG810 a b c d g +
      ((-92896801 / 31821888000 : k) * a * b ^ 2 * d + (23199 / 33147800 : k) * a * b * c ^ 2 + (-7733 / 4143475 : k) * a * b * g + (-741620011 / 95465664000 : k) * b ^ 3 * c + (103414261 / 7955472000 : k) * b * d ^ 2 + (16806223 / 1136496000 : k) * c ^ 2 * d + (-16806223 / 426186000 : k) * d * g) * muQuarticInnerABCDG810 a b c d g +
      ((797763 / 8485836800 : k) * a ^ 3 * b ^ 2 + (-2737373 / 2121459200 : k) * a ^ 2 * b * d + (-1898377 / 2121459200 : k) * a ^ 2 * c ^ 2 + (134807 / 53036480 : k) * a ^ 2 * g + (-4201067 / 5966604000 : k) * a * d ^ 2 + (251521447 / 763725312000 : k) * b ^ 4 + (-2429551 / 1325912000 : k) * b * c * d + (-16806223 / 6818976000 : k) * c ^ 3 + (16806223 / 852372000 : k) * c * g) * nuQuarticInnerABCDG810 a b c d g +
      ((-7733 / 24860850 : k) * a * c * d + (-332993 / 165739000 : k) * b ^ 2 * d + (-3055001 / 1988868000 : k) * b * c ^ 2 + (75939 / 82869500 : k) * b * g) * xiQuarticInnerABCDG810 a b c d g +
      ((797763 / 16971673600 : k) * a ^ 2 * b ^ 2 + (-522729 / 848583680 : k) * a * b * d + (-1898377 / 4242918400 : k) * a * c ^ 2 + (134807 / 106072960 : k) * a * g + (-4710339 / 8485836800 : k) * b ^ 2 * c + (-1 / 2560 : k) * d ^ 2) * omicronQuarticInnerABCDG810 a b c d g +
      ((32323 / 2651824000 : k) * b ^ 3) * piQuarticInnerABCDG810 a b c d g =
      d ^ 5 := by
  simp only [kappaQuarticInnerABCDG810, muQuarticInnerABCDG810, nuQuarticInnerABCDG810, xiQuarticInnerABCDG810, omicronQuarticInnerABCDG810, piQuarticInnerABCDG810, primitiveQuarticInnerABCDG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABCDG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABCDG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)
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
theorem degreeZeroKappaQuartic810_eq_ABCDG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABCDG810 A B C D E F G +
        degreeZeroKappaQuarticNoABCDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABCDG810, degreeZeroKappaQuarticNoABCDG810]
  all_goals module

theorem kappaQuarticFaceABCDG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceABCDG810 A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 512 : k) * kappaQuarticInnerABCDG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hGpos, hAB, hAC, hAD, hAG, hElt, hFlt⟩
  simp only [kappaQuarticFaceABCDG810, kappaQuarticInnerABCDG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2D : ((B ^ 2 * D)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BG : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    omega
  have hcf_BG : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_B2D, hcf_BC2, hcf_BG]
  ring

end QuarticKills810

end Max11DegreeRoutes
