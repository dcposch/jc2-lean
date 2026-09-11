import Grok810ScaleZeroQuarticMultiKills4Part105Scratch

/-! # Part 11 of `Grok810ScaleZeroQuarticMultiKills4Scratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills4Scratch`; statements are byte-identical.
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

set_option maxHeartbeats 64000000 in
theorem omicronQuarticFaceABDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABDEG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceABDEG810 A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * omicronQuarticInnerABDEG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
  simp only [omicronQuarticFaceABDEG810, omicronQuarticInnerABDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BG : ((A ^ 2 * B * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow]
    omega
  have hcf_A2BG : ((A ^ 2 * B * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2BG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2DE : ((A ^ 2 * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DE : ((A ^ 2 * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABD2 : ((A * B * D ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hDne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABD2 : ((A * B * D ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ABD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ADG : ((A * D * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
    omega
  have hcf_ADG : ((A * D * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ADG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B5 : (B ^ 5).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BE2 : ((B * E ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_BE2 : ((B * E ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_BE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D3 : (D ^ 3).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (3 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A3B3, hcf_A2B2D, hcf_A2BG, hcf_A2DE, hcf_ABD2, hcf_ADG, hcf_B5, hcf_B3E, hcf_BE2, hcf_D3]
  ring

set_option maxHeartbeats 64000000 in
def primitiveQuarticFaceABDEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Original monomials 1–10, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk01
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * E * F)

set_option maxHeartbeats 64000000 in
/-- Original monomials 11–20, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk02 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (5 / 128 : k) • (A * B * C * G)
  + (5 / 32 : k) • (A * B * D * F)
  + (15 / 128 : k) • (A * C * D * E)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)

set_option maxHeartbeats 64000000 in
/-- Original monomials 21–30, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk03 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  + (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (171 / 262144 * l : k) • (A ^ 5 * E)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)

set_option maxHeartbeats 64000000 in
/-- Original monomials 31–40, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk04 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (45 / 32768 * l : k) • (A ^ 4 * G)
  - (9 / 4096 * l : k) • (A ^ 3 * B * F)
  + (99 / 8192 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (9 / 4096 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (243 / 8192 * l : k) • (A * B ^ 3 * D)
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)

set_option maxHeartbeats 64000000 in
/-- Original monomials 41–50, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk05 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (27 / 1024 * l : k) • (A ^ 2 * C * G)
  - (9 / 512 * l : k) • (A ^ 2 * D * F)
  + (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)
  + (9 / 1024 * l : k) • (A * B ^ 2 * G)
  + (9 / 256 * l : k) • (A * B * C * F)
  + (45 / 512 * l : k) • (A * B * D * E)
  + (9 / 1024 * l : k) • (A * C ^ 2 * E)
  + (9 / 256 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)

set_option maxHeartbeats 64000000 in
/-- Original monomials 51–60, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk06 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  + (9 / 64 * l : k) • (A * E * G)
  - (9 / 64 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Original monomials 61–70, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk07 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2
  + (25 / 1048576 * beta : k) • A ^ 7
  + (21 / 32768 * beta : k) • (A ^ 5 * C)
  - (119 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 16384 * beta : k) • (A ^ 4 * E)
  - (7 / 2048 * beta : k) • (A ^ 3 * B * D)
  + (21 / 4096 * beta : k) • (A ^ 3 * C ^ 2)
  - (21 / 8192 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (119 / 16384 * beta : k) • (A * B ^ 4)

set_option maxHeartbeats 64000000 in
/-- Original monomials 71–80, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk08 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (21 / 512 * beta : k) • (A ^ 2 * C * E)
  - (7 / 512 * beta : k) • (A ^ 2 * D ^ 2)
  - (21 / 512 * beta : k) • (A * B ^ 2 * E)
  - (7 / 128 * beta : k) • (A * B * C * D)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 64 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Original monomials 81–90, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk09 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2
  + (3 / 2048 * gamma : k) • (A ^ 3 * B * C)
  + (3 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 3 * F)
  + (3 / 256 * gamma : k) • (A ^ 2 * B * E)
  + (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 128 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 128 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)

set_option maxHeartbeats 64000000 in
/-- Original monomials 91–100, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk10 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (3 / 32 * gamma : k) • (A * C * F)
  + (3 / 16 * gamma : k) • (A * D * E)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)
  + (25 / 262144 * delta : k) • A ^ 6
  + (35 / 16384 * delta : k) • (A ^ 4 * C)
  - (25 / 16384 * delta : k) • (A ^ 3 * B ^ 2)

set_option maxHeartbeats 64000000 in
/-- Original monomials 101–110, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk11 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  - (5 / 512 * delta : k) • (A ^ 2 * B * D)
  + (15 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (65 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (5 / 64 * delta : k) • (A * C * E)
  + (5 / 64 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Original monomials 111–120, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk12 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2
  - (1 / 256 * epsilon : k) • (A ^ 3 * D)
  + (1 / 64 * epsilon : k) • (A ^ 2 * B * C)
  - (1 / 32 * epsilon : k) • (A * B ^ 3)
  - (1 / 32 * epsilon : k) • (A ^ 2 * F)
  + (1 / 8 * epsilon : k) • (A * B * E)
  + (1 / 16 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Original monomials 121–130, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk13 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)
  + (3 / 8192 * zeta : k) • A ^ 5
  + (3 / 512 * zeta : k) • (A ^ 3 * C)
  - (3 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (3 / 32 * zeta : k) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)

set_option maxHeartbeats 64000000 in
/-- Original monomials 131–140, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk14 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  - (3 / 16 * zeta : k) • D ^ 2
  - (1 / 512 * eta : k) • (A ^ 3 * B)
  - (1 / 64 * eta : k) • (A ^ 2 * D)
  + (1 / 32 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • B ^ 3
  - (1 / 4 * eta : k) • (A * F)
  - (1 / 4 * eta : k) • (B * E)
  - (1 / 4 * eta : k) • (C * D)
  + (5 / 4096 * theta : k) • A ^ 4
  + (3 / 128 * theta : k) • (A ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Original monomials 141–145, preserving signs and left association. -/
private abbrev grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk15 (acc : k[X])
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  acc
  + (1 / 128 * theta : k) • (A * B ^ 2)
  + (1 / 8 * theta : k) • (A * E)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

set_option maxHeartbeats 64000000 in
def degreeZeroPrimitiveQuarticNoABDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk15
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk14
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk13
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk12
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk11
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk10
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk09
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk08
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk07
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk06
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk05
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk04
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk03
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk02
    (grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk01 l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G) l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuartic810_eq_ABDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticFaceABDEG810 A B C D E F G +
        degreeZeroPrimitiveQuarticNoABDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810,
    rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810, primitiveQuarticFaceABDEG810, degreeZeroPrimitiveQuarticNoABDEG810,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk01,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk02,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk03,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk04,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk05,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk06,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk07,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk08,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk09,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk10,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk11,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk12,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk13,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk14,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk15]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroPrimitiveQuarticNoABDEG810` (145 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPrimitiveQuarticNoABDEG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuarticNoABDEG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 16384 : k), (15 / 8192 : k), (-(5 / 2048) : k),
      (-(5 / 2048) : k), (15 / 1024 : k), (15 / 2048 : k),
      (-(135 / 1024) : k), (-(15 / 1024) : k), (-(265 / 2048) : k),
      (-(5 / 256) : k), (5 / 128 : k), (5 / 32 : k),
      (15 / 128 : k), (85 / 256 : k), (45 / 128 : k),
      (45 / 128 : k), (15 / 128 : k), (-(5 / 16) : k),
      (-(5 / 16) : k), (-(5 / 16) : k), (-(5 / 8) : k),
      (-(5 / 16) : k), (1575 / 268435456 * l : k), (765 / 4194304 * l : k),
      (-(369 / 4194304 * l) : k), (171 / 262144 * l : k), (-(153 / 262144 * l) : k),
      (855 / 524288 * l : k), (-(81 / 131072 * l) : k), (261 / 262144 * l : k),
      (45 / 32768 * l : k), (-(9 / 4096 * l) : k), (99 / 8192 * l : k),
      (-(9 / 4096 * l) : k), (-(9 / 4096 * l) : k), (9 / 8192 * l : k),
      (27 / 16384 * l : k), (-(243 / 8192 * l) : k), (-(387 / 16384 * l) : k),
      (-(567 / 16384 * l) : k), (27 / 1024 * l : k), (-(9 / 512 * l) : k),
      (27 / 1024 * l : k), (9 / 1024 * l : k), (9 / 256 * l : k),
      (45 / 512 * l : k), (9 / 1024 * l : k), (9 / 256 * l : k),
      (27 / 512 * l : k), (45 / 256 * l : k), (45 / 512 * l : k),
      (189 / 1024 * l : k), (63 / 4096 * l : k), (9 / 64 * l : k),
      (-(9 / 64 * l) : k), (-(9 / 64 * l) : k), (-(9 / 32 * l) : k),
      (-(9 / 128 * l) : k), (-(9 / 32 * l) : k), (-(9 / 64 * l) : k),
      (-(9 / 64 * l) : k), (9 / 16 * l : k), (25 / 1048576 * beta : k),
      (21 / 32768 * beta : k), (-(119 / 262144 * beta) : k), (35 / 16384 * beta : k),
      (-(7 / 2048 * beta) : k), (21 / 4096 * beta : k), (-(21 / 8192 * beta) : k),
      (119 / 16384 * beta : k), (21 / 512 * beta : k), (-(7 / 512 * beta) : k),
      (-(21 / 512 * beta) : k), (-(7 / 128 * beta) : k), (-(7 / 128 * beta) : k),
      (-(91 / 1024 * beta) : k), (7 / 64 * beta : k), (7 / 32 * beta : k),
      (7 / 32 * beta : k), (7 / 64 * beta : k), (7 / 64 * beta : k),
      (-(7 / 16 * beta) : k), (3 / 2048 * gamma : k), (3 / 2048 * gamma : k),
      (-(3 / 512 * gamma) : k), (3 / 256 * gamma : k), (3 / 256 * gamma : k),
      (-(9 / 128 * gamma) : k), (-(3 / 128 * gamma) : k), (-(27 / 256 * gamma) : k),
      (-(3 / 32 * gamma) : k), (3 / 16 * gamma : k), (9 / 64 * gamma : k),
      (3 / 8 * gamma : k), (3 / 16 * gamma : k), (3 / 16 * gamma : k),
      (-(3 / 4 * gamma) : k), (25 / 262144 * delta : k), (35 / 16384 * delta : k),
      (-(25 / 16384 * delta) : k), (5 / 1024 * delta : k), (-(5 / 512 * delta) : k),
      (15 / 1024 * delta : k), (-(65 / 1024 * delta) : k), (-(135 / 4096 * delta) : k),
      (5 / 64 * delta : k), (5 / 64 * delta : k), (25 / 128 * delta : k),
      (15 / 32 * delta : k), (5 / 64 * delta : k), (-(5 / 8 * delta) : k),
      (-(5 / 16 * delta) : k), (-(1 / 256 * epsilon) : k), (1 / 64 * epsilon : k),
      (-(1 / 32 * epsilon) : k), (-(1 / 32 * epsilon) : k), (1 / 8 * epsilon : k),
      (1 / 16 * epsilon : k), (7 / 32 * epsilon : k), (1 / 4 * epsilon : k),
      (-(1 / 2 * epsilon) : k), (-(1 / 2 * epsilon) : k), (3 / 8192 * zeta : k),
      (3 / 512 * zeta : k), (-(3 / 2048 * zeta) : k), (3 / 128 * zeta : k),
      (3 / 32 * zeta : k), (27 / 128 * zeta : k), (-(3 / 8 * zeta) : k),
      (-(3 / 8 * zeta) : k), (-(3 / 16 * zeta) : k), (-(1 / 512 * eta) : k),
      (-(1 / 64 * eta) : k), (1 / 32 * eta : k), (3 / 64 * eta : k),
      (-(1 / 4 * eta) : k), (-(1 / 4 * eta) : k), (-(1 / 4 * eta) : k),
      (5 / 4096 * theta : k), (3 / 128 * theta : k), (1 / 128 * theta : k),
      (1 / 8 * theta : k), (-(1 / 8 * theta) : k), (-(1 / 16 * theta) : k),
      (1 * theta : k)]
      [
      [3, 1, 2, 0, 0, 0, 0], [2, 3, 1, 0, 0, 0, 0], [3, 0, 1, 0, 0, 1, 0], [2, 2, 0, 0, 0, 1, 0],
      [2, 1, 1, 0, 1, 0, 0], [2, 0, 2, 1, 0, 0, 0], [1, 2, 1, 1, 0, 0, 0], [1, 1, 3, 0, 0, 0, 0],
      [0, 3, 2, 0, 0, 0, 0], [2, 0, 0, 0, 1, 1, 0], [1, 1, 1, 0, 0, 0, 1], [1, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 1, 1, 0, 0], [0, 2, 1, 0, 0, 1, 0], [0, 1, 2, 0, 1, 0, 0], [0, 1, 1, 2, 0, 0, 0],
      [0, 0, 3, 1, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 0, 2, 0], [0, 0, 1, 1, 0, 0, 1],
      [0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 2, 0, 1, 0], [8, 0, 0, 0, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0],
      [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0], [4, 1, 0, 1, 0, 0, 0], [4, 0, 2, 0, 0, 0, 0],
      [3, 2, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 1], [3, 1, 0, 0, 0, 1, 0],
      [3, 0, 1, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0],
      [2, 0, 3, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [2, 0, 1, 0, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0], [2, 0, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 1],
      [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 2, 0, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1],
      [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0],
      [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2], [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0],
      [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0],
      [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 0, 1, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0],
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 0, 2, 0, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0], [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0],
      [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0],
      [0, 0, 0, 0, 1, 1, 0], [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0],
      [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0],
      [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0],
      [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0],
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 1]] := by
  simp only [degreeZeroPrimitiveQuarticNoABDEG810,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk01,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk02,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk03,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk04,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk05,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk06,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk07,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk08,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk09,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk10,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk11,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk12,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk13,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk14,
    grok810MultiKills4Part11SpeedT_degreeZeroPrimitiveQuarticNoABDEG810_chunk15, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuarticNoABDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDEG810 A B C D E F G) :
    (degreeZeroPrimitiveQuarticNoABDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroPrimitiveQuarticNoABDEG810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticFaceABDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABDEG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (primitiveQuarticFaceABDEG810 A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * primitiveQuarticInnerABDEG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
  simp only [primitiveQuarticFaceABDEG810, primitiveQuarticInnerABDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A4B3 : ((A ^ 4 * B ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A4B3 : ((A ^ 4 * B ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A4B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3B2D : ((A ^ 3 * B ^ 2 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A3B2D : ((A ^ 3 * B ^ 2 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A3B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3BG : ((A ^ 3 * B * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne, natDegree_pow]
    omega
  have hcf_A3BG : ((A ^ 3 * B * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A3BG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A3DE : ((A ^ 3 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 3 hAne) hDne, natDegree_pow]
    omega
  have hcf_A3DE : ((A ^ 3 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A3DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2BD2 : ((A ^ 2 * B * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hDne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BD2 : ((A ^ 2 * B * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2DG : ((A ^ 2 * D * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DG : ((A ^ 2 * D * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2DG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB5 : ((A * B ^ 5)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 5 hBne), natDegree_pow]
    omega
  have hcf_AB5 : ((A * B ^ 5)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 5 := by
    rw [← hdeg_AB5, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB3E : ((A * B ^ 3 * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3E : ((A * B ^ 3 * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_AB3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABE2 : ((A * B * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hEne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABE2 : ((A * B * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_ABE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AD3 : ((A * D ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hDne), natDegree_pow]
    omega
  have hcf_AD3 : ((A * D ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 3 := by
    rw [← hdeg_AD3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4D : ((B ^ 4 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hDne, natDegree_pow]
    omega
  have hcf_B4D : ((B ^ 4 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 4 * D.leadingCoeff := by
    rw [← hdeg_B4D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3G : ((B ^ 3 * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hGne, natDegree_pow]
    omega
  have hcf_B3G : ((B ^ 3 * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * G.leadingCoeff := by
    rw [← hdeg_B3G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2DE : ((B ^ 2 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2DE : ((B ^ 2 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BEG : ((B * E * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hEne) hGne, natDegree_mul hBne hEne]
    omega
  have hcf_BEG : ((B * E * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BEG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_DE2 : ((D * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_DE2 : ((D * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_DE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A4B3, hcf_A3B2D, hcf_A3BG, hcf_A3DE, hcf_A2BD2, hcf_A2DG, hcf_AB5, hcf_AB3E, hcf_ABE2, hcf_AD3, hcf_B4D, hcf_B3G, hcf_B2DE, hcf_BEG, hcf_DE2]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCone_ABDEG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDEG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerABDEG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoABDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceABDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ABDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerABDEG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoABDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceABDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ABDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerABDEG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoABDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceABDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ABDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerABDEG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoABDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceABDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_ABDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerABDEG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoABDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceABDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_ABDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveQuarticInnerABDEG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveQuarticNoABDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := primitiveQuarticFaceABDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hGpos, hAB, hAD, hAE, hAG, hClt, hFlt⟩
      omega
    rw [degreeZeroPrimitiveQuartic810_eq_ABDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_ABDEG_identity A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff
  have hpow : D.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)

end QuarticKills810

end Max11DegreeRoutes
