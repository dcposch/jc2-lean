import Grok810ScaleZeroQuarticMultiKills4Scratch

/-! # Quartic Stage A multi-cone certificates (part 4b: 5-letter cones ACDEF–CDEFG) -/

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

def kappaQuarticInnerACDEF810 (a c d e f : k) : k :=
  5 * c * f + 5 * d * e

def muQuarticInnerACDEF810 (a c d e f : k) : k :=
  (-5 : k) * a * d ^ 2 + (-5 : k) * c ^ 3 + 40 * d * f + 20 * e ^ 2

def nuQuarticInnerACDEF810 (a c d e f : k) : k :=
  (-5 : k) * a * c * f + (-5 : k) * a * d * e + (-15 : k) * c ^ 2 * d + 40 * e * f

def xiQuarticInnerACDEF810 (a c d e f : k) : k :=
  (-10 : k) * a * d * f + (-15 : k) * c ^ 2 * e + (-15 : k) * c * d ^ 2 + 20 * f ^ 2

def omicronQuarticInnerACDEF810 (a c d e f : k) : k :=
  (-5 : k) * a ^ 2 * c * f + (-5 : k) * a ^ 2 * d * e + 30 * a * c ^ 2 * d + (-80 : k) * a * e * f + (-160 : k) * c ^ 2 * f + (-400 : k) * c * d * e + (-80 : k) * d ^ 3

def piQuarticInnerACDEF810 (a c d e f : k) : k :=
  40 * a * c * d ^ 2 + (-80 : k) * a * f ^ 2 + 15 * c ^ 4 + (-240 : k) * c * d * f + (-160 : k) * c * e ^ 2 + (-160 : k) * d ^ 2 * e

def primitiveQuarticInnerACDEF810 (a c d e f : k) : k :=
  (-5 : k) * a ^ 3 * c * f + (-5 : k) * a ^ 3 * d * e + 15 * a ^ 2 * c ^ 2 * d + (-40 : k) * a ^ 2 * e * f + 240 * a * c * d * e + 80 * a * d ^ 3 + 240 * c ^ 3 * d + (-1280 : k) * c * e * f + (-640 : k) * d ^ 2 * f + (-640 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_ACDEF_identity
    (a c d e f : k) :
    ((2097 / 99520 : k) * a ^ 3 * f + (7771 / 149280 : k) * a ^ 2 * c * d + (199 / 622 : k) * a * c * f + (-175 / 3732 : k) * a * d * e + (3917 / 6220 : k) * c ^ 2 * d + (1051 / 4665 : k) * e * f) * kappaQuarticInnerACDEF810 a c d e f +
      ((111 / 6220 : k) * c ^ 3 + (233 / 6220 : k) * d * f + (1 / 20 : k) * e ^ 2) * muQuarticInnerACDEF810 a c d e f +
      ((699 / 49760 : k) * a ^ 2 * f + (2837 / 74640 : k) * a * c * d + (-452 / 4665 : k) * d * e) * nuQuarticInnerACDEF810 a c d e f +
      ((-1051 / 18660 : k) * c * e + (-233 / 3110 : k) * d ^ 2) * xiQuarticInnerACDEF810 a c d e f +
      ((699 / 99520 : k) * a * f + (699 / 49760 : k) * c * d) * omicronQuarticInnerACDEF810 a c d e f +
      ((37 / 6220 : k) * c ^ 2) * piQuarticInnerACDEF810 a c d e f =
      e ^ 4 := by
  simp only [kappaQuarticInnerACDEF810, muQuarticInnerACDEF810, nuQuarticInnerACDEF810, xiQuarticInnerACDEF810, omicronQuarticInnerACDEF810, piQuarticInnerACDEF810, primitiveQuarticInnerACDEF810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoACDEF810
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
theorem degreeZeroKappaQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACDEF810 A B C D E F G +
        degreeZeroKappaQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceACDEF810, degreeZeroKappaQuarticNoACDEF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoACDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoACDEF810]
  compute_degree
  omega

theorem kappaQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (kappaQuarticFaceACDEF810 A B C D E F G).coeff (C.natDegree + F.natDegree) =
      (1 / 16 : k) * kappaQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [kappaQuarticFaceACDEF810, kappaQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
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

set_option maxHeartbeats 16000000 in
def muQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoACDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceACDEF810 A B C D E F G +
        degreeZeroMuQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceACDEF810, degreeZeroMuQuarticNoACDEF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoACDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEF810 A B C D E F G) :
    (degreeZeroMuQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoACDEF810]
  compute_degree
  omega

theorem muQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (muQuarticFaceACDEF810 A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) =
      (1 / 128 : k) * muQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [muQuarticFaceACDEF810, muQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_DF : ((D * F)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (A.natDegree + 2 * D.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * D.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AD2, hcf_C3, hcf_DF, hcf_E2]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoACDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
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
theorem degreeZeroNuQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceACDEF810 A B C D E F G +
        degreeZeroNuQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceACDEF810, degreeZeroNuQuarticNoACDEF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoACDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEF810 A B C D E F G) :
    (degreeZeroNuQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + C.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroNuQuarticNoACDEF810]
  compute_degree
  omega

theorem nuQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (nuQuarticFaceACDEF810 A B C D E F G).coeff (A.natDegree + C.natDegree + F.natDegree) =
      (1 / 128 : k) * nuQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [nuQuarticFaceACDEF810, nuQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_ACF : ((A * C * F)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) hFne, natDegree_mul hAne hCne]
  have hcf_ACF : ((A * C * F)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ACF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ADE : ((A * D * E)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    omega
  have hcf_ADE : ((A * D * E)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ADE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_EF : ((E * F)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_ACF, hcf_ADE, hcf_C2D, hcf_EF]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoACDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  + (5 / 16 : k) • (E * G)
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
theorem degreeZeroXiQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceACDEF810 A B C D E F G +
        degreeZeroXiQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceACDEF810, degreeZeroXiQuarticNoACDEF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoACDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEF810 A B C D E F G) :
    (degreeZeroXiQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + D.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroXiQuarticNoACDEF810]
  compute_degree
  omega

theorem xiQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (xiQuarticFaceACDEF810 A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) =
      (1 / 128 : k) * xiQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [xiQuarticFaceACDEF810, xiQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_ADF : ((A * D * F)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
  have hcf_ADF : ((A * D * F)).coeff (A.natDegree + D.natDegree + F.natDegree) =
      A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ADF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + D.natDegree + F.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (A.natDegree + D.natDegree + F.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_F2 : (F ^ 2).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (A.natDegree + D.natDegree + F.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_ADF, hcf_C2E, hcf_CD2, hcf_F2]
  ring

set_option maxHeartbeats 16000000 in
def omicronQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 2 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  - (5 / 128 : k) • (A * E * F)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoACDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * D * G)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
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
theorem degreeZeroOmicronQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceACDEF810 A B C D E F G +
        degreeZeroOmicronQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceACDEF810, degreeZeroOmicronQuarticNoACDEF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoACDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEF810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + C.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroOmicronQuarticNoACDEF810]
  compute_degree
  omega

theorem omicronQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (omicronQuarticFaceACDEF810 A B C D E F G).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      (1 / 2048 : k) * omicronQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [omicronQuarticFaceACDEF810, omicronQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2CF : ((A ^ 2 * C * F)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hCne, natDegree_pow]
  have hcf_A2CF : ((A ^ 2 * C * F)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A2CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2DE : ((A ^ 2 * D * E)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DE : ((A ^ 2 * D * E)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AC2D : ((A * C ^ 2 * D)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_AC2D : ((A * C ^ 2 * D)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AEF : ((A * E * F)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hEne) hFne, natDegree_mul hAne hEne]
    omega
  have hcf_AEF : ((A * E * F)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_AEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2F : ((C ^ 2 * F)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hFne, natDegree_pow]
    omega
  have hcf_C2F : ((C ^ 2 * F)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_C2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDE : ((C * D * E)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hEne, natDegree_mul hCne hDne]
    omega
  have hcf_CDE : ((C * D * E)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_CDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D3 : (D ^ 3).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A2CF, hcf_A2DE, hcf_AC2D, hcf_AEF, hcf_C2F, hcf_CDE, hcf_D3]
  ring

set_option maxHeartbeats 16000000 in
def piQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoACDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2
  + (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceACDEF810 A B C D E F G +
        degreeZeroPiQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceACDEF810, degreeZeroPiQuarticNoACDEF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoACDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEF810 A B C D E F G) :
    (degreeZeroPiQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + C.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroPiQuarticNoACDEF810]
  compute_degree
  omega

theorem piQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (piQuarticFaceACDEF810 A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      (1 / 256 : k) * piQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [piQuarticFaceACDEF810, piQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_ACD2 : ((A * C * D ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne, natDegree_pow]
  have hcf_ACD2 : ((A * C * D ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ACD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AF2 : ((A * F ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne), natDegree_pow]
    omega
  have hcf_AF2 : ((A * F ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_AF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C4 : (C ^ 4).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C4 : (C ^ 4).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CDF : ((C * D * F)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hFne, natDegree_mul hCne hDne]
    omega
  have hcf_CDF : ((C * D * F)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      C.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CE2 : ((C * E ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_CE2 : ((C * E ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_CE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D2E : ((D ^ 2 * E)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hEne, natDegree_pow]
    omega
  have hcf_D2E : ((D ^ 2 * E)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      D.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_D2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_ACD2, hcf_AF2, hcf_C4, hcf_CDF, hcf_CE2, hcf_D2E]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_ACDEF_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
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
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoACDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceACDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (C.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ACDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 16 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoACDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceACDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ACDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoACDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceACDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + C.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ACDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoACDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceACDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_ACDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoACDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceACDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + C.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_ACDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoACDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceACDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_ACDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 256 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_ACDEF_identity A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
  have hpow : E.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner] at hid
    simpa using hid.symm
  have hlc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)


def kappaQuarticInnerBCDEF810 (b c d e f : k) : k :=
  (-15 : k) * b ^ 2 * d + (-15 : k) * b * c ^ 2 + 40 * c * f + 40 * d * e

def muQuarticInnerBCDEF810 (b c d e f : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * d * f + 320 * e ^ 2

def nuQuarticInnerBCDEF810 (b c d e f : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b ^ 2 * f + (-120 : k) * b * c * e + (-60 : k) * b * d ^ 2 + (-60 : k) * c ^ 2 * d + 160 * e * f

def xiQuarticInnerBCDEF810 (b c d e f : k) : k :=
  55 * b ^ 3 * d + 90 * b ^ 2 * c ^ 2 + (-200 : k) * b * c * f + (-200 : k) * b * d * e + (-120 : k) * c ^ 2 * e + (-120 : k) * c * d ^ 2 + 160 * f ^ 2

def omicronQuarticInnerBCDEF810 (b c d e f : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-640 : k) * b * d * f + (-320 : k) * b * e ^ 2 + (-320 : k) * c ^ 2 * f + (-800 : k) * c * d * e + (-160 : k) * d ^ 3

def piQuarticInnerBCDEF810 (b c d e f : k) : k :=
  (-35 : k) * b ^ 4 * c + 50 * b ^ 3 * f + 180 * b ^ 2 * c * e + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + (-240 : k) * b * e * f + 15 * c ^ 4 + (-240 : k) * c * d * f + (-160 : k) * c * e ^ 2 + (-160 : k) * d ^ 2 * e

def primitiveQuarticInnerBCDEF810 (b c d e f : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 680 * b ^ 2 * c * f + 680 * b ^ 2 * d * e + 720 * b * c ^ 2 * e + 720 * b * c * d ^ 2 + (-640 : k) * b * f ^ 2 + 240 * c ^ 3 * d + (-1280 : k) * c * e * f + (-640 : k) * d ^ 2 * f + (-640 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCDEF_identity
    (b c d e f : k) :
    ((5856019861 / 12769491545600 : k) * b ^ 4 * d + (-54944173451 / 12097413043200 : k) * b ^ 3 * c ^ 2 + (4117052321 / 2094994706700 : k) * b ^ 2 * c * f + (-153008969 / 167599576536 : k) * b ^ 2 * d * e + (670351762721 / 67039830614400 : k) * b * c ^ 2 * e + (3117429893 / 1596186443200 : k) * b * c * d ^ 2 + (66994308781 / 2394279664800 : k) * b * f ^ 2 + (-38833312739 / 3351991530720 : k) * c ^ 3 * d + (622239207463 / 12569968240200 : k) * c * e * f + (-87284367397 / 2793326275600 : k) * d ^ 2 * f + (-27178691719 / 4189989413400 : k) * d * e ^ 2) * kappaQuarticInnerBCDEF810 b c d e f +
      ((-887750649 / 5586652551200 : k) * b ^ 3 * f + (149192413 / 558665255120 : k) * b ^ 2 * c * e + (-6520437989 / 17877288163840 : k) * b * c ^ 2 * d + (13439415371 / 5586652551200 : k) * b * e * f + (-29381166921 / 178772881638400 : k) * c ^ 4 + (-16804476719 / 4788559329600 : k) * c * d * f + (-5679925609 / 2793326275600 : k) * c * e ^ 2 + (-40980415589 / 33519915307200 : k) * d ^ 2 * e) * muQuarticInnerBCDEF810 b c d e f +
      ((-1995531 / 14701717240 : k) * b ^ 3 * e + (-10344927983 / 8379978826800 : k) * b * c ^ 3 + (-79495316587 / 5586652551200 : k) * b * d * f + (-2079564153 / 2793326275600 : k) * b * e ^ 2 + (1618396469 / 1795709748600 : k) * c ^ 2 * f + (42759268939 / 6284984120100 : k) * c * d * e + (5856019861 / 6703983061440 : k) * d ^ 3) * nuQuarticInnerBCDEF810 b c d e f +
      ((-8486878607 / 15323389854720 : k) * b ^ 2 * c ^ 2 + (978366343 / 1197139832400 : k) * b * c * f + (933757931 / 2394279664800 : k) * b * d * e + (10603295 / 6720785024 : k) * c ^ 2 * e + (2237965889 / 1915423731840 : k) * c * d ^ 2 + (1 / 160 : k) * f ^ 2) * xiQuarticInnerBCDEF810 b c d e f +
      ((-295916883 / 1117330510240 : k) * b ^ 2 * f + (-225022591 / 558665255120 : k) * b * c * e + (-5856019861 / 17877288163840 : k) * b * d ^ 2 + (-5380445271 / 4469322040960 : k) * c ^ 2 * d + (5679925609 / 1117330510240 : k) * e * f) * omicronQuarticInnerBCDEF810 b c d e f +
      ((260469737 / 698331568900 : k) * b ^ 2 * e + (3455893409 / 2793326275600 : k) * b * c * d + (-9793722307 / 11173305102400 : k) * c ^ 3 + (-332683353 / 19671311800 : k) * d * f + (-5679925609 / 1396663137800 : k) * e ^ 2) * piQuarticInnerBCDEF810 b c d e f =
      f ^ 4 := by
  simp only [kappaQuarticInnerBCDEF810, muQuarticInnerBCDEF810, nuQuarticInnerBCDEF810, xiQuarticInnerBCDEF810, omicronQuarticInnerBCDEF810, piQuarticInnerBCDEF810, primitiveQuarticInnerBCDEF810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBCDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBCDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
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
theorem degreeZeroKappaQuartic810_eq_BCDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBCDEF810 A B C D E F G +
        degreeZeroKappaQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBCDEF810, degreeZeroKappaQuarticNoBCDEF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBCDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoBCDEF810]
  compute_degree
  omega

theorem kappaQuarticFaceBCDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (kappaQuarticFaceBCDEF810 A B C D E F G).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 128 : k) * kappaQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  simp only [kappaQuarticFaceBCDEF810, kappaQuarticInnerBCDEF810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_CF : ((C * F)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hCne hFne]
    omega
  have hcf_CF : ((C * F)).coeff (2 * B.natDegree + D.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DE : ((D * E)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (2 * B.natDegree + D.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2D, hcf_BC2, hcf_CF, hcf_DE]
  ring

set_option maxHeartbeats 16000000 in
def muQuarticFaceBCDEF810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoBCDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_BCDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBCDEF810 A B C D E F G +
        degreeZeroMuQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBCDEF810, degreeZeroMuQuarticNoBCDEF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoBCDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G) :
    (degreeZeroMuQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoBCDEF810]
  compute_degree
  omega

theorem muQuarticFaceBCDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (muQuarticFaceBCDEF810 A B C D E F G).coeff (4 * B.natDegree) =
      (1 / 2048 : k) * muQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  simp only [muQuarticFaceBCDEF810, muQuarticInnerBCDEF810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_DF : ((D * F)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (4 * B.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (4 * B.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4, hcf_B2E, hcf_BCD, hcf_C3, hcf_DF, hcf_E2]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceBCDEF810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoBCDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
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
theorem degreeZeroNuQuartic810_eq_BCDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBCDEF810 A B C D E F G +
        degreeZeroNuQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBCDEF810, degreeZeroNuQuarticNoBCDEF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoBCDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G) :
    (degreeZeroNuQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroNuQuarticNoBCDEF810]
  compute_degree
  omega

theorem nuQuarticFaceBCDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (nuQuarticFaceBCDEF810 A B C D E F G).coeff (3 * B.natDegree + C.natDegree) =
      (1 / 512 : k) * nuQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  simp only [nuQuarticFaceBCDEF810, nuQuarticInnerBCDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
  have hcf_B3C : ((B ^ 3 * C)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2F : ((B ^ 2 * F)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hFne, natDegree_pow]
    omega
  have hcf_B2F : ((B ^ 2 * F)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
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
  have hdeg_EF : ((E * F)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (3 * B.natDegree + C.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B3C, hcf_B2F, hcf_BCE, hcf_BD2, hcf_C2D, hcf_EF]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceBCDEF810 (A B C D E F G : k[X]) : k[X] :=
  (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoBCDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  + (5 / 16 : k) • (E * G)
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
theorem degreeZeroXiQuartic810_eq_BCDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceBCDEF810 A B C D E F G +
        degreeZeroXiQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceBCDEF810, degreeZeroXiQuarticNoBCDEF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoBCDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G) :
    (degreeZeroXiQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroXiQuarticNoBCDEF810]
  compute_degree
  omega

theorem xiQuarticFaceBCDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (xiQuarticFaceBCDEF810 A B C D E F G).coeff (3 * B.natDegree + D.natDegree) =
      (1 / 1024 : k) * xiQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  simp only [xiQuarticFaceBCDEF810, xiQuarticInnerBCDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
  have hcf_B3D : ((B ^ 3 * D)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_BCF : ((B * C * F)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hFne, natDegree_mul hBne hCne]
    omega
  have hcf_BCF : ((B * C * F)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BCF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BDE : ((B * D * E)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hEne, natDegree_mul hBne hDne]
    omega
  have hcf_BDE : ((B * D * E)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (3 * B.natDegree + D.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (3 * B.natDegree + D.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_F2 : (F ^ 2).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (3 * B.natDegree + D.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B3D, hcf_B2C2, hcf_BCF, hcf_BDE, hcf_C2E, hcf_CD2, hcf_F2]
  ring

set_option maxHeartbeats 16000000 in
def omicronQuarticFaceBCDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(21 / 4096 : k)) • B ^ 5
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoBCDEF810
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
  - (5 / 128 : k) • (A * D * G)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
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
theorem degreeZeroOmicronQuartic810_eq_BCDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceBCDEF810 A B C D E F G +
        degreeZeroOmicronQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceBCDEF810, degreeZeroOmicronQuarticNoBCDEF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoBCDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroOmicronQuarticNoBCDEF810]
  compute_degree
  omega

theorem omicronQuarticFaceBCDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (omicronQuarticFaceBCDEF810 A B C D E F G).coeff (5 * B.natDegree) =
      (1 / 4096 : k) * omicronQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  simp only [omicronQuarticFaceBCDEF810, omicronQuarticInnerBCDEF810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_B2CD : ((B ^ 2 * C * D)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hDne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CD : ((B ^ 2 * C * D)).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_B2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (5 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDF : ((B * D * F)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hFne, natDegree_mul hBne hDne]
    omega
  have hcf_BDF : ((B * D * F)).coeff (5 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BE2 : ((B * E ^ 2)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_BE2 : ((B * E ^ 2)).coeff (5 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_BE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2F : ((C ^ 2 * F)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hFne, natDegree_pow]
    omega
  have hcf_C2F : ((C ^ 2 * F)).coeff (5 * B.natDegree) =
      C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_C2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDE : ((C * D * E)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hEne, natDegree_mul hCne hDne]
    omega
  have hcf_CDE : ((C * D * E)).coeff (5 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_CDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D3 : (D ^ 3).natDegree = 5 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (5 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B5, hcf_B3E, hcf_B2CD, hcf_BC3, hcf_BDF, hcf_BE2, hcf_C2F, hcf_CDE, hcf_D3]
  ring

set_option maxHeartbeats 16000000 in
def piQuarticFaceBCDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 256 : k)) • (B ^ 4 * C)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoBCDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2
  + (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_BCDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceBCDEF810 A B C D E F G +
        degreeZeroPiQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceBCDEF810, degreeZeroPiQuarticNoBCDEF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoBCDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G) :
    (degreeZeroPiQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroPiQuarticNoBCDEF810]
  compute_degree
  omega

theorem piQuarticFaceBCDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (piQuarticFaceBCDEF810 A B C D E F G).coeff (4 * B.natDegree + C.natDegree) =
      (1 / 256 : k) * piQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  simp only [piQuarticFaceBCDEF810, piQuarticInnerBCDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4C : ((B ^ 4 * C)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hCne, natDegree_pow]
  have hcf_B4C : ((B ^ 4 * C)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 * C.leadingCoeff := by
    rw [← hdeg_B4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3F : ((B ^ 3 * F)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hFne, natDegree_pow]
    omega
  have hcf_B3F : ((B ^ 3 * F)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * F.leadingCoeff := by
    rw [← hdeg_B3F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CE : ((B ^ 2 * C * E)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CE : ((B ^ 2 * C * E)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2CE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D2 : ((B ^ 2 * D ^ 2)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hDne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2D2 : ((B ^ 2 * D ^ 2)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff ^ 2 := by
    rw [← hdeg_B2D2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_BC2D : ((B * C ^ 2 * D)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2D : ((B * C ^ 2 * D)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_BC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BEF : ((B * E * F)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hEne) hFne, natDegree_mul hBne hEne]
    omega
  have hcf_BEF : ((B * E * F)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C4 : (C ^ 4).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CDF : ((C * D * F)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hFne, natDegree_mul hCne hDne]
    omega
  have hcf_CDF : ((C * D * F)).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CE2 : ((C * E ^ 2)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_CE2 : ((C * E ^ 2)).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_CE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D2E : ((D ^ 2 * E)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hEne, natDegree_pow]
    omega
  have hcf_D2E : ((D ^ 2 * E)).coeff (4 * B.natDegree + C.natDegree) =
      D.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_D2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B4C, hcf_B3F, hcf_B2CE, hcf_B2D2, hcf_BC2D, hcf_BEF, hcf_C4, hcf_CDF, hcf_CE2, hcf_D2E]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_BCDEF_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G)
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
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoBCDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceBCDEF810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_BCDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoBCDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceBCDEF810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_BCDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoBCDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceBCDEF810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_BCDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoBCDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceBCDEF810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_BCDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1024 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoBCDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceBCDEF810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_BCDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoBCDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceBCDEF810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_BCDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 256 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_BCDEF_identity B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
  have hpow : F.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner] at hid
    simpa using hid.symm
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)


def kappaQuarticInnerBCDEG810 (b c d e g : k) : k :=
  (-15 : k) * b ^ 2 * d + (-15 : k) * b * c ^ 2 + 40 * b * g + 40 * d * e

def muQuarticInnerBCDEG810 (b c d e g : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * c * g + 320 * e ^ 2

def nuQuarticInnerBCDEG810 (b c d e g : k) : k :=
  35 * b ^ 3 * c + (-120 : k) * b * c * e + (-60 : k) * b * d ^ 2 + (-60 : k) * c ^ 2 * d + 160 * d * g

def xiQuarticInnerBCDEG810 (b c d e g : k) : k :=
  55 * b ^ 3 * d + 90 * b ^ 2 * c ^ 2 + (-80 : k) * b ^ 2 * g + (-200 : k) * b * d * e + (-120 : k) * c ^ 2 * e + (-120 : k) * c * d ^ 2 + 320 * e * g

def omicronQuarticInnerBCDEG810 (b c d e g : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-480 : k) * b * c * g + (-320 : k) * b * e ^ 2 + (-800 : k) * c * d * e + (-160 : k) * d ^ 3

def piQuarticInnerBCDEG810 (b c d e g : k) : k :=
  (-35 : k) * b ^ 4 * c + 180 * b ^ 2 * c * e + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + (-160 : k) * b * d * g + 15 * c ^ 4 + (-80 : k) * c ^ 2 * g + (-160 : k) * c * e ^ 2 + (-160 : k) * d ^ 2 * e + 320 * g ^ 2

def primitiveQuarticInnerBCDEG810 (b c d e g : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 120 * b ^ 3 * g + 680 * b ^ 2 * d * e + 720 * b * c ^ 2 * e + 720 * b * c * d ^ 2 + (-640 : k) * b * e * g + 240 * c ^ 3 * d + (-640 : k) * c * d * g + (-640 : k) * d * e ^ 2

set_option maxHeartbeats 64000000 in
theorem quarticInner_BCDEG_identity
    (b c d e g : k) :
    ((-25686694503478743 / 14916339186188222464 : k) * b ^ 4 * c * d + (-1958592148964633 / 3925352417417953280 : k) * b ^ 3 * c ^ 3 + (212962847516251 / 73600357826586624 : k) * b ^ 3 * c * g + (-19379141224833 / 196267620870897664 : k) * b ^ 3 * e ^ 2 + (11537019432645313 / 932271199136763904 : k) * b ^ 2 * c * d * e + (-616420093976163 / 3729084796547055616 : k) * b ^ 2 * d ^ 3 + (939317705213721 / 490669052177244160 : k) * b * c ^ 3 * e + (1681843467312838013 / 37290847965470556160 : k) * b * c ^ 2 * d ^ 2 + (-1720412315508397 / 122667263044311040 : k) * b * c * e * g + (-8751490750323411 / 2330677997841909760 : k) * b * d ^ 2 * g + (29483730440343 / 122667263044311040 : k) * b * e ^ 3 + (472532382559468199 / 74581695930941112320 : k) * c ^ 4 * d + (-642037454305765443 / 9322711991367639040 : k) * c ^ 2 * d * g + (-40249488613413473 / 4661355995683819520 : k) * c * d * e ^ 2 + (7772100477067313 / 9322711991367639040 : k) * d ^ 3 * e + (289364722125257 / 18400089456646656 : k) * d * g ^ 2) * kappaQuarticInnerBCDEG810 b c d e g +
      ((-34761552192303 / 245334526088622080 : k) * b ^ 2 * e * g + (-14513265344315031 / 15701409669671813120 : k) * b * c ^ 3 * d + (4262752319251469 / 1962676208708976640 : k) * b * c * d * g + (-29483730440343 / 981338104354488320 : k) * b * d * e ^ 2 + (-3 / 81920 : k) * c ^ 3 * g + (18647753130261 / 981338104354488320 : k) * c ^ 2 * e ^ 2 + (27513490006482343 / 18645423982735278080 : k) * c * d ^ 2 * e + (1 / 2048 : k) * c * g ^ 2 + (-1118892612660777 / 3925352417417953280 : k) * d ^ 4 + (54769227269329 / 122667263044311040 : k) * e ^ 2 * g) * muQuarticInnerBCDEG810 b c d e g +
      ((-839396635270557 / 3925352417417953280 : k) * b * c ^ 4 + (354282485933507 / 196267620870897664 : k) * b * c ^ 2 * g + (2828799918687 / 49066905217724416 : k) * b * c * e ^ 2 + (-173021323491619 / 291334749730238720 : k) * b * d ^ 2 * e + (-296818019585869 / 368001789132933120 : k) * b * g ^ 2 + (-2118226446433937 / 18645423982735278080 : k) * c ^ 2 * d * e + (-2497257460630121 / 1962676208708976640 : k) * c * d ^ 3 + (13187229835760279 / 6992033993525729280 : k) * d * e * g) * nuQuarticInnerBCDEG810 b c d e g +
      ((-5857212642225 / 98133810435448832 : k) * b ^ 2 * c * g + (19379141224833 / 196267620870897664 : k) * b ^ 2 * e ^ 2 + (78833174276629 / 981338104354488320 : k) * b * c * d * e + (10166137440483051 / 74581695930941112320 : k) * b * d ^ 3 + (8326755828597 / 245334526088622080 : k) * c ^ 3 * e + (28528663003045603 / 37290847965470556160 : k) * c ^ 2 * d ^ 2 + (-23505839299839 / 122667263044311040 : k) * c * e * g + (-657792838576287 / 932271199136763904 : k) * d ^ 2 * g + (-54769227269329 / 122667263044311040 : k) * e ^ 3) * xiQuarticInnerBCDEG810 b c d e g +
      ((18347638931056245 / 14916339186188222464 : k) * b * c * d ^ 2 + (-11587184064101 / 49066905217724416 : k) * b * e * g + (2737923303750561 / 59665356744752889856 : k) * c ^ 3 * d + (-14046405175158643 / 7458169593094111232 : k) * c * d * g + (54769227269329 / 196267620870897664 : k) * d * e ^ 2) * omicronQuarticInnerBCDEG810 b c d e g +
      ((-1 / 5120 : k) * c ^ 2 * g + (21 / 56320 : k) * c * e ^ 2 + (-597325308616499 / 932271199136763904 : k) * d ^ 2 * e + (1 / 320 : k) * g ^ 2) * piQuarticInnerBCDEG810 b c d e g =
      g ^ 4 := by
  simp only [kappaQuarticInnerBCDEG810, muQuarticInnerBCDEG810, nuQuarticInnerBCDEG810, xiQuarticInnerBCDEG810, omicronQuarticInnerBCDEG810, piQuarticInnerBCDEG810, primitiveQuarticInnerBCDEG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
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
theorem degreeZeroKappaQuartic810_eq_BCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBCDEG810 A B C D E F G +
        degreeZeroKappaQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBCDEG810, degreeZeroKappaQuarticNoBCDEG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroKappaQuarticNoBCDEG810]
  compute_degree
  omega

theorem kappaQuarticFaceBCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceBCDEG810 A B C D E F G).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 128 : k) * kappaQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  simp only [kappaQuarticFaceBCDEG810, kappaQuarticInnerBCDEG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_DE : ((D * E)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (2 * B.natDegree + D.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2D, hcf_BC2, hcf_BG, hcf_DE]
  ring

set_option maxHeartbeats 16000000 in
def muQuarticFaceBCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoBCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
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
theorem degreeZeroMuQuartic810_eq_BCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBCDEG810 A B C D E F G +
        degreeZeroMuQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBCDEG810, degreeZeroMuQuarticNoBCDEG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoBCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G) :
    (degreeZeroMuQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroMuQuarticNoBCDEG810]
  compute_degree
  omega

theorem muQuarticFaceBCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceBCDEG810 A B C D E F G).coeff (4 * B.natDegree) =
      (1 / 2048 : k) * muQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  simp only [muQuarticFaceBCDEG810, muQuarticInnerBCDEG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_E2 : (E ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (4 * B.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4, hcf_B2E, hcf_BCD, hcf_C3, hcf_CG, hcf_E2]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceBCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoBCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
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
theorem degreeZeroNuQuartic810_eq_BCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBCDEG810 A B C D E F G +
        degreeZeroNuQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBCDEG810, degreeZeroNuQuarticNoBCDEG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoBCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G) :
    (degreeZeroNuQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroNuQuarticNoBCDEG810]
  compute_degree
  omega

theorem nuQuarticFaceBCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceBCDEG810 A B C D E F G).coeff (3 * B.natDegree + C.natDegree) =
      (1 / 512 : k) * nuQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  simp only [nuQuarticFaceBCDEG810, nuQuarticInnerBCDEG810, coeff_add, coeff_sub, coeff_smul,
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
  rw [hcf_B3C, hcf_BCE, hcf_BD2, hcf_C2D, hcf_DG]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceBCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoBCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * C * F)
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
theorem degreeZeroXiQuartic810_eq_BCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceBCDEG810 A B C D E F G +
        degreeZeroXiQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceBCDEG810, degreeZeroXiQuarticNoBCDEG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoBCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G) :
    (degreeZeroXiQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroXiQuarticNoBCDEG810]
  compute_degree
  omega

theorem xiQuarticFaceBCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (xiQuarticFaceBCDEG810 A B C D E F G).coeff (3 * B.natDegree + D.natDegree) =
      (1 / 1024 : k) * xiQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  simp only [xiQuarticFaceBCDEG810, xiQuarticInnerBCDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
  have hcf_B3D : ((B ^ 3 * D)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B2G : ((B ^ 2 * G)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hGne, natDegree_pow]
    omega
  have hcf_B2G : ((B ^ 2 * G)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_B2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDE : ((B * D * E)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hEne, natDegree_mul hBne hDne]
    omega
  have hcf_BDE : ((B * D * E)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (3 * B.natDegree + D.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (3 * B.natDegree + D.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_EG : ((E * G)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hEne hGne]
    omega
  have hcf_EG : ((E * G)).coeff (3 * B.natDegree + D.natDegree) =
      E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_EG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B3D, hcf_B2C2, hcf_B2G, hcf_BDE, hcf_C2E, hcf_CD2, hcf_EG]
  ring

set_option maxHeartbeats 16000000 in
def omicronQuarticFaceBCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(21 / 4096 : k)) • B ^ 5
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 64 : k) • (B * E ^ 2)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoBCDEG810
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
  - (5 / 128 : k) • (A * D * G)
  - (5 / 128 : k) • (A * E * F)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (C ^ 2 * F)
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
theorem degreeZeroOmicronQuartic810_eq_BCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceBCDEG810 A B C D E F G +
        degreeZeroOmicronQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceBCDEG810, degreeZeroOmicronQuarticNoBCDEG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoBCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroOmicronQuarticNoBCDEG810]
  compute_degree
  omega

theorem omicronQuarticFaceBCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceBCDEG810 A B C D E F G).coeff (5 * B.natDegree) =
      (1 / 4096 : k) * omicronQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  simp only [omicronQuarticFaceBCDEG810, omicronQuarticInnerBCDEG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_B2CD : ((B ^ 2 * C * D)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hDne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CD : ((B ^ 2 * C * D)).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_B2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
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
  have hdeg_CDE : ((C * D * E)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hEne, natDegree_mul hCne hDne]
    omega
  have hcf_CDE : ((C * D * E)).coeff (5 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_CDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D3 : (D ^ 3).natDegree = 5 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (5 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B5, hcf_B3E, hcf_B2CD, hcf_BC3, hcf_BCG, hcf_BE2, hcf_CDE, hcf_D3]
  ring

set_option maxHeartbeats 16000000 in
def piQuarticFaceBCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 256 : k)) • (B ^ 4 * C)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoBCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  + (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_BCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceBCDEG810 A B C D E F G +
        degreeZeroPiQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceBCDEG810, degreeZeroPiQuarticNoBCDEG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoBCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G) :
    (degreeZeroPiQuarticNoBCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroPiQuarticNoBCDEG810]
  compute_degree
  omega

theorem piQuarticFaceBCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceBCDEG810 A B C D E F G).coeff (4 * B.natDegree + C.natDegree) =
      (1 / 256 : k) * piQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
  simp only [piQuarticFaceBCDEG810, piQuarticInnerBCDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4C : ((B ^ 4 * C)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hCne, natDegree_pow]
  have hcf_B4C : ((B ^ 4 * C)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 * C.leadingCoeff := by
    rw [← hdeg_B4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CE : ((B ^ 2 * C * E)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CE : ((B ^ 2 * C * E)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2CE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D2 : ((B ^ 2 * D ^ 2)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hDne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2D2 : ((B ^ 2 * D ^ 2)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff ^ 2 := by
    rw [← hdeg_B2D2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_BC2D : ((B * C ^ 2 * D)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2D : ((B * C ^ 2 * D)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_BC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDG : ((B * D * G)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hGne, natDegree_mul hBne hDne]
    omega
  have hcf_BDG : ((B * D * G)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C4 : (C ^ 4).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C2G : ((C ^ 2 * G)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow]
    omega
  have hcf_C2G : ((C ^ 2 * G)).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_C2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CE2 : ((C * E ^ 2)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_CE2 : ((C * E ^ 2)).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_CE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D2E : ((D ^ 2 * E)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hEne, natDegree_pow]
    omega
  have hcf_D2E : ((D ^ 2 * E)).coeff (4 * B.natDegree + C.natDegree) =
      D.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_D2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_G2 : (G ^ 2).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_G2 : (G ^ 2).coeff (4 * B.natDegree + C.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4C, hcf_B2CE, hcf_B2D2, hcf_BC2D, hcf_BDG, hcf_C4, hcf_C2G, hcf_CE2, hcf_D2E, hcf_G2]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_BCDEG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEG810 A B C D E F G)
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
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoBCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceBCDEG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_BCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoBCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceBCDEG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_BCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoBCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceBCDEG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_BCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoBCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceBCDEG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_BCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1024 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoBCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceBCDEG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_BCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerBCDEG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoBCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceBCDEG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hGpos, hBC, hBD, hBE, hBG, hAlt, hFlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_BCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 256 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_BCDEG_identity B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff
  have hpow : G.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner] at hid
    simpa using hid.symm
  have hlc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)


def kappaQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-15 : k) * b ^ 2 * d + (-15 : k) * b * c ^ 2 + 40 * b * g + 40 * c * f

def muQuarticInnerBCDFG810 (b c d f g : k) : k :=
  35 * b ^ 4 + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * c * g + 640 * d * f

def nuQuarticInnerBCDFG810 (b c d f g : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b ^ 2 * f + (-60 : k) * b * d ^ 2 + (-60 : k) * c ^ 2 * d + 160 * d * g

def xiQuarticInnerBCDFG810 (b c d f g : k) : k :=
  55 * b ^ 3 * d + 90 * b ^ 2 * c ^ 2 + (-80 : k) * b ^ 2 * g + (-200 : k) * b * c * f + (-120 : k) * c * d ^ 2 + 160 * f ^ 2

def omicronQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-21 : k) * b ^ 5 + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-480 : k) * b * c * g + (-640 : k) * b * d * f + (-320 : k) * c ^ 2 * f + (-160 : k) * d ^ 3 + 1280 * f * g

def piQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-35 : k) * b ^ 4 * c + 50 * b ^ 3 * f + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + (-160 : k) * b * d * g + 15 * c ^ 4 + (-80 : k) * c ^ 2 * g + (-240 : k) * c * d * f + 320 * g ^ 2

def primitiveQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 120 * b ^ 3 * g + 680 * b ^ 2 * c * f + 720 * b * c * d ^ 2 + (-640 : k) * b * f ^ 2 + 240 * c ^ 3 * d + (-640 : k) * c * d * g + (-640 : k) * d ^ 2 * f

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCDFG_identity
    (b c d f g : k) :
    ((49721439699 / 92489280634880 : k) * b ^ 4 * d + (-1412223896701 / 55493568380928 : k) * b ^ 3 * c ^ 2 + (-433327923123 / 11561160079360 : k) * b ^ 3 * g + (718669049307 / 16185624111104 : k) * b ^ 2 * c * f + (338005186913 / 5780580039680 : k) * b * c * d ^ 2 + (181171989941 / 5780580039680 : k) * b * f ^ 2 + (600807275947 / 10116015069440 : k) * c ^ 3 * d + (-13099546853549 / 60696090416640 : k) * c * d * g + (-1897249609669 / 40464060277760 : k) * d ^ 2 * f) * kappaQuarticInnerBCDFG810 b c d f g +
      ((69797673027 / 129484992888832 : k) * b ^ 3 * f + (1038672910209 / 258969985777664 : k) * b * c ^ 2 * d + (765235362377 / 161856241111040 : k) * b * d * g + (191100579987 / 323712482222080 : k) * c ^ 4 + (-63700193329 / 20232030138880 : k) * c ^ 2 * g + (-128691860909 / 23122320158720 : k) * c * d * f + (63700193329 / 5058007534720 : k) * g ^ 2) * muQuarticInnerBCDFG810 b c d f g +
      ((-1213263453279 / 161856241111040 : k) * b * c ^ 3 + (1471610468093 / 60696090416640 : k) * b * c * g + (-934271627935 / 32371248222208 : k) * b * d * f + (221467542707 / 8670870059520 : k) * c ^ 2 * f + (16573813233 / 16185624111104 : k) * d ^ 3 + (-7193167623 / 2023203013888 : k) * f * g) * nuQuarticInnerBCDFG810 b c d f g +
      ((-12263569863 / 36995712253952 : k) * b ^ 2 * c ^ 2 + (-61185507293 / 4624464031744 : k) * b ^ 2 * g + (-528863701 / 23122320158720 : k) * b * c * f + (-11963841453 / 4624464031744 : k) * c * d ^ 2 + (1 / 160 : k) * f ^ 2) * xiQuarticInnerBCDFG810 b c d f g +
      ((116329455045 / 129484992888832 : k) * b ^ 2 * f + (-49721439699 / 129484992888832 : k) * b * d ^ 2 + (5303137653 / 3407499812864 : k) * c ^ 2 * d + (16573813233 / 16185624111104 : k) * d * g) * omicronQuarticInnerBCDFG810 b c d f g +
      ((133856743379 / 10116015069440 : k) * b * c * d + (63700193329 / 20232030138880 : k) * c ^ 3 + (-63700193329 / 2529003767360 : k) * c * g + (-278252387341 / 10116015069440 : k) * d * f) * piQuarticInnerBCDFG810 b c d f g =
      f ^ 4 := by
  simp only [kappaQuarticInnerBCDFG810, muQuarticInnerBCDFG810, nuQuarticInnerBCDFG810, xiQuarticInnerBCDFG810, omicronQuarticInnerBCDFG810, piQuarticInnerBCDFG810, primitiveQuarticInnerBCDFG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
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
theorem degreeZeroKappaQuartic810_eq_BCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBCDFG810 A B C D E F G +
        degreeZeroKappaQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBCDFG810, degreeZeroKappaQuarticNoBCDFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaQuarticNoBCDFG810]
  compute_degree
  omega

theorem kappaQuarticFaceBCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceBCDFG810 A B C D E F G).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 128 : k) * kappaQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  simp only [kappaQuarticFaceBCDFG810, kappaQuarticInnerBCDFG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_CF : ((C * F)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hCne hFne]
    omega
  have hcf_CF : ((C * F)).coeff (2 * B.natDegree + D.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2D, hcf_BC2, hcf_BG, hcf_CF]
  ring

set_option maxHeartbeats 16000000 in
def muQuarticFaceBCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoBCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
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
theorem degreeZeroMuQuartic810_eq_BCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBCDFG810 A B C D E F G +
        degreeZeroMuQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBCDFG810, degreeZeroMuQuarticNoBCDFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoBCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroMuQuarticNoBCDFG810]
  compute_degree
  omega

theorem muQuarticFaceBCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceBCDFG810 A B C D E F G).coeff (4 * B.natDegree) =
      (1 / 2048 : k) * muQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  simp only [muQuarticFaceBCDFG810, muQuarticInnerBCDFG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_DF : ((D * F)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (4 * B.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B4, hcf_BCD, hcf_C3, hcf_CG, hcf_DF]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceBCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoBCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
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
theorem degreeZeroNuQuartic810_eq_BCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBCDFG810 A B C D E F G +
        degreeZeroNuQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBCDFG810, degreeZeroNuQuarticNoBCDFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoBCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroNuQuarticNoBCDFG810]
  compute_degree
  omega

theorem nuQuarticFaceBCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceBCDFG810 A B C D E F G).coeff (3 * B.natDegree + C.natDegree) =
      (1 / 512 : k) * nuQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  simp only [nuQuarticFaceBCDFG810, nuQuarticInnerBCDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
  have hcf_B3C : ((B ^ 3 * C)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2F : ((B ^ 2 * F)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hFne, natDegree_pow]
    omega
  have hcf_B2F : ((B ^ 2 * F)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
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
  rw [hcf_B3C, hcf_B2F, hcf_BD2, hcf_C2D, hcf_DG]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceBCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoBCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)
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
theorem degreeZeroXiQuartic810_eq_BCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceBCDFG810 A B C D E F G +
        degreeZeroXiQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceBCDFG810, degreeZeroXiQuarticNoBCDFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoBCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G) :
    (degreeZeroXiQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroXiQuarticNoBCDFG810]
  compute_degree
  omega

theorem xiQuarticFaceBCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (xiQuarticFaceBCDFG810 A B C D E F G).coeff (3 * B.natDegree + D.natDegree) =
      (1 / 1024 : k) * xiQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  simp only [xiQuarticFaceBCDFG810, xiQuarticInnerBCDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
  have hcf_B3D : ((B ^ 3 * D)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B2G : ((B ^ 2 * G)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hGne, natDegree_pow]
    omega
  have hcf_B2G : ((B ^ 2 * G)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_B2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCF : ((B * C * F)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hFne, natDegree_mul hBne hCne]
    omega
  have hcf_BCF : ((B * C * F)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BCF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (3 * B.natDegree + D.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_F2 : (F ^ 2).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (3 * B.natDegree + D.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B3D, hcf_B2C2, hcf_B2G, hcf_BCF, hcf_CD2, hcf_F2]
  ring

set_option maxHeartbeats 16000000 in
def omicronQuarticFaceBCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(21 / 4096 : k)) • B ^ 5
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoBCDFG810
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
  + (5 / 128 : k) • (B ^ 3 * E)
  - (5 / 128 : k) • (A * D * G)
  - (5 / 128 : k) • (A * E * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (25 / 128 : k) • (C * D * E)
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
theorem degreeZeroOmicronQuartic810_eq_BCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceBCDFG810 A B C D E F G +
        degreeZeroOmicronQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceBCDFG810, degreeZeroOmicronQuarticNoBCDFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoBCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroOmicronQuarticNoBCDFG810]
  compute_degree
  omega

theorem omicronQuarticFaceBCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceBCDFG810 A B C D E F G).coeff (5 * B.natDegree) =
      (1 / 4096 : k) * omicronQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  simp only [omicronQuarticFaceBCDFG810, omicronQuarticInnerBCDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 5 * B.natDegree := by
    rw [natDegree_pow]
  have hcf_B5 : (B ^ 5).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2CD : ((B ^ 2 * C * D)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hDne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CD : ((B ^ 2 * C * D)).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_B2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
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
  have hdeg_BDF : ((B * D * F)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hFne, natDegree_mul hBne hDne]
    omega
  have hcf_BDF : ((B * D * F)).coeff (5 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2F : ((C ^ 2 * F)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hFne, natDegree_pow]
    omega
  have hcf_C2F : ((C ^ 2 * F)).coeff (5 * B.natDegree) =
      C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_C2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D3 : (D ^ 3).natDegree = 5 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (5 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_FG : ((F * G)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hFne hGne]
    omega
  have hcf_FG : ((F * G)).coeff (5 * B.natDegree) =
      F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_FG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B5, hcf_B2CD, hcf_BC3, hcf_BCG, hcf_BDF, hcf_C2F, hcf_D3, hcf_FG]
  ring

set_option maxHeartbeats 16000000 in
def piQuarticFaceBCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 256 : k)) • (B ^ 4 * C)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoBCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_BCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceBCDFG810 A B C D E F G +
        degreeZeroPiQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceBCDFG810, degreeZeroPiQuarticNoBCDFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoBCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G) :
    (degreeZeroPiQuarticNoBCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroPiQuarticNoBCDFG810]
  compute_degree
  omega

theorem piQuarticFaceBCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceBCDFG810 A B C D E F G).coeff (4 * B.natDegree + C.natDegree) =
      (1 / 256 : k) * piQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
  simp only [piQuarticFaceBCDFG810, piQuarticInnerBCDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4C : ((B ^ 4 * C)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hCne, natDegree_pow]
  have hcf_B4C : ((B ^ 4 * C)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 * C.leadingCoeff := by
    rw [← hdeg_B4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3F : ((B ^ 3 * F)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hFne, natDegree_pow]
    omega
  have hcf_B3F : ((B ^ 3 * F)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * F.leadingCoeff := by
    rw [← hdeg_B3F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D2 : ((B ^ 2 * D ^ 2)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hDne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2D2 : ((B ^ 2 * D ^ 2)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff ^ 2 := by
    rw [← hdeg_B2D2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_BC2D : ((B * C ^ 2 * D)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2D : ((B * C ^ 2 * D)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_BC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDG : ((B * D * G)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hGne, natDegree_mul hBne hDne]
    omega
  have hcf_BDG : ((B * D * G)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C4 : (C ^ 4).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C2G : ((C ^ 2 * G)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow]
    omega
  have hcf_C2G : ((C ^ 2 * G)).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_C2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDF : ((C * D * F)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hFne, natDegree_mul hCne hDne]
    omega
  have hcf_CDF : ((C * D * F)).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_G2 : (G ^ 2).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_G2 : (G ^ 2).coeff (4 * B.natDegree + C.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4C, hcf_B3F, hcf_B2D2, hcf_BC2D, hcf_BDG, hcf_C4, hcf_C2G, hcf_CDF, hcf_G2]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_BCDFG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDFG810 A B C D E F G)
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
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoBCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceBCDFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_BCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoBCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceBCDFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_BCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoBCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceBCDFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_BCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoBCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceBCDFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_BCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1024 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoBCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceBCDFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_BCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerBCDFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoBCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceBCDFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hFpos, hGpos, hBC, hBD, hBF, hBG, hAlt, hElt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_BCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 256 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_BCDFG_identity B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff
  have hpow : F.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner] at hid
    simpa using hid.symm
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)


def kappaQuarticInnerBCEFG810 (b c e f g : k) : k :=
  (-15 : k) * b * c ^ 2 + 40 * b * g + 40 * c * f

def muQuarticInnerBCEFG810 (b c e f g : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-80 : k) * c ^ 3 + 640 * c * g + 320 * e ^ 2

def nuQuarticInnerBCEFG810 (b c e f g : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b ^ 2 * f + (-120 : k) * b * c * e + 160 * e * f

def xiQuarticInnerBCEFG810 (b c e f g : k) : k :=
  45 * b ^ 2 * c ^ 2 + (-40 : k) * b ^ 2 * g + (-100 : k) * b * c * f + (-60 : k) * c ^ 2 * e + 160 * e * g + 80 * f ^ 2

def omicronQuarticInnerBCEFG810 (b c e f g : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + 180 * b * c ^ 3 + (-480 : k) * b * c * g + (-320 : k) * b * e ^ 2 + (-320 : k) * c ^ 2 * f + 1280 * f * g

def piQuarticInnerBCEFG810 (b c e f g : k) : k :=
  (-35 : k) * b ^ 4 * c + 50 * b ^ 3 * f + 180 * b ^ 2 * c * e + (-240 : k) * b * e * f + 15 * c ^ 4 + (-80 : k) * c ^ 2 * g + (-160 : k) * c * e ^ 2 + 320 * g ^ 2

def primitiveQuarticInnerBCEFG810 (b c e f g : k) : k :=
  (-265 : k) * b ^ 3 * c ^ 2 + 120 * b ^ 3 * g + 680 * b ^ 2 * c * f + 720 * b * c ^ 2 * e + (-640 : k) * b * e * g + (-640 : k) * b * f ^ 2 + (-1280 : k) * c * e * f

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCEFG_identity
    (b c e f g : k) :
    ((-1752793 / 122880 : k) * b ^ 3 * c * g + (20099 / 3604480 : k) * b ^ 3 * e ^ 2 + (-7602413 / 21626880 : k) * b ^ 2 * c ^ 2 * f + (663151 / 811008 : k) * b ^ 2 * f * g + (-2298357 / 901120 : k) * b * c ^ 3 * e + (8263249 / 122880 : k) * b * c * e * g + (113241803 / 16220160 : k) * b * c * f ^ 2 + (205249 / 40960 : k) * b * e ^ 3 + (-7412243 / 5406720 : k) * c ^ 2 * e * f + (-20111485 / 202752 : k) * e * f * g + (1370671 / 2027520 : k) * f ^ 3) * kappaQuarticInnerBCEFG810 b c e f g +
      ((3976167 / 1802240 : k) * b ^ 2 * e * g + (409455 / 720896 : k) * b ^ 2 * f ^ 2 + (-1512557 / 1441792 : k) * b * c * e * f + (-3 / 81920 : k) * c ^ 3 * g + (2298609 / 3604480 : k) * c ^ 2 * e ^ 2 + (1 / 2048 : k) * c * g ^ 2 + (-765979 / 450560 : k) * e ^ 2 * g + (687057 / 901120 : k) * e * f ^ 2) * muQuarticInnerBCEFG810 b c e f g +
      ((2513033 / 3604480 : k) * b ^ 2 * e * f + (-279621 / 450560 : k) * b * c * e ^ 2 + (55657 / 5120 : k) * b * g ^ 2 + (-1086059 / 7208960 : k) * c ^ 3 * f + (21065777 / 901120 : k) * c * f * g + (-363259 / 112640 : k) * e ^ 2 * f) * nuQuarticInnerBCEFG810 b c e f g +
      ((-1168559 / 245760 : k) * b ^ 2 * c * g + (-20099 / 1802240 : k) * b ^ 2 * e ^ 2 + (-62788921 / 4055040 : k) * b * f * g + (-766119 / 901120 : k) * c ^ 3 * e + (766137 / 112640 : k) * c * e * g + (-1370671 / 4055040 : k) * c * f ^ 2 + (765979 / 225280 : k) * e ^ 3) * xiQuarticInnerBCEFG810 b c e f g +
      ((1325389 / 360448 : k) * b * e * g + (682425 / 720896 : k) * b * f ^ 2 + (-845573 / 1441792 : k) * c * e * f) * omicronQuarticInnerBCEFG810 b c e f g +
      ((-1 / 5120 : k) * c ^ 2 * g + (21 / 56320 : k) * c * e ^ 2 + (1 / 320 : k) * g ^ 2) * piQuarticInnerBCEFG810 b c e f g =
      g ^ 4 := by
  simp only [kappaQuarticInnerBCEFG810, muQuarticInnerBCEFG810, nuQuarticInnerBCEFG810, xiQuarticInnerBCEFG810, omicronQuarticInnerBCEFG810, piQuarticInnerBCEFG810, primitiveQuarticInnerBCEFG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
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
theorem degreeZeroKappaQuartic810_eq_BCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBCEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBCEFG810, degreeZeroKappaQuarticNoBCEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      B.natDegree + 2 * C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroKappaQuarticNoBCEFG810]
  compute_degree
  omega

theorem kappaQuarticFaceBCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceBCEFG810 A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) =
      (1 / 128 : k) * kappaQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  simp only [kappaQuarticFaceBCEFG810, kappaQuarticInnerBCEFG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_CF : ((C * F)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hCne hFne]
    omega
  have hcf_CF : ((C * F)).coeff (B.natDegree + 2 * C.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_BC2, hcf_BG, hcf_CF]
  ring

set_option maxHeartbeats 16000000 in
def muQuarticFaceBCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoBCEFG810
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
theorem degreeZeroMuQuartic810_eq_BCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBCEFG810 A B C D E F G +
        degreeZeroMuQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBCEFG810, degreeZeroMuQuarticNoBCEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoBCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroMuQuarticNoBCEFG810]
  compute_degree
  omega

theorem muQuarticFaceBCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceBCEFG810 A B C D E F G).coeff (4 * B.natDegree) =
      (1 / 2048 : k) * muQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  simp only [muQuarticFaceBCEFG810, muQuarticInnerBCEFG810, coeff_add, coeff_sub, coeff_smul,
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
def nuQuarticFaceBCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoBCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
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
theorem degreeZeroNuQuartic810_eq_BCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBCEFG810 A B C D E F G +
        degreeZeroNuQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBCEFG810, degreeZeroNuQuarticNoBCEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoBCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroNuQuarticNoBCEFG810]
  compute_degree
  omega

theorem nuQuarticFaceBCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceBCEFG810 A B C D E F G).coeff (3 * B.natDegree + C.natDegree) =
      (1 / 512 : k) * nuQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  simp only [nuQuarticFaceBCEFG810, nuQuarticInnerBCEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
  have hcf_B3C : ((B ^ 3 * C)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2F : ((B ^ 2 * F)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hFne, natDegree_pow]
    omega
  have hcf_B2F : ((B ^ 2 * F)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_EF : ((E * F)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (3 * B.natDegree + C.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B3C, hcf_B2F, hcf_BCE, hcf_EF]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceBCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoBCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
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
theorem degreeZeroXiQuartic810_eq_BCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceBCEFG810 A B C D E F G +
        degreeZeroXiQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceBCEFG810, degreeZeroXiQuarticNoBCEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoBCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G) :
    (degreeZeroXiQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + 2 * C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroXiQuarticNoBCEFG810]
  compute_degree
  omega

theorem xiQuarticFaceBCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (xiQuarticFaceBCEFG810 A B C D E F G).coeff (2 * B.natDegree + 2 * C.natDegree) =
      (1 / 512 : k) * xiQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  simp only [xiQuarticFaceBCEFG810, xiQuarticInnerBCEFG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_BCF : ((B * C * F)).natDegree = 2 * B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hFne, natDegree_mul hBne hCne]
    omega
  have hcf_BCF : ((B * C * F)).coeff (2 * B.natDegree + 2 * C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BCF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
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
  have hdeg_F2 : (F ^ 2).natDegree = 2 * B.natDegree + 2 * C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (2 * B.natDegree + 2 * C.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B2C2, hcf_B2G, hcf_BCF, hcf_C2E, hcf_EG, hcf_F2]
  ring

set_option maxHeartbeats 16000000 in
def omicronQuarticFaceBCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(21 / 4096 : k)) • B ^ 5
  + (5 / 128 : k) • (B ^ 3 * E)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoBCEFG810
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
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
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
theorem degreeZeroOmicronQuartic810_eq_BCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceBCEFG810 A B C D E F G +
        degreeZeroOmicronQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceBCEFG810, degreeZeroOmicronQuarticNoBCEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoBCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroOmicronQuarticNoBCEFG810]
  compute_degree
  omega

theorem omicronQuarticFaceBCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceBCEFG810 A B C D E F G).coeff (5 * B.natDegree) =
      (1 / 4096 : k) * omicronQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  simp only [omicronQuarticFaceBCEFG810, omicronQuarticInnerBCEFG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_C2F : ((C ^ 2 * F)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hFne, natDegree_pow]
    omega
  have hcf_C2F : ((C ^ 2 * F)).coeff (5 * B.natDegree) =
      C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_C2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_FG : ((F * G)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hFne hGne]
    omega
  have hcf_FG : ((F * G)).coeff (5 * B.natDegree) =
      F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_FG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B5, hcf_B3E, hcf_BC3, hcf_BCG, hcf_BE2, hcf_C2F, hcf_FG]
  ring

set_option maxHeartbeats 16000000 in
def piQuarticFaceBCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 256 : k)) • (B ^ 4 * C)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (15 / 256 : k) • C ^ 4
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (C * E ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoBCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_BCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceBCEFG810 A B C D E F G +
        degreeZeroPiQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceBCEFG810, degreeZeroPiQuarticNoBCEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoBCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G) :
    (degreeZeroPiQuarticNoBCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroPiQuarticNoBCEFG810]
  compute_degree
  omega

theorem piQuarticFaceBCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceBCEFG810 A B C D E F G).coeff (4 * B.natDegree + C.natDegree) =
      (1 / 256 : k) * piQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
  simp only [piQuarticFaceBCEFG810, piQuarticInnerBCEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4C : ((B ^ 4 * C)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hCne, natDegree_pow]
  have hcf_B4C : ((B ^ 4 * C)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 * C.leadingCoeff := by
    rw [← hdeg_B4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3F : ((B ^ 3 * F)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hFne, natDegree_pow]
    omega
  have hcf_B3F : ((B ^ 3 * F)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * F.leadingCoeff := by
    rw [← hdeg_B3F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CE : ((B ^ 2 * C * E)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CE : ((B ^ 2 * C * E)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2CE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BEF : ((B * E * F)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hEne) hFne, natDegree_mul hBne hEne]
    omega
  have hcf_BEF : ((B * E * F)).coeff (4 * B.natDegree + C.natDegree) =
      B.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C4 : (C ^ 4).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C2G : ((C ^ 2 * G)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow]
    omega
  have hcf_C2G : ((C ^ 2 * G)).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_C2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CE2 : ((C * E ^ 2)).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_CE2 : ((C * E ^ 2)).coeff (4 * B.natDegree + C.natDegree) =
      C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_CE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_G2 : (G ^ 2).natDegree = 4 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_G2 : (G ^ 2).coeff (4 * B.natDegree + C.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4C, hcf_B3F, hcf_B2CE, hcf_BEF, hcf_C4, hcf_C2G, hcf_CE2, hcf_G2]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_BCEFG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCEFG810 A B C D E F G)
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
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoBCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceBCEFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_BCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoBCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceBCEFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_BCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoBCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceBCEFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_BCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoBCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceBCEFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * B.natDegree + 2 * C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_BCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoBCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceBCEFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_BCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerBCEFG810 B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoBCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceBCEFG810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hBpos, hCpos, hEpos, hFpos, hGpos, hBC, hBE, hBF, hBG, hAlt, hDlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_BCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 256 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_BCEFG_identity B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff
  have hpow : G.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner] at hid
    simpa using hid.symm
  have hlc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)


def kappaQuarticInnerBDEFG810 (b d e f g : k) : k :=
  (-15 : k) * b ^ 2 * d + 40 * b * g + 40 * d * e

def muQuarticInnerBDEFG810 (b d e f g : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + 640 * d * f + 320 * e ^ 2

def nuQuarticInnerBDEFG810 (b d e f g : k) : k :=
  (-15 : k) * b ^ 2 * f + (-15 : k) * b * d ^ 2 + 40 * d * g + 40 * e * f

def xiQuarticInnerBDEFG810 (b d e f g : k) : k :=
  55 * b ^ 3 * d + (-80 : k) * b ^ 2 * g + (-200 : k) * b * d * e + 320 * e * g + 160 * f ^ 2

def omicronQuarticInnerBDEFG810 (b d e f g : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + (-640 : k) * b * d * f + (-320 : k) * b * e ^ 2 + (-160 : k) * d ^ 3 + 1280 * f * g

def piQuarticInnerBDEFG810 (b d e f g : k) : k :=
  25 * b ^ 3 * f + 45 * b ^ 2 * d ^ 2 + (-80 : k) * b * d * g + (-120 : k) * b * e * f + (-80 : k) * d ^ 2 * e + 160 * g ^ 2

def primitiveQuarticInnerBDEFG810 (b d e f g : k) : k :=
  (-125 : k) * b ^ 4 * d + 120 * b ^ 3 * g + 680 * b ^ 2 * d * e + (-640 : k) * b * e * g + (-640 : k) * b * f ^ 2 + (-640 : k) * d ^ 2 * f + (-640 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_BDEFG_identity
    (b d e f g : k) :
    ((128 / 105 : k) * b ^ 6 * f + (5120 / 441 : k) * b ^ 4 * e * f + (-177823936 / 3573255 : k) * b ^ 3 * d ^ 2 * e + (-38150144 / 102093 : k) * b ^ 3 * g ^ 2 + (152600576 / 238217 : k) * b ^ 2 * d * e * g + (104102112512 / 58363165 : k) * b ^ 2 * d * f ^ 2 + (59592407552 / 35017899 : k) * b ^ 2 * e ^ 2 * f + (85705858944 / 58363165 : k) * b * d ^ 3 * f + (25209086464 / 35017899 : k) * b * d ^ 2 * e ^ 2 + (1220804608 / 714651 : k) * b * e * g ^ 2 + (-361404408832 / 35017899 : k) * b * f ^ 2 * g + (-14284309824 / 11672633 : k) * d ^ 5 + (108521978368 / 58363165 : k) * d ^ 2 * f * g + (-950559340544 / 175089495 : k) * d * e ^ 2 * g + (-1790846772224 / 525268485 : k) * d * e * f ^ 2 + (-33271402496 / 15007671 : k) * e ^ 3 * f) * kappaQuarticInnerBDEFG810 b d e f g +
      ((1 / 35 : k) * b ^ 8 + (48 / 245 : k) * b ^ 6 * e + (-4016 / 343 : k) * b ^ 4 * e ^ 2 + (-1024 / 735 : k) * b ^ 3 * f * g + (13184 / 343 : k) * b ^ 2 * e ^ 3 + (-2391599984 / 11672633 : k) * b * d ^ 3 * e + (-38150144 / 238217 : k) * b * d * g ^ 2 + (377768122496 / 525268485 : k) * b * e * f * g + (20122773056 / 58363165 : k) * b * f ^ 3 + (8289617408 / 25012785 : k) * d ^ 2 * e * g + (-1559295232 / 25012785 : k) * d ^ 2 * f ^ 2 + (10122437632 / 105053697 : k) * d * e ^ 2 * f + (305201152 / 714651 : k) * g ^ 3) * muQuarticInnerBDEFG810 b d e f g +
      ((3143068672 / 25012785 : k) * b ^ 3 * f ^ 2 + (14284309824 / 11672633 : k) * b * d ^ 4 + (-108521978368 / 58363165 : k) * b * d * f * g + (501913647104 / 175089495 : k) * b * e ^ 2 * g + (-546085888 / 58363165 : k) * b * e * f ^ 2 + (297767667712 / 175089495 : k) * d ^ 2 * e * f + (50640105472 / 35017899 : k) * d * e ^ 3 + (-4883218432 / 714651 : k) * f * g ^ 2) * nuQuarticInnerBDEFG810 b d e f g +
      ((98120811008 / 175089495 : k) * b * d * f ^ 2 + (1413427712 / 5002557 : k) * b * e ^ 2 * f + (42852929472 / 58363165 : k) * d ^ 3 * f + (29142529792 / 175089495 : k) * d ^ 2 * e ^ 2 + (-305201152 / 714651 : k) * e * g ^ 2 + (-135837635072 / 35017899 : k) * f ^ 2 * g) * xiQuarticInnerBDEFG810 b d e f g +
      ((-7312 / 343 : k) * b ^ 3 * e ^ 2 + (13184 / 343 : k) * b * e ^ 3 + (-3571077456 / 11672633 : k) * d ^ 3 * e + (14435398016 / 11672633 : k) * e * f * g + (16979704384 / 35017899 : k) * f ^ 3) * omicronQuarticInnerBDEFG810 b d e f g =
      b ^ 12 := by
  simp only [kappaQuarticInnerBDEFG810, muQuarticInnerBDEFG810, nuQuarticInnerBDEFG810, xiQuarticInnerBDEFG810, omicronQuarticInnerBDEFG810, piQuarticInnerBDEFG810, primitiveQuarticInnerBDEFG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBDEFG810
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
theorem degreeZeroKappaQuartic810_eq_BDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBDEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoBDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBDEFG810, degreeZeroKappaQuarticNoBDEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroKappaQuarticNoBDEFG810]
  compute_degree
  omega

theorem kappaQuarticFaceBDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBDEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceBDEFG810 A B C D E F G).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 128 : k) * kappaQuarticInnerBDEFG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
  simp only [kappaQuarticFaceBDEFG810, kappaQuarticInnerBDEFG810, coeff_add, coeff_sub, coeff_smul,
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

set_option maxHeartbeats 16000000 in
def muQuarticFaceBDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoBDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_BDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBDEFG810 A B C D E F G +
        degreeZeroMuQuarticNoBDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBDEFG810, degreeZeroMuQuarticNoBDEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoBDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDEFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoBDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroMuQuarticNoBDEFG810]
  compute_degree
  omega

theorem muQuarticFaceBDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBDEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceBDEFG810 A B C D E F G).coeff (4 * B.natDegree) =
      (1 / 2048 : k) * muQuarticInnerBDEFG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
  simp only [muQuarticFaceBDEFG810, muQuarticInnerBDEFG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_DF : ((D * F)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (4 * B.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (4 * B.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4, hcf_B2E, hcf_DF, hcf_E2]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceBDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * F)
  - (15 / 128 : k) • (B * D ^ 2)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoBDEFG810
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
theorem degreeZeroNuQuartic810_eq_BDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBDEFG810 A B C D E F G +
        degreeZeroNuQuarticNoBDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBDEFG810, degreeZeroNuQuarticNoBDEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoBDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDEFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoBDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + F.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroNuQuarticNoBDEFG810]
  compute_degree
  omega

theorem nuQuarticFaceBDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBDEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceBDEFG810 A B C D E F G).coeff (2 * B.natDegree + F.natDegree) =
      (1 / 128 : k) * nuQuarticInnerBDEFG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
  simp only [nuQuarticFaceBDEFG810, nuQuarticInnerBDEFG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_EF : ((E * F)).natDegree = 2 * B.natDegree + F.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (2 * B.natDegree + F.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2F, hcf_BD2, hcf_DG, hcf_EF]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceBDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * D * E)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoBDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * C * F)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
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
theorem degreeZeroXiQuartic810_eq_BDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceBDEFG810 A B C D E F G +
        degreeZeroXiQuarticNoBDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceBDEFG810, degreeZeroXiQuarticNoBDEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoBDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDEFG810 A B C D E F G) :
    (degreeZeroXiQuarticNoBDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroXiQuarticNoBDEFG810]
  compute_degree
  omega

theorem xiQuarticFaceBDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBDEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (xiQuarticFaceBDEFG810 A B C D E F G).coeff (3 * B.natDegree + D.natDegree) =
      (1 / 1024 : k) * xiQuarticInnerBDEFG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
  simp only [xiQuarticFaceBDEFG810, xiQuarticInnerBDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
  have hcf_B3D : ((B ^ 3 * D)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2G : ((B ^ 2 * G)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hGne, natDegree_pow]
    omega
  have hcf_B2G : ((B ^ 2 * G)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_B2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDE : ((B * D * E)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hEne, natDegree_mul hBne hDne]
    omega
  have hcf_BDE : ((B * D * E)).coeff (3 * B.natDegree + D.natDegree) =
      B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_EG : ((E * G)).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hEne hGne]
    omega
  have hcf_EG : ((E * G)).coeff (3 * B.natDegree + D.natDegree) =
      E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_EG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_F2 : (F ^ 2).natDegree = 3 * B.natDegree + D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (3 * B.natDegree + D.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B3D, hcf_B2G, hcf_BDE, hcf_EG, hcf_F2]
  ring

set_option maxHeartbeats 16000000 in
def omicronQuarticFaceBDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(21 / 4096 : k)) • B ^ 5
  + (5 / 128 : k) • (B ^ 3 * E)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoBDEFG810
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
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * D * G)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
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
theorem degreeZeroOmicronQuartic810_eq_BDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceBDEFG810 A B C D E F G +
        degreeZeroOmicronQuarticNoBDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceBDEFG810, degreeZeroOmicronQuarticNoBDEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoBDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDEFG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoBDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroOmicronQuarticNoBDEFG810]
  compute_degree
  omega

theorem omicronQuarticFaceBDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBDEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceBDEFG810 A B C D E F G).coeff (5 * B.natDegree) =
      (1 / 4096 : k) * omicronQuarticInnerBDEFG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
  simp only [omicronQuarticFaceBDEFG810, omicronQuarticInnerBDEFG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_BDF : ((B * D * F)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hFne, natDegree_mul hBne hDne]
    omega
  have hcf_BDF : ((B * D * F)).coeff (5 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BE2 : ((B * E ^ 2)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_BE2 : ((B * E ^ 2)).coeff (5 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_BE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D3 : (D ^ 3).natDegree = 5 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (5 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_FG : ((F * G)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hFne hGne]
    omega
  have hcf_FG : ((F * G)).coeff (5 * B.natDegree) =
      F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_FG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B5, hcf_B3E, hcf_BDF, hcf_BE2, hcf_D3, hcf_FG]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_BDEFG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDEFG810 A B C D E F G)
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
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerBDEFG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoBDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceBDEFG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_BDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerBDEFG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoBDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceBDEFG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_BDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerBDEFG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoBDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceBDEFG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * B.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_BDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerBDEFG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoBDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceBDEFG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_BDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1024 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerBDEFG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoBDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceBDEFG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hBpos, hDpos, hEpos, hFpos, hGpos, hBD, hBE, hBF, hBG, hAlt, hClt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_BDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_BDEFG_identity B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff
  have hpow : B.leadingCoeff ^ 12 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner] at hid
    simpa using hid.symm
  have hlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  exact hlc ((pow_eq_zero_iff (by decide : (12 : ℕ) ≠ 0)).mp hpow)


def kappaQuarticInnerCDEFG810 (c d e f g : k) : k :=
  5 * c * f + 5 * d * e

def muQuarticInnerCDEFG810 (c d e f g : k) : k :=
  (-5 : k) * c ^ 3 + 40 * c * g + 40 * d * f + 20 * e ^ 2

def nuQuarticInnerCDEFG810 (c d e f g : k) : k :=
  (-15 : k) * c ^ 2 * d + 40 * d * g + 40 * e * f

def xiQuarticInnerCDEFG810 (c d e f g : k) : k :=
  (-15 : k) * c ^ 2 * e + (-15 : k) * c * d ^ 2 + 40 * e * g + 20 * f ^ 2

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

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  simp only [degreeZeroKappaQuarticNoCDEFG810]
  compute_degree
  omega

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

set_option maxHeartbeats 16000000 in
def muQuarticFaceCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
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
theorem degreeZeroMuQuartic810_eq_CDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceCDEFG810 A B C D E F G +
        degreeZeroMuQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceCDEFG810, degreeZeroMuQuarticNoCDEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  simp only [degreeZeroMuQuarticNoCDEFG810]
  compute_degree
  omega

theorem muQuarticFaceCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceCDEFG810 A B C D E F G).coeff (3 * C.natDegree) =
      (1 / 128 : k) * muQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  simp only [muQuarticFaceCDEFG810, muQuarticInnerCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C3 : (C ^ 3).natDegree = 3 * C.natDegree := by
    rw [natDegree_pow]
  have hcf_C3 : (C ^ 3).coeff (3 * C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CG : ((C * G)).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hCne hGne]
    omega
  have hcf_CG : ((C * G)).coeff (3 * C.natDegree) =
      C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CG, coeff_natDegree, leadingCoeff_mul]
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
  rw [hcf_C3, hcf_CG, hcf_DF, hcf_E2]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoCDEFG810
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
theorem degreeZeroNuQuartic810_eq_CDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceCDEFG810 A B C D E F G +
        degreeZeroNuQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceCDEFG810, degreeZeroNuQuarticNoCDEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * C.natDegree + D.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  simp only [degreeZeroNuQuarticNoCDEFG810]
  compute_degree
  omega

theorem nuQuarticFaceCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceCDEFG810 A B C D E F G).coeff (2 * C.natDegree + D.natDegree) =
      (1 / 128 : k) * nuQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  simp only [nuQuarticFaceCDEFG810, nuQuarticInnerCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
  have hcf_C2D : ((C ^ 2 * D)).coeff (2 * C.natDegree + D.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DG : ((D * G)).natDegree = 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul hDne hGne]
    omega
  have hcf_DG : ((D * G)).coeff (2 * C.natDegree + D.natDegree) =
      D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_DG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_EF : ((E * F)).natDegree = 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (2 * C.natDegree + D.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_C2D, hcf_DG, hcf_EF]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
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
theorem degreeZeroXiQuartic810_eq_CDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceCDEFG810 A B C D E F G +
        degreeZeroXiQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceCDEFG810, degreeZeroXiQuarticNoCDEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G) :
    (degreeZeroXiQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  simp only [degreeZeroXiQuarticNoCDEFG810]
  compute_degree
  omega

theorem xiQuarticFaceCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (xiQuarticFaceCDEFG810 A B C D E F G).coeff (2 * C.natDegree + E.natDegree) =
      (1 / 128 : k) * xiQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  simp only [xiQuarticFaceCDEFG810, xiQuarticInnerCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = 2 * C.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
  have hcf_C2E : ((C ^ 2 * E)).coeff (2 * C.natDegree + E.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = 2 * C.natDegree + E.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (2 * C.natDegree + E.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_EG : ((E * G)).natDegree = 2 * C.natDegree + E.natDegree := by
    rw [natDegree_mul hEne hGne]
    omega
  have hcf_EG : ((E * G)).coeff (2 * C.natDegree + E.natDegree) =
      E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_EG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_F2 : (F ^ 2).natDegree = 2 * C.natDegree + E.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (2 * C.natDegree + E.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_C2E, hcf_CD2, hcf_EG, hcf_F2]
  ring

set_option maxHeartbeats 16000000 in
def omicronQuarticFaceCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * D * G)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
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
theorem degreeZeroOmicronQuartic810_eq_CDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceCDEFG810 A B C D E F G +
        degreeZeroOmicronQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceCDEFG810, degreeZeroOmicronQuarticNoCDEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * C.natDegree + F.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  simp only [degreeZeroOmicronQuarticNoCDEFG810]
  compute_degree
  omega

theorem omicronQuarticFaceCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceCDEFG810 A B C D E F G).coeff (2 * C.natDegree + F.natDegree) =
      (1 / 128 : k) * omicronQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  simp only [omicronQuarticFaceCDEFG810, omicronQuarticInnerCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C2F : ((C ^ 2 * F)).natDegree = 2 * C.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hFne, natDegree_pow]
  have hcf_C2F : ((C ^ 2 * F)).coeff (2 * C.natDegree + F.natDegree) =
      C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_C2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDE : ((C * D * E)).natDegree = 2 * C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hEne, natDegree_mul hCne hDne]
    omega
  have hcf_CDE : ((C * D * E)).coeff (2 * C.natDegree + F.natDegree) =
      C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_CDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D3 : (D ^ 3).natDegree = 2 * C.natDegree + F.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (2 * C.natDegree + F.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_FG : ((F * G)).natDegree = 2 * C.natDegree + F.natDegree := by
    rw [natDegree_mul hFne hGne]
    omega
  have hcf_FG : ((F * G)).coeff (2 * C.natDegree + F.natDegree) =
      F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_FG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_C2F, hcf_CDE, hcf_D3, hcf_FG]
  ring

set_option maxHeartbeats 16000000 in
def piQuarticFaceCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  + (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_CDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceCDEFG810 A B C D E F G +
        degreeZeroPiQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceCDEFG810, degreeZeroPiQuarticNoCDEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G) :
    (degreeZeroPiQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * C.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  simp only [degreeZeroPiQuarticNoCDEFG810]
  compute_degree
  omega

theorem piQuarticFaceCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceCDEFG810 A B C D E F G).coeff (4 * C.natDegree) =
      (1 / 256 : k) * piQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  simp only [piQuarticFaceCDEFG810, piQuarticInnerCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 4 * C.natDegree := by
    rw [natDegree_pow]
  have hcf_C4 : (C ^ 4).coeff (4 * C.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C2G : ((C ^ 2 * G)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow]
    omega
  have hcf_C2G : ((C ^ 2 * G)).coeff (4 * C.natDegree) =
      C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_C2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDF : ((C * D * F)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hFne, natDegree_mul hCne hDne]
    omega
  have hcf_CDF : ((C * D * F)).coeff (4 * C.natDegree) =
      C.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CE2 : ((C * E ^ 2)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_CE2 : ((C * E ^ 2)).coeff (4 * C.natDegree) =
      C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_CE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D2E : ((D ^ 2 * E)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hEne, natDegree_pow]
    omega
  have hcf_D2E : ((D ^ 2 * E)).coeff (4 * C.natDegree) =
      D.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_D2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_G2 : (G ^ 2).natDegree = 4 * C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_G2 : (G ^ 2).coeff (4 * C.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_C4, hcf_C2G, hcf_CDF, hcf_CE2, hcf_D2E, hcf_G2]
  ring

set_option maxHeartbeats 16000000 in
def primitiveQuarticFaceCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveQuarticNoCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  - (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 128 : k) • (A * B * C * G)
  + (5 / 32 : k) • (A * B * D * F)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (15 / 128 : k) • (A * C * D * E)
  + (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  + (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (171 / 262144 * l : k) • (A ^ 5 * E)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)
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
  + (1 / 128 * theta : k) • (A * B ^ 2)
  + (1 / 8 * theta : k) • (A * E)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveQuartic810_eq_CDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticFaceCDEFG810 A B C D E F G +
        degreeZeroPrimitiveQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810,
    rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810, primitiveQuarticFaceCDEFG810, degreeZeroPrimitiveQuarticNoCDEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveQuarticNoCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G) :
    (degreeZeroPrimitiveQuarticNoCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * C.natDegree + D.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  simp only [degreeZeroPrimitiveQuarticNoCDEFG810]
  compute_degree
  omega

theorem primitiveQuarticFaceCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (primitiveQuarticFaceCDEFG810 A B C D E F G).coeff (3 * C.natDegree + D.natDegree) =
      (1 / 128 : k) * primitiveQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
  simp only [primitiveQuarticFaceCDEFG810, primitiveQuarticInnerCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C3D : ((C ^ 3 * D)).natDegree = 3 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hCne) hDne, natDegree_pow]
  have hcf_C3D : ((C ^ 3 * D)).coeff (3 * C.natDegree + D.natDegree) =
      C.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_C3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDG : ((C * D * G)).natDegree = 3 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hGne, natDegree_mul hCne hDne]
    omega
  have hcf_CDG : ((C * D * G)).coeff (3 * C.natDegree + D.natDegree) =
      C.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CEF : ((C * E * F)).natDegree = 3 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hEne) hFne, natDegree_mul hCne hEne]
    omega
  have hcf_CEF : ((C * E * F)).coeff (3 * C.natDegree + D.natDegree) =
      C.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D2F : ((D ^ 2 * F)).natDegree = 3 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hFne, natDegree_pow]
    omega
  have hcf_D2F : ((D ^ 2 * F)).coeff (3 * C.natDegree + D.natDegree) =
      D.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_D2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE2 : ((D * E ^ 2)).natDegree = 3 * C.natDegree + D.natDegree := by
    rw [natDegree_mul hDne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_DE2 : ((D * E ^ 2)).coeff (3 * C.natDegree + D.natDegree) =
      D.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_DE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_C3D, hcf_CDG, hcf_CEF, hcf_D2F, hcf_DE2]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_CDEFG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEFG810 A B C D E F G)
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
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceCDEFG810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (C.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_CDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 16 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceCDEFG810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_CDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceCDEFG810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * C.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_CDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceCDEFG810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * C.natDegree + E.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_CDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceCDEFG810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * C.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_CDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceCDEFG810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_CDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 256 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveQuarticInnerCDEFG810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveQuarticNoCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := primitiveQuarticFaceCDEFG810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * C.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hGpos, hCD, hCE, hCF, hCG, hAlt, hBlt⟩
      omega
    rw [degreeZeroPrimitiveQuartic810_eq_CDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_CDEFG_identity C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff
  have hpow : F.leadingCoeff ^ 3 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  exact hlc ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hpow)


end QuarticKills810

end Max11DegreeRoutes
