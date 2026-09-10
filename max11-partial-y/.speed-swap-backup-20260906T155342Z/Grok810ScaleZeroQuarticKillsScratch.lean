import Grok810ScaleZeroQuarticDefsScratch

/-! # Quartic Stage A cone kills (monomial + multi certificates) -/

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

/-! ## Split lemmas, rest bounds, and cone kills -/

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 16000000 in
def muQuarticFaceB810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoB810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_eq_B_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceB810 A B C D E F G +
        degreeZeroMuQuarticNoB810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceB810, degreeZeroMuQuarticNoB810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoB810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeB810 A B C D E F G) :
    (degreeZeroMuQuarticNoB810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoB810]
  compute_degree
  omega


theorem quarticCone_B_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeB810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (35 / 2048 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceB810 A B C D E F G).natDegree = 4 * B.natDegree := by
    simp only [muQuarticFaceB810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoB810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_B_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceC810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoC810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_eq_C_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceC810 A B C D E F G +
        degreeZeroMuQuarticNoC810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceC810, degreeZeroMuQuarticNoC810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoC810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeC810 A B C D E F G) :
    (degreeZeroMuQuarticNoC810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt, hFlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 4 * F.natDegree + 1 ≤ 7 * C.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoC810]
  compute_degree
  omega


theorem quarticCone_C_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeC810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muQuarticFaceC810 A B C D E F G).natDegree = 3 * C.natDegree := by
    simp only [muQuarticFaceC810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoC810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_C_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def omicronQuarticFaceD810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoD810
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
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
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
theorem degreeZeroOmicronQuartic810_eq_D_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceD810 A B C D E F G +
        degreeZeroOmicronQuarticNoD810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceD810, degreeZeroOmicronQuarticNoD810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoD810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeD810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoD810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * D.natDegree := by
  rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt, hFlt, hGlt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : 5 * E.natDegree + 1 ≤ 6 * D.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 5 * F.natDegree + 1 ≤ 7 * D.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 5 * G.natDegree + 1 ≤ 8 * D.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroOmicronQuarticNoD810]
  compute_degree
  omega


theorem quarticCone_D_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeD810 A B C D E F G)
    (hdeg : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (omicronQuarticFaceD810 A B C D E F G).natDegree = 3 * D.natDegree := by
    simp only [omicronQuarticFaceD810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroOmicronQuarticNoD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroOmicronQuartic810_eq_D_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
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
theorem degreeZeroMuQuartic810_eq_E_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceE810 A B C D E F G +
        degreeZeroMuQuarticNoE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceE810, degreeZeroMuQuarticNoE810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeE810 A B C D E F G) :
    (degreeZeroMuQuarticNoE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hEpos, hAlt, hBlt, hClt, hDlt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 2 * B.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 3 * C.natDegree + 1 ≤ 2 * E.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 6 * D.natDegree + 1 ≤ 5 * E.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 6 * F.natDegree + 1 ≤ 7 * E.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 4 * E.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoE810]
  compute_degree
  omega


theorem quarticCone_E_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeE810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hEpos, hAlt, hBlt, hClt, hDlt, hFlt, hGlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceE810 A B C D E F G).natDegree = 2 * E.natDegree := by
    simp only [muQuarticFaceE810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_E_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hEpos, hAlt, hBlt, hClt, hDlt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def xiQuarticFaceF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoF810
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
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
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
theorem degreeZeroXiQuartic810_eq_F_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceF810 A B C D E F G +
        degreeZeroXiQuarticNoF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceF810, degreeZeroXiQuarticNoF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeF810 A B C D E F G) :
    (degreeZeroXiQuarticNoF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * F.natDegree := by
  rcases hcone with ⟨hFpos, hAlt, hBlt, hClt, hDlt, hElt, hGlt⟩
  have hA1 : 7 * A.natDegree + 1 ≤ 2 * F.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 7 * B.natDegree + 1 ≤ 3 * F.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 7 * C.natDegree + 1 ≤ 4 * F.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 7 * D.natDegree + 1 ≤ 5 * F.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 7 * E.natDegree + 1 ≤ 6 * F.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : 7 * G.natDegree + 1 ≤ 8 * F.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroXiQuarticNoF810]
  compute_degree
  omega


theorem quarticCone_F_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeF810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hFpos, hAlt, hBlt, hClt, hDlt, hElt, hGlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (xiQuarticFaceF810 A B C D E F G).natDegree = 2 * F.natDegree := by
    simp only [xiQuarticFaceF810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroXiQuarticNoF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_F_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hFpos, hAlt, hBlt, hClt, hDlt, hElt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def piQuarticFaceG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoG810
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
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
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
theorem degreeZeroPiQuartic810_eq_G_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceG810 A B C D E F G +
        degreeZeroPiQuarticNoG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceG810, degreeZeroPiQuarticNoG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeG810 A B C D E F G) :
    (degreeZeroPiQuarticNoG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * G.natDegree := by
  rcases hcone with ⟨hGpos, hAlt, hBlt, hClt, hDlt, hElt, hFlt⟩
  have hA1 : 4 * A.natDegree + 1 ≤ G.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 8 * B.natDegree + 1 ≤ 3 * G.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 2 * C.natDegree + 1 ≤ G.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 8 * D.natDegree + 1 ≤ 5 * G.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 4 * E.natDegree + 1 ≤ 3 * G.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 8 * F.natDegree + 1 ≤ 7 * G.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroPiQuarticNoG810]
  compute_degree
  omega


theorem quarticCone_G_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeG810 A B C D E F G)
    (hdeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hGpos, hAlt, hBlt, hClt, hDlt, hElt, hFlt⟩
    omega
  have hc : (5 / 4 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (piQuarticFaceG810 A B C D E F G).natDegree = 2 * G.natDegree := by
    simp only [piQuarticFaceG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroPiQuarticNoG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroPiQuartic810_eq_G_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hGpos, hAlt, hBlt, hClt, hDlt, hElt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceAB810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoAB810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_AB_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceAB810 A B C D E F G +
        degreeZeroKappaQuarticNoAB810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceAB810, degreeZeroKappaQuarticNoAB810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoAB810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAB810 A B C D E F G) :
    (degreeZeroKappaQuarticNoAB810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt, hFlt, hGlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoAB810]
  compute_degree
  omega


theorem quarticCone_AB_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAB810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (5 / 512 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceAB810 A B C D E F G).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaQuarticFaceAB810]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaQuarticNoAB810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_AB_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceAC810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoAC810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_eq_AC_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAC810 A B C D E F G +
        degreeZeroMuQuarticNoAC810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceAC810, degreeZeroMuQuarticNoAC810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoAC810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAC810 A B C D E F G) :
    (degreeZeroMuQuarticNoAC810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt, hFlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoAC810]
  compute_degree
  omega


theorem quarticCone_AC_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAC810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muQuarticFaceAC810 A B C D E F G).natDegree = 3 * C.natDegree := by
    simp only [muQuarticFaceAC810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoAC810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_AC_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceAD810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoAD810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_eq_AD_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAD810 A B C D E F G +
        degreeZeroMuQuarticNoAD810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceAD810, degreeZeroMuQuarticNoAD810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoAD810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAD810 A B C D E F G) :
    (degreeZeroMuQuarticNoAD810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt, hFlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoAD810]
  compute_degree
  omega


theorem quarticCone_AD_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAD810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muQuarticFaceAD810 A B C D E F G).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [muQuarticFaceAD810]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroMuQuarticNoAD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_AD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceAE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoAE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
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
theorem degreeZeroMuQuartic810_eq_AE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAE810 A B C D E F G +
        degreeZeroMuQuarticNoAE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceAE810, degreeZeroMuQuarticNoAE810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoAE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAE810 A B C D E F G) :
    (degreeZeroMuQuarticNoAE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt, hFlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoAE810]
  compute_degree
  omega


theorem quarticCone_AE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAE810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt, hFlt, hGlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceAE810 A B C D E F G).natDegree = 2 * E.natDegree := by
    simp only [muQuarticFaceAE810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoAE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_AE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def xiQuarticFaceAF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoAF810
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
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
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
theorem degreeZeroXiQuartic810_eq_AF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceAF810 A B C D E F G +
        degreeZeroXiQuarticNoAF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceAF810, degreeZeroXiQuarticNoAF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoAF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAF810 A B C D E F G) :
    (degreeZeroXiQuarticNoAF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * F.natDegree := by
  rcases hcone with ⟨hApos, hFpos, hAF, hBlt, hClt, hDlt, hElt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroXiQuarticNoAF810]
  compute_degree
  omega


theorem quarticCone_AF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAF810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hFpos, hAF, hBlt, hClt, hDlt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hFpos, hAF, hBlt, hClt, hDlt, hElt, hGlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (xiQuarticFaceAF810 A B C D E F G).natDegree = 2 * F.natDegree := by
    simp only [xiQuarticFaceAF810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroXiQuarticNoAF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_AF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hFpos, hAF, hBlt, hClt, hDlt, hElt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def piQuarticFaceAG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoAG810
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
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
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
theorem degreeZeroPiQuartic810_eq_AG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceAG810 A B C D E F G +
        degreeZeroPiQuarticNoAG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceAG810, degreeZeroPiQuarticNoAG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoAG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAG810 A B C D E F G) :
    (degreeZeroPiQuarticNoAG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * G.natDegree := by
  rcases hcone with ⟨hApos, hGpos, hAG, hBlt, hClt, hDlt, hElt, hFlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroPiQuarticNoAG810]
  compute_degree
  omega


theorem quarticCone_AG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAG810 A B C D E F G)
    (hdeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hGpos, hAG, hBlt, hClt, hDlt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hGpos, hAG, hBlt, hClt, hDlt, hElt, hFlt⟩
    omega
  have hc : (5 / 4 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (piQuarticFaceAG810 A B C D E F G).natDegree = 2 * G.natDegree := by
    simp only [piQuarticFaceAG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroPiQuarticNoAG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroPiQuartic810_eq_AG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hGpos, hAG, hBlt, hClt, hDlt, hElt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBC810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBC810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_BC_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBC810 A B C D E F G +
        degreeZeroKappaQuarticNoBC810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBC810, degreeZeroKappaQuarticNoBC810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBC810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBC810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBC810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      B.natDegree + 2 * C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoBC810]
  compute_degree
  omega


theorem quarticCone_BC_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBC810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaQuarticFaceBC810 A B C D E F G).natDegree = B.natDegree + 2 * C.natDegree := by
    simp only [kappaQuarticFaceBC810]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
  have hrest := degreeZeroKappaQuarticNoBC810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_BC_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBD810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBD810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_BD_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBD810 A B C D E F G +
        degreeZeroKappaQuarticNoBD810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBD810, degreeZeroKappaQuarticNoBD810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBD810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBD810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBD810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoBD810]
  compute_degree
  omega


theorem quarticCone_BD_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBD810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaQuarticFaceBD810 A B C D E F G).natDegree = 2 * B.natDegree + D.natDegree := by
    simp only [kappaQuarticFaceBD810]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hrest := degreeZeroKappaQuarticNoBD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_BD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceBF810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoBF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_eq_BF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBF810 A B C D E F G +
        degreeZeroMuQuarticNoBF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBF810, degreeZeroMuQuarticNoBF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoBF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBF810 A B C D E F G) :
    (degreeZeroMuQuarticNoBF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hFpos, hBF, hAlt, hClt, hDlt, hElt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoBF810]
  compute_degree
  omega


theorem quarticCone_BF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBF810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hFpos, hBF, hAlt, hClt, hDlt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hFpos, hBF, hAlt, hClt, hDlt, hElt, hGlt⟩
    omega
  have hc : (35 / 2048 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceBF810 A B C D E F G).natDegree = 4 * B.natDegree := by
    simp only [muQuarticFaceBF810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoBF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_BF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hFpos, hBF, hAlt, hClt, hDlt, hElt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
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
theorem degreeZeroKappaQuartic810_eq_BG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBG810 A B C D E F G +
        degreeZeroKappaQuarticNoBG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBG810, degreeZeroKappaQuarticNoBG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      B.natDegree + G.natDegree := by
  rcases hcone with ⟨hBpos, hGpos, hBG, hAlt, hClt, hDlt, hElt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroKappaQuarticNoBG810]
  compute_degree
  omega


theorem quarticCone_BG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hGpos, hBG, hAlt, hClt, hDlt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hGpos, hBG, hAlt, hClt, hDlt, hElt, hFlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceBG810 A B C D E F G).natDegree = B.natDegree + G.natDegree := by
    simp only [kappaQuarticFaceBG810]
    rw [natDegree_smul _ hc, natDegree_mul hBne hGne]
  have hrest := degreeZeroKappaQuarticNoBG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_BG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hGpos, hBG, hAlt, hClt, hDlt, hElt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceCD810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoCD810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_eq_CD_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceCD810 A B C D E F G +
        degreeZeroMuQuarticNoCD810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceCD810, degreeZeroMuQuarticNoCD810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoCD810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCD810 A B C D E F G) :
    (degreeZeroMuQuarticNoCD810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt, hFlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 4 * F.natDegree + 1 ≤ 7 * C.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoCD810]
  compute_degree
  omega


theorem quarticCone_CD_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCD810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muQuarticFaceCD810 A B C D E F G).natDegree = 3 * C.natDegree := by
    simp only [muQuarticFaceCD810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoCD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_CD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def xiQuarticFaceCE810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoCE810
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
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
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
theorem degreeZeroXiQuartic810_eq_CE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceCE810 A B C D E F G +
        degreeZeroXiQuarticNoCE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceCE810, degreeZeroXiQuarticNoCE810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoCE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCE810 A B C D E F G) :
    (degreeZeroXiQuarticNoCE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt, hFlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 4 * F.natDegree + 1 ≤ 7 * C.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroXiQuarticNoCE810]
  compute_degree
  omega


theorem quarticCone_CE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCE810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt, hFlt, hGlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (xiQuarticFaceCE810 A B C D E F G).natDegree = 2 * C.natDegree + E.natDegree := by
    simp only [xiQuarticFaceCE810]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
  have hrest := degreeZeroXiQuarticNoCE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_CE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceCF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoCF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_CF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCF810 A B C D E F G +
        degreeZeroKappaQuarticNoCF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceCF810, degreeZeroKappaQuarticNoCF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoCF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoCF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hCpos, hFpos, hCF, hAlt, hBlt, hDlt, hElt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoCF810]
  compute_degree
  omega


theorem quarticCone_CF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCF810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hFpos, hCF, hAlt, hBlt, hDlt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hFpos, hCF, hAlt, hBlt, hDlt, hElt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceCF810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceCF810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoCF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_CF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hFpos, hCF, hAlt, hBlt, hDlt, hElt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceDE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoDE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_DE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceDE810 A B C D E F G +
        degreeZeroKappaQuarticNoDE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceDE810, degreeZeroKappaQuarticNoDE810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoDE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDE810 A B C D E F G) :
    (degreeZeroKappaQuarticNoDE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt, hFlt, hGlt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  have hF1 : 5 * F.natDegree + 1 ≤ 7 * D.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 5 * G.natDegree + 1 ≤ 8 * D.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoDE810]
  compute_degree
  omega


theorem quarticCone_DE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDE810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt, hFlt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceDE810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceDE810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoDE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_DE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceDF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * F)

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoDF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
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
theorem degreeZeroMuQuartic810_eq_DF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceDF810 A B C D E F G +
        degreeZeroMuQuarticNoDF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceDF810, degreeZeroMuQuarticNoDF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoDF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDF810 A B C D E F G) :
    (degreeZeroMuQuarticNoDF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + F.natDegree := by
  rcases hcone with ⟨hDpos, hFpos, hDF, hAlt, hBlt, hClt, hElt, hGlt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : 5 * E.natDegree + 1 ≤ 6 * D.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : 5 * G.natDegree + 1 ≤ 8 * D.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoDF810]
  compute_degree
  omega


theorem quarticCone_DF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDF810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hFpos, hDF, hAlt, hBlt, hClt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hFpos, hDF, hAlt, hBlt, hClt, hElt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceDF810 A B C D E F G).natDegree = D.natDegree + F.natDegree := by
    simp only [muQuarticFaceDF810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hFne]
  have hrest := degreeZeroMuQuarticNoDF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_DF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hFpos, hDF, hAlt, hBlt, hClt, hElt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def nuQuarticFaceDG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * G)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoDG810
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
theorem degreeZeroNuQuartic810_eq_DG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceDG810 A B C D E F G +
        degreeZeroNuQuarticNoDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceDG810, degreeZeroNuQuarticNoDG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoDG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDG810 A B C D E F G) :
    (degreeZeroNuQuarticNoDG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + G.natDegree := by
  rcases hcone with ⟨hDpos, hGpos, hDG, hAlt, hBlt, hClt, hElt, hFlt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : 5 * E.natDegree + 1 ≤ 6 * D.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 5 * F.natDegree + 1 ≤ 7 * D.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroNuQuarticNoDG810]
  compute_degree
  omega


theorem quarticCone_DG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDG810 A B C D E F G)
    (hdeg : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hGpos, hDG, hAlt, hBlt, hClt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hGpos, hDG, hAlt, hBlt, hClt, hElt, hFlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (nuQuarticFaceDG810 A B C D E F G).natDegree = D.natDegree + G.natDegree := by
    simp only [nuQuarticFaceDG810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hGne]
  have hrest := degreeZeroNuQuarticNoDG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroNuQuartic810_eq_DG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hGpos, hDG, hAlt, hBlt, hClt, hElt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
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
theorem degreeZeroMuQuartic810_eq_EF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceEF810 A B C D E F G +
        degreeZeroMuQuarticNoEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceEF810, degreeZeroMuQuarticNoEF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeEF810 A B C D E F G) :
    (degreeZeroMuQuarticNoEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hEpos, hFpos, hEF, hAlt, hBlt, hClt, hDlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 2 * B.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 3 * C.natDegree + 1 ≤ 2 * E.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 6 * D.natDegree + 1 ≤ 5 * E.natDegree := Nat.succ_le_of_lt hDlt
  have hG1 : 3 * G.natDegree + 1 ≤ 4 * E.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoEF810]
  compute_degree
  omega


theorem quarticCone_EF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeEF810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hEpos, hFpos, hEF, hAlt, hBlt, hClt, hDlt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hEpos, hFpos, hEF, hAlt, hBlt, hClt, hDlt, hGlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceEF810 A B C D E F G).natDegree = 2 * E.natDegree := by
    simp only [muQuarticFaceEF810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_EF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hEpos, hFpos, hEF, hAlt, hBlt, hClt, hDlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
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
theorem degreeZeroMuQuartic810_eq_EG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceEG810 A B C D E F G +
        degreeZeroMuQuarticNoEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceEG810, degreeZeroMuQuarticNoEG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeEG810 A B C D E F G) :
    (degreeZeroMuQuarticNoEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hEpos, hGpos, hEG, hAlt, hBlt, hClt, hDlt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 2 * B.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 3 * C.natDegree + 1 ≤ 2 * E.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 6 * D.natDegree + 1 ≤ 5 * E.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 6 * F.natDegree + 1 ≤ 7 * E.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroMuQuarticNoEG810]
  compute_degree
  omega


theorem quarticCone_EG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeEG810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hEpos, hGpos, hEG, hAlt, hBlt, hClt, hDlt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hEpos, hGpos, hEG, hAlt, hBlt, hClt, hDlt, hFlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceEG810 A B C D E F G).natDegree = 2 * E.natDegree := by
    simp only [muQuarticFaceEG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_EG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hEpos, hGpos, hEG, hAlt, hBlt, hClt, hDlt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def xiQuarticFaceFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoFG810
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
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
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
theorem degreeZeroXiQuartic810_eq_FG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceFG810 A B C D E F G +
        degreeZeroXiQuarticNoFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceFG810, degreeZeroXiQuarticNoFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeFG810 A B C D E F G) :
    (degreeZeroXiQuarticNoFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * F.natDegree := by
  rcases hcone with ⟨hFpos, hGpos, hFG, hAlt, hBlt, hClt, hDlt, hElt⟩
  have hA1 : 7 * A.natDegree + 1 ≤ 2 * F.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 7 * B.natDegree + 1 ≤ 3 * F.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 7 * C.natDegree + 1 ≤ 4 * F.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 7 * D.natDegree + 1 ≤ 5 * F.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 7 * E.natDegree + 1 ≤ 6 * F.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroXiQuarticNoFG810]
  compute_degree
  omega


theorem quarticCone_FG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeFG810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hFpos, hGpos, hFG, hAlt, hBlt, hClt, hDlt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hFpos, hGpos, hFG, hAlt, hBlt, hClt, hDlt, hElt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (xiQuarticFaceFG810 A B C D E F G).natDegree = 2 * F.natDegree := by
    simp only [xiQuarticFaceFG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroXiQuarticNoFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_FG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hFpos, hGpos, hFG, hAlt, hBlt, hClt, hDlt, hElt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_ABE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABE810 A B C D E F G +
        degreeZeroKappaQuarticNoABE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABE810, degreeZeroKappaQuarticNoABE810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoABE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABE810 A B C D E F G) :
    (degreeZeroKappaQuarticNoABE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt, hFlt, hGlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoABE810]
  compute_degree
  omega


theorem quarticCone_ABE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABE810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt, hFlt, hGlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt, hFlt, hGlt⟩
    omega
  have hc : (5 / 512 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceABE810 A B C D E F G).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaQuarticFaceABE810]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaQuarticNoABE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ABE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_ABF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABF810 A B C D E F G +
        degreeZeroKappaQuarticNoABF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABF810, degreeZeroKappaQuarticNoABF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoABF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoABF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hFpos, hAB, hAF, hClt, hDlt, hElt, hGlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoABF810]
  compute_degree
  omega


theorem quarticCone_ABF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABF810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hFpos, hAB, hAF, hClt, hDlt, hElt, hGlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hFpos, hAB, hAF, hClt, hDlt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hFpos, hAB, hAF, hClt, hDlt, hElt, hGlt⟩
    omega
  have hc : (5 / 512 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceABF810 A B C D E F G).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaQuarticFaceABF810]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaQuarticNoABF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ABF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hBpos, hFpos, hAB, hAF, hClt, hDlt, hElt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceABG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoABG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_eq_ABG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceABG810 A B C D E F G +
        degreeZeroMuQuarticNoABG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceABG810, degreeZeroMuQuarticNoABG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoABG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABG810 A B C D E F G) :
    (degreeZeroMuQuarticNoABG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hGpos, hAB, hAG, hClt, hDlt, hElt, hFlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroMuQuarticNoABG810]
  compute_degree
  omega


theorem quarticCone_ABG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABG810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hGpos, hAB, hAG, hClt, hDlt, hElt, hFlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hGpos, hAB, hAG, hClt, hDlt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hGpos, hAB, hAG, hClt, hDlt, hElt, hFlt⟩
    omega
  have hc : (35 / 2048 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceABG810 A B C D E F G).natDegree = 4 * B.natDegree := by
    simp only [muQuarticFaceABG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoABG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_ABG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hBpos, hGpos, hAB, hAG, hClt, hDlt, hElt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def nuQuarticFaceACD810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * D)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoACD810
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
theorem degreeZeroNuQuartic810_eq_ACD_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceACD810 A B C D E F G +
        degreeZeroNuQuarticNoACD810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceACD810, degreeZeroNuQuarticNoACD810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoACD810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACD810 A B C D E F G) :
    (degreeZeroNuQuarticNoACD810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * C.natDegree + D.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt, hFlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroNuQuarticNoACD810]
  compute_degree
  omega


theorem quarticCone_ACD_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACD810 A B C D E F G)
    (hdeg : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt, hFlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (nuQuarticFaceACD810 A B C D E F G).natDegree = 2 * C.natDegree + D.natDegree := by
    simp only [nuQuarticFaceACD810]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
  have hrest := degreeZeroNuQuarticNoACD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroNuQuartic810_eq_ACD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def xiQuarticFaceACE810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoACE810
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
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
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
theorem degreeZeroXiQuartic810_eq_ACE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceACE810 A B C D E F G +
        degreeZeroXiQuarticNoACE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceACE810, degreeZeroXiQuarticNoACE810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoACE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACE810 A B C D E F G) :
    (degreeZeroXiQuarticNoACE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt, hFlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroXiQuarticNoACE810]
  compute_degree
  omega


theorem quarticCone_ACE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACE810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt, hFlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt, hFlt, hGlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (xiQuarticFaceACE810 A B C D E F G).natDegree = 2 * C.natDegree + E.natDegree := by
    simp only [xiQuarticFaceACE810]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
  have hrest := degreeZeroXiQuarticNoACE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_ACE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceACF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoACF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_ACF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACF810 A B C D E F G +
        degreeZeroKappaQuarticNoACF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceACF810, degreeZeroKappaQuarticNoACF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoACF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoACF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hFpos, hAC, hAF, hBlt, hDlt, hElt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoACF810]
  compute_degree
  omega


theorem quarticCone_ACF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACF810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hFpos, hAC, hAF, hBlt, hDlt, hElt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hFpos, hAC, hAF, hBlt, hDlt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hFpos, hAC, hAF, hBlt, hDlt, hElt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceACF810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceACF810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoACF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ACF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hFpos, hAC, hAF, hBlt, hDlt, hElt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceADE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoADE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_ADE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceADE810 A B C D E F G +
        degreeZeroKappaQuarticNoADE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceADE810, degreeZeroKappaQuarticNoADE810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoADE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADE810 A B C D E F G) :
    (degreeZeroKappaQuarticNoADE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt, hFlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoADE810]
  compute_degree
  omega


theorem quarticCone_ADE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADE810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt, hFlt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceADE810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceADE810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoADE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ADE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def omicronQuarticFaceADF810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoADF810
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
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
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
theorem degreeZeroOmicronQuartic810_eq_ADF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceADF810 A B C D E F G +
        degreeZeroOmicronQuarticNoADF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceADF810, degreeZeroOmicronQuarticNoADF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoADF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADF810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoADF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * D.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hFpos, hAD, hAF, hBlt, hClt, hElt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroOmicronQuarticNoADF810]
  compute_degree
  omega


theorem quarticCone_ADF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADF810 A B C D E F G)
    (hdeg : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hFpos, hAD, hAF, hBlt, hClt, hElt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hFpos, hAD, hAF, hBlt, hClt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hFpos, hAD, hAF, hBlt, hClt, hElt, hGlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (omicronQuarticFaceADF810 A B C D E F G).natDegree = 3 * D.natDegree := by
    simp only [omicronQuarticFaceADF810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroOmicronQuarticNoADF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroOmicronQuartic810_eq_ADF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hFpos, hAD, hAF, hBlt, hClt, hElt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceADG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoADG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_eq_ADG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceADG810 A B C D E F G +
        degreeZeroMuQuarticNoADG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceADG810, degreeZeroMuQuarticNoADG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoADG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADG810 A B C D E F G) :
    (degreeZeroMuQuarticNoADG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hGpos, hAD, hAG, hBlt, hClt, hElt, hFlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroMuQuarticNoADG810]
  compute_degree
  omega


theorem quarticCone_ADG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADG810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hGpos, hAD, hAG, hBlt, hClt, hElt, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hGpos, hAD, hAG, hBlt, hClt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hGpos, hAD, hAG, hBlt, hClt, hElt, hFlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muQuarticFaceADG810 A B C D E F G).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [muQuarticFaceADG810]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroMuQuarticNoADG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_ADG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hGpos, hAD, hAG, hBlt, hClt, hElt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceAEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoAEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
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
theorem degreeZeroMuQuartic810_eq_AEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAEF810 A B C D E F G +
        degreeZeroMuQuarticNoAEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceAEF810, degreeZeroMuQuarticNoAEF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoAEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAEF810 A B C D E F G) :
    (degreeZeroMuQuarticNoAEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hApos, hEpos, hFpos, hAE, hAF, hBlt, hClt, hDlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroMuQuarticNoAEF810]
  compute_degree
  omega


theorem quarticCone_AEF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAEF810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hFpos, hAE, hAF, hBlt, hClt, hDlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hFpos, hAE, hAF, hBlt, hClt, hDlt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hFpos, hAE, hAF, hBlt, hClt, hDlt, hGlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceAEF810 A B C D E F G).natDegree = 2 * E.natDegree := by
    simp only [muQuarticFaceAEF810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoAEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_AEF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hEpos, hFpos, hAE, hAF, hBlt, hClt, hDlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceAEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoAEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
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
theorem degreeZeroMuQuartic810_eq_AEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAEG810 A B C D E F G +
        degreeZeroMuQuarticNoAEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceAEG810, degreeZeroMuQuarticNoAEG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoAEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAEG810 A B C D E F G) :
    (degreeZeroMuQuarticNoAEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hApos, hEpos, hGpos, hAE, hAG, hBlt, hClt, hDlt, hFlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroMuQuarticNoAEG810]
  compute_degree
  omega


theorem quarticCone_AEG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAEG810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hGpos, hAE, hAG, hBlt, hClt, hDlt, hFlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hGpos, hAE, hAG, hBlt, hClt, hDlt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hGpos, hAE, hAG, hBlt, hClt, hDlt, hFlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceAEG810 A B C D E F G).natDegree = 2 * E.natDegree := by
    simp only [muQuarticFaceAEG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoAEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_AEG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hEpos, hGpos, hAE, hAG, hBlt, hClt, hDlt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def xiQuarticFaceAFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoAFG810
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
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
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
theorem degreeZeroXiQuartic810_eq_AFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceAFG810 A B C D E F G +
        degreeZeroXiQuarticNoAFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceAFG810, degreeZeroXiQuarticNoAFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoAFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAFG810 A B C D E F G) :
    (degreeZeroXiQuarticNoAFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * F.natDegree := by
  rcases hcone with ⟨hApos, hFpos, hGpos, hAF, hAG, hBlt, hClt, hDlt, hElt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroXiQuarticNoAFG810]
  compute_degree
  omega


theorem quarticCone_AFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAFG810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hFpos, hGpos, hAF, hAG, hBlt, hClt, hDlt, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hFpos, hGpos, hAF, hAG, hBlt, hClt, hDlt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hFpos, hGpos, hAF, hAG, hBlt, hClt, hDlt, hElt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (xiQuarticFaceAFG810 A B C D E F G).natDegree = 2 * F.natDegree := by
    simp only [xiQuarticFaceAFG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroXiQuarticNoAFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_AFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hFpos, hGpos, hAF, hAG, hBlt, hClt, hDlt, hElt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBCE810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBCE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_BCE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBCE810 A B C D E F G +
        degreeZeroKappaQuarticNoBCE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBCE810, degreeZeroKappaQuarticNoBCE810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBCE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCE810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBCE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      B.natDegree + 2 * C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoBCE810]
  compute_degree
  omega


theorem quarticCone_BCE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCE810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt, hFlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt, hFlt, hGlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaQuarticFaceBCE810 A B C D E F G).natDegree = B.natDegree + 2 * C.natDegree := by
    simp only [kappaQuarticFaceBCE810]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
  have hrest := degreeZeroKappaQuarticNoBCE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_BCE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def nuQuarticFaceBCG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoBCG810
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
theorem degreeZeroNuQuartic810_eq_BCG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBCG810 A B C D E F G +
        degreeZeroNuQuarticNoBCG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBCG810, degreeZeroNuQuarticNoBCG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoBCG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCG810 A B C D E F G) :
    (degreeZeroNuQuarticNoBCG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hGpos, hBC, hBG, hAlt, hDlt, hElt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroNuQuarticNoBCG810]
  compute_degree
  omega


theorem quarticCone_BCG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCG810 A B C D E F G)
    (hdeg : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hGpos, hBC, hBG, hAlt, hDlt, hElt, hFlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hGpos, hBC, hBG, hAlt, hDlt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hGpos, hBC, hBG, hAlt, hDlt, hElt, hFlt⟩
    omega
  have hc : (35 / 512 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (nuQuarticFaceBCG810 A B C D E F G).natDegree = 3 * B.natDegree + C.natDegree := by
    simp only [nuQuarticFaceBCG810]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
  have hrest := degreeZeroNuQuarticNoBCG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroNuQuartic810_eq_BCG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hCpos, hGpos, hBC, hBG, hAlt, hDlt, hElt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def nuQuarticFaceBDE810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * D ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoBDE810
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
theorem degreeZeroNuQuartic810_eq_BDE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceBDE810 A B C D E F G +
        degreeZeroNuQuarticNoBDE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceBDE810, degreeZeroNuQuarticNoBDE810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoBDE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDE810 A B C D E F G) :
    (degreeZeroNuQuarticNoBDE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      B.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroNuQuarticNoBDE810]
  compute_degree
  omega


theorem quarticCone_BDE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDE810 A B C D E F G)
    (hdeg : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt, hFlt, hGlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (nuQuarticFaceBDE810 A B C D E F G).natDegree = B.natDegree + 2 * D.natDegree := by
    simp only [nuQuarticFaceBDE810]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroNuQuarticNoBDE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroNuQuartic810_eq_BDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBDF810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBDF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_BDF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBDF810 A B C D E F G +
        degreeZeroKappaQuarticNoBDF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBDF810, degreeZeroKappaQuarticNoBDF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBDF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBDF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hFpos, hBD, hBF, hAlt, hClt, hElt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoBDF810]
  compute_degree
  omega


theorem quarticCone_BDF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDF810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hFpos, hBD, hBF, hAlt, hClt, hElt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hFpos, hBD, hBF, hAlt, hClt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hFpos, hBD, hBF, hAlt, hClt, hElt, hGlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaQuarticFaceBDF810 A B C D E F G).natDegree = 2 * B.natDegree + D.natDegree := by
    simp only [kappaQuarticFaceBDF810]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hrest := degreeZeroKappaQuarticNoBDF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_BDF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, hFpos, hBD, hBF, hAlt, hClt, hElt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceBDG810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoBDG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
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

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuartic810_eq_BDG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBDG810 A B C D E F G +
        degreeZeroMuQuarticNoBDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBDG810, degreeZeroMuQuarticNoBDG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoBDG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDG810 A B C D E F G) :
    (degreeZeroMuQuarticNoBDG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hGpos, hBD, hBG, hAlt, hClt, hElt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroMuQuarticNoBDG810]
  compute_degree
  omega


theorem quarticCone_BDG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDG810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hGpos, hBD, hBG, hAlt, hClt, hElt, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hGpos, hBD, hBG, hAlt, hClt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hGpos, hBD, hBG, hAlt, hClt, hElt, hFlt⟩
    omega
  have hc : (35 / 2048 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceBDG810 A B C D E F G).natDegree = 4 * B.natDegree := by
    simp only [muQuarticFaceBDG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoBDG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_BDG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, hGpos, hBD, hBG, hAlt, hClt, hElt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def xiQuarticFaceBEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoBEF810
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
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
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
theorem degreeZeroXiQuartic810_eq_BEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceBEF810 A B C D E F G +
        degreeZeroXiQuarticNoBEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceBEF810, degreeZeroXiQuarticNoBEF810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoBEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBEF810 A B C D E F G) :
    (degreeZeroXiQuarticNoBEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * F.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, hFpos, hBE, hBF, hAlt, hClt, hDlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroXiQuarticNoBEF810]
  compute_degree
  omega


theorem quarticCone_BEF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBEF810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hFpos, hBE, hBF, hAlt, hClt, hDlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hFpos, hBE, hBF, hAlt, hClt, hDlt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hFpos, hBE, hBF, hAlt, hClt, hDlt, hGlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (xiQuarticFaceBEF810 A B C D E F G).natDegree = 2 * F.natDegree := by
    simp only [xiQuarticFaceBEF810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroXiQuarticNoBEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_BEF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hEpos, hFpos, hBE, hBF, hAlt, hClt, hDlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
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
theorem degreeZeroKappaQuartic810_eq_BEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBEG810 A B C D E F G +
        degreeZeroKappaQuarticNoBEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBEG810, degreeZeroKappaQuarticNoBEG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBEG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      B.natDegree + G.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, hGpos, hBE, hBG, hAlt, hClt, hDlt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroKappaQuarticNoBEG810]
  compute_degree
  omega


theorem quarticCone_BEG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBEG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hGpos, hBE, hBG, hAlt, hClt, hDlt, hFlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hGpos, hBE, hBG, hAlt, hClt, hDlt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hGpos, hBE, hBG, hAlt, hClt, hDlt, hFlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceBEG810 A B C D E F G).natDegree = B.natDegree + G.natDegree := by
    simp only [kappaQuarticFaceBEG810]
    rw [natDegree_smul _ hc, natDegree_mul hBne hGne]
  have hrest := degreeZeroKappaQuarticNoBEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_BEG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hEpos, hGpos, hBE, hBG, hAlt, hClt, hDlt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
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
theorem degreeZeroKappaQuartic810_eq_BFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBFG810 A B C D E F G +
        degreeZeroKappaQuarticNoBFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBFG810, degreeZeroKappaQuarticNoBFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      B.natDegree + G.natDegree := by
  rcases hcone with ⟨hBpos, hFpos, hGpos, hBF, hBG, hAlt, hClt, hDlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaQuarticNoBFG810]
  compute_degree
  omega


theorem quarticCone_BFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBFG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hFpos, hGpos, hBF, hBG, hAlt, hClt, hDlt, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hFpos, hGpos, hBF, hBG, hAlt, hClt, hDlt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hFpos, hGpos, hBF, hBG, hAlt, hClt, hDlt, hElt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceBFG810 A B C D E F G).natDegree = B.natDegree + G.natDegree := by
    simp only [kappaQuarticFaceBFG810]
    rw [natDegree_smul _ hc, natDegree_mul hBne hGne]
  have hrest := degreeZeroKappaQuarticNoBFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_BFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hFpos, hGpos, hBF, hBG, hAlt, hClt, hDlt, hElt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceCDE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoCDE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_CDE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCDE810 A B C D E F G +
        degreeZeroKappaQuarticNoCDE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceCDE810, degreeZeroKappaQuarticNoCDE810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoCDE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDE810 A B C D E F G) :
    (degreeZeroKappaQuarticNoCDE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt, hFlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hF1 : 4 * F.natDegree + 1 ≤ 7 * C.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoCDE810]
  compute_degree
  omega


theorem quarticCone_CDE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDE810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt, hFlt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceCDE810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceCDE810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoCDE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_CDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceCDF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoCDF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_CDF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCDF810 A B C D E F G +
        degreeZeroKappaQuarticNoCDF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceCDF810, degreeZeroKappaQuarticNoCDF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoCDF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoCDF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hFpos, hCD, hCF, hAlt, hBlt, hElt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoCDF810]
  compute_degree
  omega


theorem quarticCone_CDF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDF810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hFpos, hCD, hCF, hAlt, hBlt, hElt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hFpos, hCD, hCF, hAlt, hBlt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hFpos, hCD, hCF, hAlt, hBlt, hElt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceCDF810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceCDF810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoCDF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_CDF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, hFpos, hCD, hCF, hAlt, hBlt, hElt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def xiQuarticFaceCDG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C * D ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoCDG810
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
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)
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
theorem degreeZeroXiQuartic810_eq_CDG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceCDG810 A B C D E F G +
        degreeZeroXiQuarticNoCDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceCDG810, degreeZeroXiQuarticNoCDG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoCDG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDG810 A B C D E F G) :
    (degreeZeroXiQuarticNoCDG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hGpos, hCD, hCG, hAlt, hBlt, hElt, hFlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 4 * F.natDegree + 1 ≤ 7 * C.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroXiQuarticNoCDG810]
  compute_degree
  omega


theorem quarticCone_CDG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDG810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hGpos, hCD, hCG, hAlt, hBlt, hElt, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hGpos, hCD, hCG, hAlt, hBlt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hGpos, hCD, hCG, hAlt, hBlt, hElt, hFlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (xiQuarticFaceCDG810 A B C D E F G).natDegree = C.natDegree + 2 * D.natDegree := by
    simp only [xiQuarticFaceCDG810]
    rw [natDegree_smul _ hc, natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroXiQuarticNoCDG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_CDG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, hGpos, hCD, hCG, hAlt, hBlt, hElt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceCEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoCEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_CEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCEF810 A B C D E F G +
        degreeZeroKappaQuarticNoCEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceCEF810, degreeZeroKappaQuarticNoCEF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoCEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCEF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoCEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hCpos, hEpos, hFpos, hCE, hCF, hAlt, hBlt, hDlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoCEF810]
  compute_degree
  omega


theorem quarticCone_CEF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCEF810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hFpos, hCE, hCF, hAlt, hBlt, hDlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hFpos, hCE, hCF, hAlt, hBlt, hDlt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hFpos, hCE, hCF, hAlt, hBlt, hDlt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceCEF810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceCEF810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoCEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_CEF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hEpos, hFpos, hCE, hCF, hAlt, hBlt, hDlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceCFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoCFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_CFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCFG810 A B C D E F G +
        degreeZeroKappaQuarticNoCFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceCFG810, degreeZeroKappaQuarticNoCFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoCFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoCFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hCpos, hFpos, hGpos, hCF, hCG, hAlt, hBlt, hDlt, hElt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaQuarticNoCFG810]
  compute_degree
  omega


theorem quarticCone_CFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCFG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hFpos, hGpos, hCF, hCG, hAlt, hBlt, hDlt, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hFpos, hGpos, hCF, hCG, hAlt, hBlt, hDlt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hFpos, hGpos, hCF, hCG, hAlt, hBlt, hDlt, hElt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceCFG810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceCFG810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoCFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_CFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hFpos, hGpos, hCF, hCG, hAlt, hBlt, hDlt, hElt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceDEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_DEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceDEF810 A B C D E F G +
        degreeZeroKappaQuarticNoDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceDEF810, degreeZeroKappaQuarticNoDEF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDEF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hDpos, hEpos, hFpos, hDE, hDF, hAlt, hBlt, hClt, hGlt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  have hG1 : 5 * G.natDegree + 1 ≤ 8 * D.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoDEF810]
  compute_degree
  omega


theorem quarticCone_DEF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDEF810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hFpos, hDE, hDF, hAlt, hBlt, hClt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hFpos, hDE, hDF, hAlt, hBlt, hClt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hFpos, hDE, hDF, hAlt, hBlt, hClt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceDEF810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceDEF810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_DEF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hEpos, hFpos, hDE, hDF, hAlt, hBlt, hClt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceDEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_DEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceDEG810 A B C D E F G +
        degreeZeroKappaQuarticNoDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceDEG810, degreeZeroKappaQuarticNoDEG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDEG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hDpos, hEpos, hGpos, hDE, hDG, hAlt, hBlt, hClt, hFlt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  have hF1 : 5 * F.natDegree + 1 ≤ 7 * D.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroKappaQuarticNoDEG810]
  compute_degree
  omega


theorem quarticCone_DEG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDEG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hGpos, hDE, hDG, hAlt, hBlt, hClt, hFlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hGpos, hDE, hDG, hAlt, hBlt, hClt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hGpos, hDE, hDG, hAlt, hBlt, hClt, hFlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceDEG810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceDEG810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_DEG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hEpos, hGpos, hDE, hDG, hAlt, hBlt, hClt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceDFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * F)

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
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
theorem degreeZeroMuQuartic810_eq_DFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceDFG810 A B C D E F G +
        degreeZeroMuQuarticNoDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceDFG810, degreeZeroMuQuarticNoDFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + F.natDegree := by
  rcases hcone with ⟨hDpos, hFpos, hGpos, hDF, hDG, hAlt, hBlt, hClt, hElt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : 5 * E.natDegree + 1 ≤ 6 * D.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroMuQuarticNoDFG810]
  compute_degree
  omega


theorem quarticCone_DFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDFG810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hFpos, hGpos, hDF, hDG, hAlt, hBlt, hClt, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hFpos, hGpos, hDF, hDG, hAlt, hBlt, hClt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hFpos, hGpos, hDF, hDG, hAlt, hBlt, hClt, hElt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceDFG810 A B C D E F G).natDegree = D.natDegree + F.natDegree := by
    simp only [muQuarticFaceDFG810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hFne]
  have hrest := degreeZeroMuQuarticNoDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_DFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hFpos, hGpos, hDF, hDG, hAlt, hBlt, hClt, hElt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
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
theorem degreeZeroMuQuartic810_eq_EFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceEFG810 A B C D E F G +
        degreeZeroMuQuarticNoEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceEFG810, degreeZeroMuQuarticNoEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeEFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hEpos, hFpos, hGpos, hEF, hEG, hAlt, hBlt, hClt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 2 * B.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 3 * C.natDegree + 1 ≤ 2 * E.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 6 * D.natDegree + 1 ≤ 5 * E.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroMuQuarticNoEFG810]
  compute_degree
  omega


theorem quarticCone_EFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeEFG810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hEpos, hFpos, hGpos, hEF, hEG, hAlt, hBlt, hClt, hDlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hEpos, hFpos, hGpos, hEF, hEG, hAlt, hBlt, hClt, hDlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hEpos, hFpos, hGpos, hEF, hEG, hAlt, hBlt, hClt, hDlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceEFG810 A B C D E F G).natDegree = 2 * E.natDegree := by
    simp only [muQuarticFaceEFG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_EFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hEpos, hFpos, hGpos, hEF, hEG, hAlt, hBlt, hClt, hDlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_ABEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABEF810 A B C D E F G +
        degreeZeroKappaQuarticNoABEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABEF810, degreeZeroKappaQuarticNoABEF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoABEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABEF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoABEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hEpos, hFpos, hAB, hAE, hAF, hClt, hDlt, hGlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoABEF810]
  compute_degree
  omega


theorem quarticCone_ABEF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABEF810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hFpos, hAB, hAE, hAF, hClt, hDlt, hGlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hFpos, hAB, hAE, hAF, hClt, hDlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hFpos, hAB, hAE, hAF, hClt, hDlt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hFpos, hAB, hAE, hAF, hClt, hDlt, hGlt⟩
    omega
  have hc : (5 / 512 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceABEF810 A B C D E F G).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaQuarticFaceABEF810]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaQuarticNoABEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ABEF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hBpos, hEpos, hFpos, hAB, hAE, hAF, hClt, hDlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceACDE810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoACDE810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_ACDE_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACDE810 A B C D E F G +
        degreeZeroKappaQuarticNoACDE810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceACDE810, degreeZeroKappaQuarticNoACDE810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoACDE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDE810 A B C D E F G) :
    (degreeZeroKappaQuarticNoACDE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt, hFlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoACDE810]
  compute_degree
  omega


theorem quarticCone_ACDE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDE810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt, hFlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt, hFlt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceACDE810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceACDE810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoACDE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ACDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt, hFlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceACDF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoACDF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_ACDF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACDF810 A B C D E F G +
        degreeZeroKappaQuarticNoACDF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceACDF810, degreeZeroKappaQuarticNoACDF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoACDF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoACDF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hAC, hAD, hAF, hBlt, hElt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoACDF810]
  compute_degree
  omega


theorem quarticCone_ACDF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDF810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hAC, hAD, hAF, hBlt, hElt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hAC, hAD, hAF, hBlt, hElt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hAC, hAD, hAF, hBlt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hAC, hAD, hAF, hBlt, hElt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceACDF810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceACDF810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoACDF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ACDF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hAC, hAD, hAF, hBlt, hElt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def xiQuarticFaceACDG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C * D ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoACDG810
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
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)
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
theorem degreeZeroXiQuartic810_eq_ACDG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceACDG810 A B C D E F G +
        degreeZeroXiQuarticNoACDG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceACDG810, degreeZeroXiQuarticNoACDG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoACDG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDG810 A B C D E F G) :
    (degreeZeroXiQuarticNoACDG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hGpos, hAC, hAD, hAG, hBlt, hElt, hFlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroXiQuarticNoACDG810]
  compute_degree
  omega


theorem quarticCone_ACDG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDG810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hGpos, hAC, hAD, hAG, hBlt, hElt, hFlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hGpos, hAC, hAD, hAG, hBlt, hElt, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hGpos, hAC, hAD, hAG, hBlt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hGpos, hAC, hAD, hAG, hBlt, hElt, hFlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (xiQuarticFaceACDG810 A B C D E F G).natDegree = C.natDegree + 2 * D.natDegree := by
    simp only [xiQuarticFaceACDG810]
    rw [natDegree_smul _ hc, natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroXiQuarticNoACDG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_ACDG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hDpos, hGpos, hAC, hAD, hAG, hBlt, hElt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceACEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoACEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_ACEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACEF810 A B C D E F G +
        degreeZeroKappaQuarticNoACEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceACEF810, degreeZeroKappaQuarticNoACEF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoACEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACEF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoACEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hAC, hAE, hAF, hBlt, hDlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoACEF810]
  compute_degree
  omega


theorem quarticCone_ACEF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACEF810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hAC, hAE, hAF, hBlt, hDlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hAC, hAE, hAF, hBlt, hDlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hAC, hAE, hAF, hBlt, hDlt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hAC, hAE, hAF, hBlt, hDlt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceACEF810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceACEF810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoACEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ACEF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hAC, hAE, hAF, hBlt, hDlt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceACFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoACFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_ACFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACFG810 A B C D E F G +
        degreeZeroKappaQuarticNoACFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceACFG810, degreeZeroKappaQuarticNoACFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoACFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoACFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hFpos, hGpos, hAC, hAF, hAG, hBlt, hDlt, hElt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaQuarticNoACFG810]
  compute_degree
  omega


theorem quarticCone_ACFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACFG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hFpos, hGpos, hAC, hAF, hAG, hBlt, hDlt, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hFpos, hGpos, hAC, hAF, hAG, hBlt, hDlt, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hFpos, hGpos, hAC, hAF, hAG, hBlt, hDlt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hFpos, hGpos, hAC, hAF, hAG, hBlt, hDlt, hElt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceACFG810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceACFG810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoACFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ACFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hFpos, hGpos, hAC, hAF, hAG, hBlt, hDlt, hElt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceADEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoADEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_ADEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceADEF810 A B C D E F G +
        degreeZeroKappaQuarticNoADEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceADEF810, degreeZeroKappaQuarticNoADEF810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoADEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADEF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoADEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hAD, hAE, hAF, hBlt, hClt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  simp only [degreeZeroKappaQuarticNoADEF810]
  compute_degree
  omega


theorem quarticCone_ADEF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADEF810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hAD, hAE, hAF, hBlt, hClt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hAD, hAE, hAF, hBlt, hClt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hAD, hAE, hAF, hBlt, hClt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hAD, hAE, hAF, hBlt, hClt, hGlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceADEF810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceADEF810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoADEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ADEF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hAD, hAE, hAF, hBlt, hClt, hGlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceADEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoADEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_ADEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceADEG810 A B C D E F G +
        degreeZeroKappaQuarticNoADEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceADEG810, degreeZeroKappaQuarticNoADEG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoADEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADEG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoADEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hEpos, hGpos, hAD, hAE, hAG, hBlt, hClt, hFlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroKappaQuarticNoADEG810]
  compute_degree
  omega


theorem quarticCone_ADEG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADEG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hGpos, hAD, hAE, hAG, hBlt, hClt, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hGpos, hAD, hAE, hAG, hBlt, hClt, hFlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hGpos, hAD, hAE, hAG, hBlt, hClt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hGpos, hAD, hAE, hAG, hBlt, hClt, hFlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceADEG810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceADEG810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoADEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ADEG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hEpos, hGpos, hAD, hAE, hAG, hBlt, hClt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def nuQuarticFaceADFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * G)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoADFG810
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
theorem degreeZeroNuQuartic810_eq_ADFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceADFG810 A B C D E F G +
        degreeZeroNuQuarticNoADFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceADFG810, degreeZeroNuQuarticNoADFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoADFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoADFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + G.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hFpos, hGpos, hAD, hAF, hAG, hBlt, hClt, hElt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroNuQuarticNoADFG810]
  compute_degree
  omega


theorem quarticCone_ADFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADFG810 A B C D E F G)
    (hdeg : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hFpos, hGpos, hAD, hAF, hAG, hBlt, hClt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hFpos, hGpos, hAD, hAF, hAG, hBlt, hClt, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hFpos, hGpos, hAD, hAF, hAG, hBlt, hClt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hFpos, hGpos, hAD, hAF, hAG, hBlt, hClt, hElt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (nuQuarticFaceADFG810 A B C D E F G).natDegree = D.natDegree + G.natDegree := by
    simp only [nuQuarticFaceADFG810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hGne]
  have hrest := degreeZeroNuQuarticNoADFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroNuQuartic810_eq_ADFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hFpos, hGpos, hAD, hAF, hAG, hBlt, hClt, hElt⟩
  omega


set_option maxHeartbeats 16000000 in
def muQuarticFaceAEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroMuQuarticNoAEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
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
theorem degreeZeroMuQuartic810_eq_AEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceAEFG810 A B C D E F G +
        degreeZeroMuQuarticNoAEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceAEFG810, degreeZeroMuQuarticNoAEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoAEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAEFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoAEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hApos, hEpos, hFpos, hGpos, hAE, hAF, hAG, hBlt, hClt, hDlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroMuQuarticNoAEFG810]
  compute_degree
  omega


theorem quarticCone_AEFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAEFG810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hFpos, hGpos, hAE, hAF, hAG, hBlt, hClt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hFpos, hGpos, hAE, hAF, hAG, hBlt, hClt, hDlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hFpos, hGpos, hAE, hAF, hAG, hBlt, hClt, hDlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hFpos, hGpos, hAE, hAF, hAG, hBlt, hClt, hDlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceAEFG810 A B C D E F G).natDegree = 2 * E.natDegree := by
    simp only [muQuarticFaceAEFG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoAEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_AEFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hEpos, hFpos, hGpos, hAE, hAF, hAG, hBlt, hClt, hDlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
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
theorem degreeZeroKappaQuartic810_eq_BEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoBEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBEFG810, degreeZeroKappaQuarticNoBEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      B.natDegree + G.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, hFpos, hGpos, hBE, hBF, hBG, hAlt, hClt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroKappaQuarticNoBEFG810]
  compute_degree
  omega


theorem quarticCone_BEFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBEFG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hFpos, hGpos, hBE, hBF, hBG, hAlt, hClt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hFpos, hGpos, hBE, hBF, hBG, hAlt, hClt, hDlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hFpos, hGpos, hBE, hBF, hBG, hAlt, hClt, hDlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hFpos, hGpos, hBE, hBF, hBG, hAlt, hClt, hDlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceBEFG810 A B C D E F G).natDegree = B.natDegree + G.natDegree := by
    simp only [kappaQuarticFaceBEFG810]
    rw [natDegree_smul _ hc, natDegree_mul hBne hGne]
  have hrest := degreeZeroKappaQuarticNoBEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_BEFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hEpos, hFpos, hGpos, hBE, hBF, hBG, hAlt, hClt, hDlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_CDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCDEG810 A B C D E F G +
        degreeZeroKappaQuarticNoCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceCDEG810, degreeZeroKappaQuarticNoCDEG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hGpos, hCD, hCE, hCG, hAlt, hBlt, hFlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hF1 : 4 * F.natDegree + 1 ≤ 7 * C.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroKappaQuarticNoCDEG810]
  compute_degree
  omega


theorem quarticCone_CDEG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hGpos, hCD, hCE, hCG, hAlt, hBlt, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hGpos, hCD, hCE, hCG, hAlt, hBlt, hFlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hGpos, hCD, hCE, hCG, hAlt, hBlt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hGpos, hCD, hCE, hCG, hAlt, hBlt, hFlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceCDEG810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceCDEG810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_CDEG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, hEpos, hGpos, hCD, hCE, hCG, hAlt, hBlt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_CDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCDFG810 A B C D E F G +
        degreeZeroKappaQuarticNoCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceCDFG810, degreeZeroKappaQuarticNoCDFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hFpos, hGpos, hCD, hCF, hCG, hAlt, hBlt, hElt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaQuarticNoCDFG810]
  compute_degree
  omega


theorem quarticCone_CDFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDFG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hFpos, hGpos, hCD, hCF, hCG, hAlt, hBlt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hFpos, hGpos, hCD, hCF, hCG, hAlt, hBlt, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hFpos, hGpos, hCD, hCF, hCG, hAlt, hBlt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hFpos, hGpos, hCD, hCF, hCG, hAlt, hBlt, hElt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceCDFG810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceCDFG810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_CDFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, hFpos, hGpos, hCD, hCF, hCG, hAlt, hBlt, hElt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_CEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceCEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceCEFG810, degreeZeroKappaQuarticNoCEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hCpos, hEpos, hFpos, hGpos, hCE, hCF, hCG, hAlt, hBlt, hDlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroKappaQuarticNoCEFG810]
  compute_degree
  omega


theorem quarticCone_CEFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCEFG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hFpos, hGpos, hCE, hCF, hCG, hAlt, hBlt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hFpos, hGpos, hCE, hCF, hCG, hAlt, hBlt, hDlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hFpos, hGpos, hCE, hCF, hCG, hAlt, hBlt, hDlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hFpos, hGpos, hCE, hCF, hCG, hAlt, hBlt, hDlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceCEFG810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceCEFG810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_CEFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hEpos, hFpos, hGpos, hCE, hCF, hCG, hAlt, hBlt, hDlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_DEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceDEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceDEFG810, degreeZeroKappaQuarticNoDEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hDpos, hEpos, hFpos, hGpos, hDE, hDF, hDG, hAlt, hBlt, hClt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroKappaQuarticNoDEFG810]
  compute_degree
  omega


theorem quarticCone_DEFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeDEFG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hFpos, hGpos, hDE, hDF, hDG, hAlt, hBlt, hClt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hFpos, hGpos, hDE, hDF, hDG, hAlt, hBlt, hClt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hFpos, hGpos, hDE, hDF, hDG, hAlt, hBlt, hClt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hFpos, hGpos, hDE, hDF, hDG, hAlt, hBlt, hClt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceDEFG810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceDEFG810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_DEFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hEpos, hFpos, hGpos, hDE, hDF, hDG, hAlt, hBlt, hClt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceACDEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoACDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_ACDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACDEG810 A B C D E F G +
        degreeZeroKappaQuarticNoACDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceACDEG810, degreeZeroKappaQuarticNoACDEG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoACDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoACDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hGpos, hAC, hAD, hAE, hAG, hBlt, hFlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroKappaQuarticNoACDEG810]
  compute_degree
  omega


theorem quarticCone_ACDEG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hGpos, hAC, hAD, hAE, hAG, hBlt, hFlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hGpos, hAC, hAD, hAE, hAG, hBlt, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hGpos, hAC, hAD, hAE, hAG, hBlt, hFlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hGpos, hAC, hAD, hAE, hAG, hBlt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hGpos, hAC, hAD, hAE, hAG, hBlt, hFlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceACDEG810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceACDEG810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoACDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ACDEG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hGpos, hAC, hAD, hAE, hAG, hBlt, hFlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceACDFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoACDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_ACDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACDFG810 A B C D E F G +
        degreeZeroKappaQuarticNoACDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceACDFG810, degreeZeroKappaQuarticNoACDFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoACDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoACDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hGpos, hAC, hAD, hAF, hAG, hBlt, hElt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaQuarticNoACDFG810]
  compute_degree
  omega


theorem quarticCone_ACDFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDFG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hGpos, hAC, hAD, hAF, hAG, hBlt, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hGpos, hAC, hAD, hAF, hAG, hBlt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hGpos, hAC, hAD, hAF, hAG, hBlt, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hGpos, hAC, hAD, hAF, hAG, hBlt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hGpos, hAC, hAD, hAF, hAG, hBlt, hElt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceACDFG810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceACDFG810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoACDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ACDFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hDpos, hFpos, hGpos, hAC, hAD, hAF, hAG, hBlt, hElt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceACEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoACEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
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
theorem degreeZeroKappaQuartic810_eq_ACEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoACEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceACEFG810, degreeZeroKappaQuarticNoACEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoACEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoACEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hGpos, hAC, hAE, hAF, hAG, hBlt, hDlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroKappaQuarticNoACEFG810]
  compute_degree
  omega


theorem quarticCone_ACEFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACEFG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hGpos, hAC, hAE, hAF, hAG, hBlt, hDlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hGpos, hAC, hAE, hAF, hAG, hBlt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hGpos, hAC, hAE, hAF, hAG, hBlt, hDlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hGpos, hAC, hAE, hAF, hAG, hBlt, hDlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hGpos, hAC, hAE, hAF, hAG, hBlt, hDlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceACEFG810 A B C D E F G).natDegree = C.natDegree + F.natDegree := by
    simp only [kappaQuarticFaceACEFG810]
    rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  have hrest := degreeZeroKappaQuarticNoACEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ACEFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hEpos, hFpos, hGpos, hAC, hAE, hAF, hAG, hBlt, hDlt⟩
  omega


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceADEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoADEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
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
theorem degreeZeroKappaQuartic810_eq_ADEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceADEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoADEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceADEFG810, degreeZeroKappaQuarticNoADEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoADEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoADEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hGpos, hAD, hAE, hAF, hAG, hBlt, hClt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  simp only [degreeZeroKappaQuarticNoADEFG810]
  compute_degree
  omega


theorem quarticCone_ADEFG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeADEFG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hGpos, hAD, hAE, hAF, hAG, hBlt, hClt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hGpos, hAD, hAE, hAF, hAG, hBlt, hClt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hGpos, hAD, hAE, hAF, hAG, hBlt, hClt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hGpos, hAD, hAE, hAF, hAG, hBlt, hClt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hGpos, hAD, hAE, hAF, hAG, hBlt, hClt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceADEFG810 A B C D E F G).natDegree = D.natDegree + E.natDegree := by
    simp only [kappaQuarticFaceADEFG810]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaQuarticNoADEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_ADEFG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hEpos, hFpos, hGpos, hAD, hAE, hAF, hAG, hBlt, hClt⟩
  omega

end QuarticKills810

end Max11DegreeRoutes
