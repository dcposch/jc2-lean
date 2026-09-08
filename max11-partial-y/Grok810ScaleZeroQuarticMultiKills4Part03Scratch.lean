import Grok810ScaleZeroQuarticMultiKills4Part02Scratch

/-! # Part 3 of `Grok810ScaleZeroQuarticMultiKills4Scratch`.

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

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoABDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDEF810 A B C D E F G) :
    (degreeZeroNuQuarticNoABDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroNuQuarticNoABDEF810_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
    Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    mul_one, one_mul, and_true, true_and, natDegree_zero]
  repeat' apply And.intro
  all_goals first
    | (right; right; omega)
    | (left; norm_num; done)
    | (right; left; simp; done)
    | trivial

theorem nuQuarticFaceABDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (nuQuarticFaceABDEF810 A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 4096 : k) * nuQuarticInnerABDEF810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
  simp only [nuQuarticFaceABDEF810, nuQuarticInnerABDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2D : ((A * B ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ADE : ((A * D * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    omega
  have hcf_ADE : ((A * D * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ADE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B2F : ((B ^ 2 * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hFne, natDegree_pow]
    omega
  have hcf_B2F : ((B ^ 2 * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_EF : ((E * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A2B3, hcf_AB2D, hcf_ADE, hcf_B2F, hcf_BD2, hcf_EF]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceABDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * D * E)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoABDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (A * B * C * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
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
theorem degreeZeroXiQuartic810_eq_ABDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceABDEF810 A B C D E F G +
        degreeZeroXiQuarticNoABDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceABDEF810, degreeZeroXiQuarticNoABDEF810]
  all_goals module

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroXiQuarticNoABDEF810` (55 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiQuarticNoABDEF810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroXiQuarticNoABDEF810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 256 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (-(45 / 262144 * l) : k), (9 / 16384 * l : k),
      (-(9 / 16384 * l) : k), (-(9 / 8192 * l) : k), (9 / 4096 * l : k),
      (-(9 / 8192 * l) : k), (171 / 8192 * l : k), (9 / 1024 * l : k),
      (63 / 2048 * l : k), (-(9 / 512 * l) : k), (-(9 / 512 * l) : k),
      (-(45 / 1024 * l) : k), (-(27 / 256 * l) : k), (-(27 / 512 * l) : k),
      (-(63 / 1024 * l) : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (-(7 / 8192 * beta) : k), (7 / 2048 * beta : k), (-(7 / 1024 * beta) : k),
      (-(7 / 1024 * beta) : k), (7 / 256 * beta : k), (7 / 512 * beta : k),
      (49 / 1024 * beta : k), (7 / 128 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (3 / 64 * gamma : k), (3 / 32 * gamma : k),
      (-(3 / 32 * gamma) : k), (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k),
      (-(5 / 1024 * delta) : k), (5 / 128 * delta : k), (5 / 128 * delta : k),
      (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k), (-(15 / 64 * delta) : k),
      (1 / 32 * epsilon : k), (-(3 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k),
      (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k), (-(3 / 16 * zeta) : k),
      (3 / 8 * zeta : k), (-(1 / 16 * eta) : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [1, 1, 1, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [4, 0, 0, 1, 0, 0, 0],
      [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0],
      [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0],
      [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0],
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroXiQuarticNoABDEF810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoABDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDEF810 A B C D E F G) :
    (degreeZeroXiQuarticNoABDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroXiQuarticNoABDEF810_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
    Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    mul_one, one_mul, and_true, true_and, natDegree_zero]
  repeat' apply And.intro
  all_goals first
    | (right; right; omega)
    | (left; norm_num; done)
    | (right; left; simp; done)
    | trivial

theorem xiQuarticFaceABDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (xiQuarticFaceABDEF810 A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) =
      (1 / 2048 : k) * xiQuarticInnerABDEF810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
  simp only [xiQuarticFaceABDEF810, xiQuarticInnerABDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB4 : ((A * B ^ 4)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 4 hBne), natDegree_pow]
  have hcf_AB4 : ((A * B ^ 4)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 4 := by
    rw [← hdeg_AB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ADF : ((A * D * F)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    omega
  have hcf_ADF : ((A * D * F)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ADF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
    omega
  have hcf_B3D : ((B ^ 3 * D)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDE : ((B * D * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hEne, natDegree_mul hBne hDne]
    omega
  have hcf_BDE : ((B * D * E)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_F2 : (F ^ 2).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (A.natDegree + 4 * B.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB4, hcf_AB2E, hcf_ADF, hcf_B3D, hcf_BDE, hcf_F2]
  ring

end QuarticKills810

end Max11DegreeRoutes
