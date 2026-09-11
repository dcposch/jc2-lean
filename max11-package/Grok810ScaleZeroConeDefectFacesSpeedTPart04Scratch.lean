import Grok810ScaleZeroConeDefectFacesSpeedTPart01Scratch

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section DefectGroups810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoF02G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(165 / 65536 : k) • A ^ 7
    + (1925 / 32768 : k) • (A ^ 4 * B ^ 2)
    + (385 / 16384 : k) • (A ^ 5 * C0)
    + (7245 / 524288 * l : k) • (A ^ 5 * B)
    - (35 / 1024 : k) • (A * B ^ 4)
    - (105 / 512 : k) • (A ^ 2 * B ^ 2 * C0)
    - (315 / 8192 * l : k) • (A ^ 2 * B ^ 3)
    - (35 / 512 : k) • (A ^ 3 * C0 ^ 2)
    - (525 / 4096 : k) • (A ^ 3 * B * D0)
    - (315 / 4096 * l : k) • (A ^ 3 * B * C0)
    - (245 / 8192 : k) • (A ^ 4 * E0)
    - (4725 / 262144 * l : k) • (A ^ 4 * D0)

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoF02G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (357 / 16384 * beta : k) • (A ^ 4 * B)
    + (9 / 1024 * gamma : k) • A ^ 5
    + (45 / 512 : k) • (B ^ 2 * C0 ^ 2)
    + (55 / 1024 : k) • (B ^ 3 * D0)
    + (63 / 2048 * l : k) • (B ^ 3 * C0)
    + (15 / 256 : k) • (A * C0 ^ 3)
    + (165 / 512 : k) • (A * B * C0 * D0)
    + (189 / 2048 * l : k) • (A * B * C0 ^ 2)
    + (75 / 512 : k) • (A * B ^ 2 * E0)
    + (693 / 8192 * l : k) • (A * B ^ 2 * D0)
    - (63 / 2048 * beta : k) • (A * B ^ 3)
    + (75 / 1024 : k) • (A ^ 2 * D0 ^ 2)

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoF02G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (75 / 512 : k) • (A ^ 2 * C0 * E0)
    + (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
    + (135 / 1024 : k) • (A ^ 2 * B * F0)
    + (315 / 4096 * l : k) • (A ^ 2 * B * E0)
    - (189 / 2048 * beta : k) • (A ^ 2 * B * C0)
    - (45 / 512 * gamma : k) • (A ^ 2 * B ^ 2)
    + (5 / 128 : k) • (A ^ 3 * G0)
    + (189 / 8192 * l : k) • (A ^ 3 * F0)
    - (231 / 8192 * beta : k) • (A ^ 3 * D0)
    - (15 / 256 * gamma : k) • (A ^ 3 * C0)
    - (165 / 2048 * delta : k) • (A ^ 3 * B)
    - (3 / 128 * epsilon : k) • A ^ 4

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoF02G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 128 : k) • (C0 * D0 ^ 2)
    - (15 / 128 : k) • (C0 ^ 2 * E0)
    - (63 / 1024 * l : k) • (C0 ^ 2 * D0)
    - (25 / 128 : k) • (B * D0 * E0)
    - (27 / 512 * l : k) • (B * D0 ^ 2)
    - (25 / 128 : k) • (B * C0 * F0)
    - (27 / 256 * l : k) • (B * C0 * E0)
    + (7 / 128 * beta : k) • (B * C0 ^ 2)
    - (5 / 64 : k) • (B ^ 2 * G0)
    - (45 / 1024 * l : k) • (B ^ 2 * F0)
    + (49 / 1024 * beta : k) • (B ^ 2 * D0)
    + (3 / 32 * gamma : k) • (B ^ 2 * C0)

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoF02G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (5 / 128 * delta : k) • B ^ 3
    - (5 / 64 : k) • (A * E0 ^ 2)
    - (5 / 32 : k) • (A * D0 * F0)
    - (45 / 512 * l : k) • (A * D0 * E0)
    - (5 / 32 : k) • (A * C0 * G0)
    - (45 / 512 * l : k) • (A * C0 * F0)
    + (49 / 512 * beta : k) • (A * C0 * D0)
    + (3 / 32 * gamma : k) • (A * C0 ^ 2)
    - (9 / 128 * l : k) • (A * B * G0)
    + (21 / 256 * beta : k) • (A * B * E0)
    + (21 / 128 * gamma : k) • (A * B * D0)
    + (15 / 64 * delta : k) • (A * B * C0)

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoF02G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (1 / 8 * epsilon : k) • (A * B ^ 2)
    + (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoF02G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(7 / 64 * beta : k) • (C0 * F0)
    - (3 / 16 * gamma : k) • (C0 * E0)
    - (15 / 64 * delta : k) • (C0 * D0)
    - (1 / 8 * epsilon : k) • C0 ^ 2
    - (3 / 32 * gamma : k) • (B * F0)
    - (5 / 32 * delta : k) • (B * E0)
    - (3 / 16 * epsilon : k) • (B * D0)
    - (3 / 16 * zeta : k) • (B * C0)
    - (1 / 16 * eta : k) • B ^ 2
    - (5 / 64 * delta : k) • (A * F0)
    - (1 / 8 * epsilon : k) • (A * E0)
    - (9 / 64 * zeta : k) • (A * D0)

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoF02G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoF02Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoF02Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroXiNoF02G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoF02G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiNoF02Polynomial810,
    degreeZeroXiNoF02G1,
    degreeZeroXiNoF02G2,
    degreeZeroXiNoF02G3,
    degreeZeroXiNoF02G4,
    degreeZeroXiNoF02G5,
    degreeZeroXiNoF02G6,
    degreeZeroXiNoF02G7,
    degreeZeroXiNoF02G8]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiNoF02G1` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoF02G1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoF02G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(165 / 65536) : k), (1925 / 32768 : k), (385 / 16384 : k),
      (7245 / 524288 * l : k), (-(35 / 1024) : k), (-(105 / 512) : k),
      (-(315 / 8192 * l) : k), (-(35 / 512) : k), (-(525 / 4096) : k),
      (-(315 / 4096 * l) : k), (-(245 / 8192) : k), (-(4725 / 262144 * l) : k)]
      [
      [7, 0, 0, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [5, 1, 0, 0, 0, 0, 0],
      [1, 4, 0, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0],
      [3, 1, 0, 1, 0, 0, 0], [3, 1, 1, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [4, 0, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroXiNoF02G1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoF02G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  rw [speedRefl_degreeZeroXiNoF02G1_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
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

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiNoF02G2` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoF02G2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoF02G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (357 / 16384 * beta : k), (9 / 1024 * gamma : k), (45 / 512 : k),
      (55 / 1024 : k), (63 / 2048 * l : k), (15 / 256 : k),
      (165 / 512 : k), (189 / 2048 * l : k), (75 / 512 : k),
      (693 / 8192 * l : k), (-(63 / 2048 * beta) : k), (75 / 1024 : k)]
      [
      [4, 1, 0, 0, 0, 0, 0], [5, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 3, 1, 0, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0],
      [1, 2, 0, 0, 1, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0]] := by
  simp only [degreeZeroXiNoF02G2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoF02G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  rw [speedRefl_degreeZeroXiNoF02G2_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
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

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiNoF02G3` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoF02G3_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoF02G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (75 / 512 : k), (693 / 8192 * l : k), (135 / 1024 : k),
      (315 / 4096 * l : k), (-(189 / 2048 * beta) : k), (-(45 / 512 * gamma) : k),
      (5 / 128 : k), (189 / 8192 * l : k), (-(231 / 8192 * beta) : k),
      (-(15 / 256 * gamma) : k), (-(165 / 2048 * delta) : k), (-(3 / 128 * epsilon) : k)]
      [
      [2, 0, 1, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [2, 1, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0],
      [2, 1, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroXiNoF02G3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoF02G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  rw [speedRefl_degreeZeroXiNoF02G3_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
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

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiNoF02G4` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoF02G4_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoF02G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(15 / 128) : k), (-(15 / 128) : k), (-(63 / 1024 * l) : k),
      (-(25 / 128) : k), (-(27 / 512 * l) : k), (-(25 / 128) : k),
      (-(27 / 256 * l) : k), (7 / 128 * beta : k), (-(5 / 64) : k),
      (-(45 / 1024 * l) : k), (49 / 1024 * beta : k), (3 / 32 * gamma : k)]
      [
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 1, 0], [0, 2, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0]] := by
  simp only [degreeZeroXiNoF02G4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoF02G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  rw [speedRefl_degreeZeroXiNoF02G4_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
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

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiNoF02G5` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoF02G5_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoF02G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (5 / 128 * delta : k), (-(5 / 64) : k), (-(5 / 32) : k),
      (-(45 / 512 * l) : k), (-(5 / 32) : k), (-(45 / 512 * l) : k),
      (49 / 512 * beta : k), (3 / 32 * gamma : k), (-(9 / 128 * l) : k),
      (21 / 256 * beta : k), (21 / 128 * gamma : k), (15 / 64 * delta : k)]
      [
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0],
      [1, 0, 1, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0], [1, 0, 1, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0],
      [1, 1, 0, 0, 0, 0, 1], [1, 1, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0]] := by
  simp only [degreeZeroXiNoF02G5, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoF02G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  rw [speedRefl_degreeZeroXiNoF02G5_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
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

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiNoF02G6` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoF02G6_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoF02G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (1 / 8 * epsilon : k), (35 / 1024 * beta : k), (9 / 128 * gamma : k),
      (105 / 1024 * delta : k), (1 / 8 * epsilon : k), (15 / 128 * zeta : k),
      (1 / 32 * eta : k), (5 / 16 : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 32 * gamma) : k)]
      [
      [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 0, 1, 0, 0], [2, 0, 0, 1, 0, 0, 0],
      [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1],
      [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]] := by
  simp only [degreeZeroXiNoF02G6, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoF02G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  rw [speedRefl_degreeZeroXiNoF02G6_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
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

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiNoF02G7` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoF02G7_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoF02G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k),
      (-(1 / 8 * epsilon) : k), (-(3 / 32 * gamma) : k), (-(5 / 32 * delta) : k),
      (-(3 / 16 * epsilon) : k), (-(3 / 16 * zeta) : k), (-(1 / 16 * eta) : k),
      (-(5 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(9 / 64 * zeta) : k)]
      [
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroXiNoF02G7, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoF02G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  rw [speedRefl_degreeZeroXiNoF02G7_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
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

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiNoF02G8` (6 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoF02G8_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoF02G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(1 / 8 * eta) : k), (-(1 / 16 * theta) : k), (1 / 2 * epsilon : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0],
      [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroXiNoF02G8, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoF02G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rcases hcone with ⟨hFpos, hA, hB, hC, hD, hE, hG⟩
  rw [speedRefl_degreeZeroXiNoF02G8_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
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

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoF02Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : F0LeadsXiCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoF02Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * F0.natDegree := by
  rw [degreeZeroXiNoF02Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroXiNoF02G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoF02G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

end DefectGroups810


#print axioms degreeZeroXiNoF02G1.eq_1
#print axioms degreeZeroXiNoF02G2.eq_1
#print axioms degreeZeroXiNoF02G3.eq_1
#print axioms degreeZeroXiNoF02G4.eq_1
#print axioms degreeZeroXiNoF02G5.eq_1
#print axioms degreeZeroXiNoF02G6.eq_1
#print axioms degreeZeroXiNoF02G7.eq_1
#print axioms degreeZeroXiNoF02G8.eq_1

end Max11DegreeRoutes
