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
def degreeZeroOmicronNoD03G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(12705 / 1048576 : k) • (A ^ 6 * B)
    - (34155 / 33554432 * l : k) • A ^ 7
    + (3745 / 65536 : k) • (A ^ 3 * B ^ 3)
    + (1365 / 16384 : k) • (A ^ 4 * B * C0)
    + (103005 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
    + (525 / 32768 : k) • (A ^ 5 * D0)
    + (19845 / 2097152 * l : k) • (A ^ 5 * C0)
    - (3927 / 2097152 * beta : k) • A ^ 6
    - (21 / 4096 : k) • B ^ 5
    - (105 / 1024 : k) • (A * B ^ 3 * C0)
    - (945 / 65536 * l : k) • (A * B ^ 4)
    - (2475 / 16384 : k) • (A ^ 2 * B * C0 ^ 2)
    - (2475 / 16384 : k) • (A ^ 2 * B ^ 2 * D0)
    - (11151 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C0)
    - (795 / 8192 : k) • (A ^ 3 * C0 * D0)

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronNoD03G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(3591 / 131072 * l : k) • (A ^ 3 * C0 ^ 2)
    - (725 / 8192 : k) • (A ^ 3 * B * E0)
    - (3591 / 65536 * l : k) • (A ^ 3 * B * D0)
    + (4095 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
    - (305 / 16384 : k) • (A ^ 4 * F0)
    - (3087 / 262144 * l : k) • (A ^ 4 * E0)
    + (1953 / 131072 * beta : k) • (A ^ 4 * C0)
    + (495 / 16384 * gamma : k) • (A ^ 4 * B)
    + (1089 / 131072 * delta : k) • A ^ 5
    + (45 / 1024 : k) • (B * C0 ^ 3)
    + (135 / 1024 : k) • (B ^ 2 * C0 * D0)
    + (567 / 16384 * l : k) • (B ^ 2 * C0 ^ 2)
    + (5 / 128 : k) • (B ^ 3 * E0)
    + (189 / 8192 * l : k) • (B ^ 3 * D0)
    - (189 / 32768 * beta : k) • B ^ 4

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronNoD03G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (135 / 1024 : k) • (A * C0 ^ 2 * D0)
    + (189 / 8192 * l : k) • (A * C0 ^ 3)
    + (135 / 1024 : k) • (A * B * D0 ^ 2)
    + (15 / 64 : k) • (A * B * C0 * E0)
    + (567 / 4096 * l : k) • (A * B * C0 * D0)
    + (105 / 1024 : k) • (A * B ^ 2 * F0)
    + (63 / 1024 * l : k) • (A * B ^ 2 * E0)
    - (567 / 8192 * beta : k) • (A * B ^ 2 * C0)
    - (45 / 1024 * gamma : k) • (A * B ^ 3)
    + (225 / 2048 : k) • (A ^ 2 * D0 * E0)
    + (135 / 4096 * l : k) • (A ^ 2 * D0 ^ 2)
    + (195 / 2048 : k) • (A ^ 2 * C0 * F0)
    + (477 / 8192 * l : k) • (A ^ 2 * C0 * E0)
    - (273 / 8192 * beta : k) • (A ^ 2 * C0 ^ 2)
    + (165 / 2048 : k) • (A ^ 2 * B * G0)

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronNoD03G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (207 / 4096 * l : k) • (A ^ 2 * B * F0)
    - (273 / 4096 * beta : k) • (A ^ 2 * B * D0)
    - (261 / 2048 * gamma : k) • (A ^ 2 * B * C0)
    - (45 / 512 * delta : k) • (A ^ 2 * B ^ 2)
    + (99 / 8192 * l : k) • (A ^ 3 * G0)
    - (147 / 8192 * beta : k) • (A ^ 3 * E0)
    - (81 / 2048 * gamma : k) • (A ^ 3 * D0)
    - (225 / 4096 * delta : k) • (A ^ 3 * C0)
    - (33 / 512 * epsilon : k) • (A ^ 3 * B)
    - (495 / 32768 * zeta : k) • A ^ 4
    - (25 / 128 : k) • (C0 * D0 * E0)
    - (27 / 512 * l : k) • (C0 * D0 ^ 2)
    - (5 / 64 : k) • (C0 ^ 2 * F0)
    - (45 / 1024 * l : k) • (C0 ^ 2 * E0)
    + (7 / 512 * beta : k) • C0 ^ 3

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronNoD03G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(5 / 64 : k) • (B * E0 ^ 2)
    - (5 / 32 : k) • (B * D0 * F0)
    - (45 / 512 * l : k) • (B * D0 * E0)
    - (15 / 128 : k) • (B * C0 * G0)
    - (9 / 128 * l : k) • (B * C0 * F0)
    + (21 / 256 * beta : k) • (B * C0 * D0)
    + (9 / 128 * gamma : k) • (B * C0 ^ 2)
    - (27 / 1024 * l : k) • (B ^ 2 * G0)
    + (35 / 1024 * beta : k) • (B ^ 2 * E0)
    + (9 / 128 * gamma : k) • (B ^ 2 * D0)
    + (45 / 512 * delta : k) • (B ^ 2 * C0)
    + (1 / 32 * epsilon : k) • B ^ 3
    - (15 / 128 : k) • (A * E0 * F0)
    - (9 / 256 * l : k) • (A * E0 ^ 2)
    - (15 / 128 : k) • (A * D0 * G0)

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronNoD03G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(9 / 128 * l : k) • (A * D0 * F0)
    + (21 / 512 * beta : k) • (A * D0 ^ 2)
    - (27 / 512 * l : k) • (A * C0 * G0)
    + (35 / 512 * beta : k) • (A * C0 * E0)
    + (9 / 64 * gamma : k) • (A * C0 * D0)
    + (45 / 512 * delta : k) • (A * C0 ^ 2)
    + (7 / 128 * beta : k) • (A * B * F0)
    + (15 / 128 * gamma : k) • (A * B * E0)
    + (45 / 256 * delta : k) • (A * B * D0)
    + (3 / 16 * epsilon : k) • (A * B * C0)
    + (45 / 512 * zeta : k) • (A * B ^ 2)
    + (15 / 512 * gamma : k) • (A ^ 2 * F0)
    + (15 / 256 * delta : k) • (A ^ 2 * E0)
    + (21 / 256 * epsilon : k) • (A ^ 2 * D0)
    + (81 / 1024 * zeta : k) • (A ^ 2 * C0)

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronNoD03G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (33 / 512 * eta : k) • (A ^ 2 * B)
    + (11 / 1024 * theta : k) • A ^ 3
    + (5 / 16 : k) • (F0 * G0)
    + (9 / 128 * l : k) • F0 ^ 2
    + (9 / 64 * l : k) • (E0 * G0)
    - (7 / 128 * beta : k) • E0 ^ 2
    - (7 / 64 * beta : k) • (D0 * F0)
    - (3 / 16 * gamma : k) • (D0 * E0)
    - (15 / 128 * delta : k) • D0 ^ 2
    - (3 / 32 * gamma : k) • (C0 * F0)
    - (5 / 32 * delta : k) • (C0 * E0)
    - (3 / 16 * epsilon : k) • (C0 * D0)
    - (9 / 128 * zeta : k) • C0 ^ 2
    - (5 / 64 * delta : k) • (B * F0)
    - (1 / 8 * epsilon : k) • (B * E0)

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronNoD03G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(9 / 64 * zeta : k) • (B * D0)
    - (3 / 32 * eta : k) • (B * C0)
    - (3 / 128 * theta : k) • B ^ 2
    - (1 / 16 * epsilon : k) • (A * F0)
    - (3 / 32 * zeta : k) • (A * E0)
    - (3 / 32 * eta : k) • (A * D0)
    - (3 / 64 * theta : k) • (A * C0)
    + (3 / 8 * zeta : k) • G0
    + (1 / 4 * eta : k) • F0
    + (1 / 8 * theta : k) • E0

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoD03Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoD03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroOmicronNoD03G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoD03G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroOmicronNoD03Polynomial810,
    degreeZeroOmicronNoD03G1,
    degreeZeroOmicronNoD03G2,
    degreeZeroOmicronNoD03G3,
    degreeZeroOmicronNoD03G4,
    degreeZeroOmicronNoD03G5,
    degreeZeroOmicronNoD03G6,
    degreeZeroOmicronNoD03G7,
    degreeZeroOmicronNoD03G8]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroOmicronNoD03G1` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoD03G1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoD03G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(12705 / 1048576) : k), (-(34155 / 33554432 * l) : k), (3745 / 65536 : k),
      (1365 / 16384 : k), (103005 / 4194304 * l : k), (525 / 32768 : k),
      (19845 / 2097152 * l : k), (-(3927 / 2097152 * beta) : k), (-(21 / 4096) : k),
      (-(105 / 1024) : k), (-(945 / 65536 * l) : k), (-(2475 / 16384) : k),
      (-(2475 / 16384) : k), (-(11151 / 131072 * l) : k), (-(795 / 8192) : k)]
      [
      [6, 1, 0, 0, 0, 0, 0], [7, 0, 0, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0], [4, 1, 1, 0, 0, 0, 0],
      [4, 2, 0, 0, 0, 0, 0], [5, 0, 0, 1, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [6, 0, 0, 0, 0, 0, 0],
      [0, 5, 0, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0],
      [2, 2, 0, 1, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [3, 0, 1, 1, 0, 0, 0]] := by
  simp only [degreeZeroOmicronNoD03G1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoD03G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroOmicronNoD03G1_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoD03G2` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoD03G2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoD03G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(3591 / 131072 * l) : k), (-(725 / 8192) : k), (-(3591 / 65536 * l) : k),
      (4095 / 131072 * beta : k), (-(305 / 16384) : k), (-(3087 / 262144 * l) : k),
      (1953 / 131072 * beta : k), (495 / 16384 * gamma : k), (1089 / 131072 * delta : k),
      (45 / 1024 : k), (135 / 1024 : k), (567 / 16384 * l : k),
      (5 / 128 : k), (189 / 8192 * l : k), (-(189 / 32768 * beta) : k)]
      [
      [3, 0, 2, 0, 0, 0, 0], [3, 1, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0],
      [4, 0, 0, 0, 0, 1, 0], [4, 0, 0, 0, 1, 0, 0], [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0],
      [5, 0, 0, 0, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [0, 3, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroOmicronNoD03G2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoD03G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroOmicronNoD03G2_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoD03G3` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoD03G3_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoD03G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (135 / 1024 : k), (189 / 8192 * l : k), (135 / 1024 : k),
      (15 / 64 : k), (567 / 4096 * l : k), (105 / 1024 : k),
      (63 / 1024 * l : k), (-(567 / 8192 * beta) : k), (-(45 / 1024 * gamma) : k),
      (225 / 2048 : k), (135 / 4096 * l : k), (195 / 2048 : k),
      (477 / 8192 * l : k), (-(273 / 8192 * beta) : k), (165 / 2048 : k)]
      [
      [1, 0, 2, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 1, 1, 0, 1, 0, 0],
      [1, 1, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 2, 0, 0, 1, 0, 0], [1, 2, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 1, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0],
      [2, 0, 1, 0, 1, 0, 0], [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 1]] := by
  simp only [degreeZeroOmicronNoD03G3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoD03G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroOmicronNoD03G3_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoD03G4` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoD03G4_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoD03G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (207 / 4096 * l : k), (-(273 / 4096 * beta) : k), (-(261 / 2048 * gamma) : k),
      (-(45 / 512 * delta) : k), (99 / 8192 * l : k), (-(147 / 8192 * beta) : k),
      (-(81 / 2048 * gamma) : k), (-(225 / 4096 * delta) : k), (-(33 / 512 * epsilon) : k),
      (-(495 / 32768 * zeta) : k), (-(25 / 128) : k), (-(27 / 512 * l) : k),
      (-(5 / 64) : k), (-(45 / 1024 * l) : k), (7 / 512 * beta : k)]
      [
      [2, 1, 0, 0, 0, 1, 0], [2, 1, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 0, 0], [3, 0, 0, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0],
      [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0]] := by
  simp only [degreeZeroOmicronNoD03G4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoD03G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroOmicronNoD03G4_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoD03G5` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoD03G5_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoD03G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(5 / 64) : k), (-(5 / 32) : k), (-(45 / 512 * l) : k),
      (-(15 / 128) : k), (-(9 / 128 * l) : k), (21 / 256 * beta : k),
      (9 / 128 * gamma : k), (-(27 / 1024 * l) : k), (35 / 1024 * beta : k),
      (9 / 128 * gamma : k), (45 / 512 * delta : k), (1 / 32 * epsilon : k),
      (-(15 / 128) : k), (-(9 / 256 * l) : k), (-(15 / 128) : k)]
      [
      [0, 1, 0, 0, 2, 0, 0], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 1, 1, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1],
      [0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 1, 0], [1, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 1]] := by
  simp only [degreeZeroOmicronNoD03G5, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoD03G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroOmicronNoD03G5_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoD03G6` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoD03G6_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoD03G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(9 / 128 * l) : k), (21 / 512 * beta : k), (-(27 / 512 * l) : k),
      (35 / 512 * beta : k), (9 / 64 * gamma : k), (45 / 512 * delta : k),
      (7 / 128 * beta : k), (15 / 128 * gamma : k), (45 / 256 * delta : k),
      (3 / 16 * epsilon : k), (45 / 512 * zeta : k), (15 / 512 * gamma : k),
      (15 / 256 * delta : k), (21 / 256 * epsilon : k), (81 / 1024 * zeta : k)]
      [
      [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 1, 0, 1, 0, 0],
      [1, 0, 1, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [2, 0, 0, 0, 1, 0, 0], [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0]] := by
  simp only [degreeZeroOmicronNoD03G6, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoD03G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroOmicronNoD03G6_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoD03G7` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoD03G7_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoD03G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (33 / 512 * eta : k), (11 / 1024 * theta : k), (5 / 16 : k),
      (9 / 128 * l : k), (9 / 64 * l : k), (-(7 / 128 * beta) : k),
      (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k), (-(15 / 128 * delta) : k),
      (-(3 / 32 * gamma) : k), (-(5 / 32 * delta) : k), (-(3 / 16 * epsilon) : k),
      (-(9 / 128 * zeta) : k), (-(5 / 64 * delta) : k), (-(1 / 8 * epsilon) : k)]
      [
      [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 2, 0],
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0]] := by
  simp only [degreeZeroOmicronNoD03G7, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoD03G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroOmicronNoD03G7_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoD03G8` (10 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoD03G8_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoD03G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(9 / 64 * zeta) : k), (-(3 / 32 * eta) : k), (-(3 / 128 * theta) : k),
      (-(1 / 16 * epsilon) : k), (-(3 / 32 * zeta) : k), (-(3 / 32 * eta) : k),
      (-(3 / 64 * theta) : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0]] := by
  simp only [degreeZeroOmicronNoD03G8, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoD03G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rcases hcone with ⟨⟨hDpos, hA, hB, hC, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroOmicronNoD03G8_eq_polyOf]
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
theorem degreeZeroOmicronNoD03Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoD03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * D0.natDegree := by
  rw [degreeZeroOmicronNoD03Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroOmicronNoD03G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoD03G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

end DefectGroups810


#print axioms degreeZeroOmicronNoD03G1.eq_1
#print axioms degreeZeroOmicronNoD03G2.eq_1
#print axioms degreeZeroOmicronNoD03G3.eq_1
#print axioms degreeZeroOmicronNoD03G4.eq_1
#print axioms degreeZeroOmicronNoD03G5.eq_1
#print axioms degreeZeroOmicronNoD03G6.eq_1
#print axioms degreeZeroOmicronNoD03G7.eq_1
#print axioms degreeZeroOmicronNoD03G8.eq_1

end Max11DegreeRoutes
