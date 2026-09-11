import Grok810ScaleZeroConeDefectFacesSpeedTPart01Scratch

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Splittings -/

section DefectSplittings810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiPolynomial810_eq_A7_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (-(165 / 65536 : k)) • A ^ 7 +
        degreeZeroXiNoA7Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiPolynomial810, degreeZeroXiNoA7Polynomial810]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiPolynomial810_eq_F02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (5 / 32 : k) • F0 ^ 2 +
        degreeZeroXiNoF02Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiPolynomial810, degreeZeroXiNoF02Polynomial810]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial810_eq_B4_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (35 / 2048 : k) • B ^ 4 +
        degreeZeroMuNoB4Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuNoB4Polynomial810]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial810_eq_C03_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (-(5 / 128 : k)) • C0 ^ 3 +
        degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuNoC03Polynomial810]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuPolynomial810_eq_E02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      (5 / 32 : k) • E0 ^ 2 +
        degreeZeroMuNoE02Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuPolynomial810, degreeZeroMuNoE02Polynomial810]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronPolynomial810_eq_B5_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      (-(21 / 4096 : k)) • B ^ 5 +
        degreeZeroOmicronNoB5Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroOmicronPolynomial810,
    degreeZeroOmicronNoB5Polynomial810]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronPolynomial810_eq_D03_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0 =
      (-(5 / 128 : k)) • D0 ^ 3 +
        degreeZeroOmicronNoD03Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroOmicronPolynomial810,
    degreeZeroOmicronNoD03Polynomial810]
  simp only [neg_smul]
  abel

end DefectSplittings810




end Max11DegreeRoutes
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
def degreeZeroXiNoA7G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (1925 / 32768 : k) • (A ^ 4 * B ^ 2)
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
    + (357 / 16384 * beta : k) • (A ^ 4 * B)

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoA7G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (9 / 1024 * gamma : k) • A ^ 5
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
    + (75 / 512 : k) • (A ^ 2 * C0 * E0)

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoA7G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (693 / 8192 * l : k) • (A ^ 2 * C0 * D0)
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
    - (15 / 128 : k) • (C0 * D0 ^ 2)

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoA7G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 128 : k) • (C0 ^ 2 * E0)
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
    + (5 / 128 * delta : k) • B ^ 3

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoA7G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(5 / 64 : k) • (A * E0 ^ 2)
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
    + (1 / 8 * epsilon : k) • (A * B ^ 2)

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoA7G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (35 / 1024 * beta : k) • (A ^ 2 * F0)
    + (9 / 128 * gamma : k) • (A ^ 2 * E0)
    + (105 / 1024 * delta : k) • (A ^ 2 * D0)
    + (1 / 8 * epsilon : k) • (A ^ 2 * C0)
    + (15 / 128 * zeta : k) • (A ^ 2 * B)
    + (1 / 32 * eta : k) • A ^ 3
    + (5 / 32 : k) • F0 ^ 2
    + (5 / 16 : k) • (E0 * G0)
    + (9 / 64 * l : k) • (E0 * F0)
    + (9 / 64 * l : k) • (D0 * G0)
    - (7 / 64 * beta : k) • (D0 * E0)
    - (3 / 32 * gamma : k) • D0 ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroXiNoA7G7
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
def degreeZeroXiNoA7G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(1 / 8 * eta : k) • (A * C0)
    - (1 / 16 * theta : k) • (A * B)
    + (1 / 2 * epsilon : k) • G0
    + (3 / 8 * zeta : k) • F0
    + (1 / 4 * eta : k) • E0
    + (1 / 8 * theta : k) • D0

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoA7Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoA7Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroXiNoA7G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroXiNoA7G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroXiNoA7Polynomial810,
    degreeZeroXiNoA7G1,
    degreeZeroXiNoA7G2,
    degreeZeroXiNoA7G3,
    degreeZeroXiNoA7G4,
    degreeZeroXiNoA7G5,
    degreeZeroXiNoA7G6,
    degreeZeroXiNoA7G7,
    degreeZeroXiNoA7G8]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiNoA7G1` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoA7G1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoA7G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (1925 / 32768 : k), (385 / 16384 : k), (7245 / 524288 * l : k),
      (-(35 / 1024) : k), (-(105 / 512) : k), (-(315 / 8192 * l) : k),
      (-(35 / 512) : k), (-(525 / 4096) : k), (-(315 / 4096 * l) : k),
      (-(245 / 8192) : k), (-(4725 / 262144 * l) : k), (357 / 16384 * beta : k)]
      [
      [4, 2, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [5, 1, 0, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0],
      [2, 2, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0], [3, 1, 0, 1, 0, 0, 0],
      [3, 1, 1, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [4, 0, 0, 1, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroXiNoA7G1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoA7G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  rw [speedRefl_degreeZeroXiNoA7G1_eq_polyOf]
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
/-- Reflected form of `degreeZeroXiNoA7G2` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoA7G2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoA7G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (9 / 1024 * gamma : k), (45 / 512 : k), (55 / 1024 : k),
      (63 / 2048 * l : k), (15 / 256 : k), (165 / 512 : k),
      (189 / 2048 * l : k), (75 / 512 : k), (693 / 8192 * l : k),
      (-(63 / 2048 * beta) : k), (75 / 1024 : k), (75 / 512 : k)]
      [
      [5, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 0, 3, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0],
      [1, 2, 0, 1, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0], [2, 0, 1, 0, 1, 0, 0]] := by
  simp only [degreeZeroXiNoA7G2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoA7G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  rw [speedRefl_degreeZeroXiNoA7G2_eq_polyOf]
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
/-- Reflected form of `degreeZeroXiNoA7G3` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoA7G3_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoA7G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (693 / 8192 * l : k), (135 / 1024 : k), (315 / 4096 * l : k),
      (-(189 / 2048 * beta) : k), (-(45 / 512 * gamma) : k), (5 / 128 : k),
      (189 / 8192 * l : k), (-(231 / 8192 * beta) : k), (-(15 / 256 * gamma) : k),
      (-(165 / 2048 * delta) : k), (-(3 / 128 * epsilon) : k), (-(15 / 128) : k)]
      [
      [2, 0, 1, 1, 0, 0, 0], [2, 1, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [2, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0], [3, 0, 0, 1, 0, 0, 0],
      [3, 0, 1, 0, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0]] := by
  simp only [degreeZeroXiNoA7G3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoA7G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  rw [speedRefl_degreeZeroXiNoA7G3_eq_polyOf]
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
/-- Reflected form of `degreeZeroXiNoA7G4` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoA7G4_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoA7G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(15 / 128) : k), (-(63 / 1024 * l) : k), (-(25 / 128) : k),
      (-(27 / 512 * l) : k), (-(25 / 128) : k), (-(27 / 256 * l) : k),
      (7 / 128 * beta : k), (-(5 / 64) : k), (-(45 / 1024 * l) : k),
      (49 / 1024 * beta : k), (3 / 32 * gamma : k), (5 / 128 * delta : k)]
      [
      [0, 0, 2, 0, 1, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1],
      [0, 2, 0, 0, 0, 1, 0], [0, 2, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroXiNoA7G4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoA7G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  rw [speedRefl_degreeZeroXiNoA7G4_eq_polyOf]
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
/-- Reflected form of `degreeZeroXiNoA7G5` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoA7G5_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoA7G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(5 / 64) : k), (-(5 / 32) : k), (-(45 / 512 * l) : k),
      (-(5 / 32) : k), (-(45 / 512 * l) : k), (49 / 512 * beta : k),
      (3 / 32 * gamma : k), (-(9 / 128 * l) : k), (21 / 256 * beta : k),
      (21 / 128 * gamma : k), (15 / 64 * delta : k), (1 / 8 * epsilon : k)]
      [
      [1, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [1, 0, 1, 0, 0, 0, 1],
      [1, 0, 1, 0, 0, 1, 0], [1, 0, 1, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 1],
      [1, 1, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroXiNoA7G5, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoA7G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  rw [speedRefl_degreeZeroXiNoA7G5_eq_polyOf]
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
/-- Reflected form of `degreeZeroXiNoA7G6` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoA7G6_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoA7G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (35 / 1024 * beta : k), (9 / 128 * gamma : k), (105 / 1024 * delta : k),
      (1 / 8 * epsilon : k), (15 / 128 * zeta : k), (1 / 32 * eta : k),
      (5 / 32 : k), (5 / 16 : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 32 * gamma) : k)]
      [
      [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 0, 1, 0, 0], [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0],
      [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 0, 1],
      [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]] := by
  simp only [degreeZeroXiNoA7G6, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoA7G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  rw [speedRefl_degreeZeroXiNoA7G6_eq_polyOf]
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
/-- Reflected form of `degreeZeroXiNoA7G7` (12 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoA7G7_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoA7G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
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
  simp only [degreeZeroXiNoA7G7, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoA7G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  rw [speedRefl_degreeZeroXiNoA7G7_eq_polyOf]
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
/-- Reflected form of `degreeZeroXiNoA7G8` (6 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiNoA7G8_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiNoA7G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(1 / 8 * eta) : k), (-(1 / 16 * theta) : k), (1 / 2 * epsilon : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0],
      [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroXiNoA7G8, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoA7G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE, hF, hG⟩
  rw [speedRefl_degreeZeroXiNoA7G8_eq_polyOf]
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
theorem degreeZeroXiNoA7Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AMaximalCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoA7Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rw [degreeZeroXiNoA7Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroXiNoA7G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroXiNoA7G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

end DefectGroups810


#print axioms degreeZeroXiNoA7G1.eq_1
#print axioms degreeZeroXiNoA7G2.eq_1
#print axioms degreeZeroXiNoA7G3.eq_1
#print axioms degreeZeroXiNoA7G4.eq_1
#print axioms degreeZeroXiNoA7G5.eq_1
#print axioms degreeZeroXiNoA7G6.eq_1
#print axioms degreeZeroXiNoA7G7.eq_1
#print axioms degreeZeroXiNoA7G8.eq_1

end Max11DegreeRoutes
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
def degreeZeroMuNoB4G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6
    - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)
    + (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoB4G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4
    - (5 / 128 : k) • C0 ^ 3

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoB4G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoB4G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoB4G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 32 : k) • E0 ^ 2
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoB4G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoB4G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoB4G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoB4Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoB4Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroMuNoB4G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoB4G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuNoB4Polynomial810,
    degreeZeroMuNoB4G1,
    degreeZeroMuNoB4G2,
    degreeZeroMuNoB4G3,
    degreeZeroMuNoB4G4,
    degreeZeroMuNoB4G5,
    degreeZeroMuNoB4G6,
    degreeZeroMuNoB4G7,
    degreeZeroMuNoB4G8]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuNoB4G1` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoB4G1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoB4G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (385 / 65536 : k), (-(385 / 4096) : k), (-(385 / 8192) : k),
      (-(7245 / 262144 * l) : k), (105 / 512 : k), (315 / 8192 * l : k),
      (105 / 1024 : k)]
      [
      [6, 0, 0, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0],
      [1, 2, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoB4G1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoB4G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroMuNoB4G1_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoB4G2` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoB4G2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoB4G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (105 / 512 : k), (945 / 8192 * l : k), (35 / 512 : k),
      (315 / 8192 * l : k), (-(357 / 8192 * beta) : k), (-(45 / 2048 * gamma) : k),
      (-(5 / 128) : k)]
      [
      [2, 1, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [3, 0, 0, 1, 0, 0, 0],
      [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoB4G2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoB4G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroMuNoB4G2_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoB4G3` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoB4G3_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoB4G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(15 / 64) : k), (-(63 / 1024 * l) : k), (-(15 / 128) : k),
      (-(63 / 1024 * l) : k), (21 / 1024 * beta : k), (-(15 / 128) : k),
      (-(15 / 64) : k)]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0]] := by
  simp only [degreeZeroMuNoB4G3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoB4G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroMuNoB4G3_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoB4G4` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoB4G4_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoB4G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(63 / 512 * l) : k), (-(15 / 64) : k), (-(63 / 512 * l) : k),
      (63 / 512 * beta : k), (15 / 128 * gamma : k), (-(15 / 128) : k),
      (-(63 / 1024 * l) : k)]
      [
      [1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 1, 0]] := by
  simp only [degreeZeroMuNoB4G4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoB4G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroMuNoB4G4_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoB4G5` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoB4G5_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoB4G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (63 / 1024 * beta : k), (15 / 128 * gamma : k), (165 / 1024 * delta : k),
      (1 / 16 * epsilon : k), (5 / 32 : k), (5 / 16 : k),
      (9 / 64 * l : k)]
      [
      [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]] := by
  simp only [degreeZeroMuNoB4G5, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoB4G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroMuNoB4G5_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoB4G6` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoB4G6_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoB4G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (5 / 16 : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k),
      (-(3 / 32 * gamma) : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k),
      (-(3 / 16 * gamma) : k)]
      [
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroMuNoB4G6, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoB4G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroMuNoB4G6_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoB4G7` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoB4G7_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoB4G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(15 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(7 / 64 * beta) : k),
      (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 4 * epsilon) : k),
      (-(15 / 64 * zeta) : k)]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0],
      [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoB4G7, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoB4G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroMuNoB4G7_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoB4G8` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoB4G8_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoB4G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(3 / 32 * eta) : k), (3 / 4 * gamma : k), (5 / 8 * delta : k),
      (1 / 2 * epsilon : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoB4G8, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoB4G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroMuNoB4G8_eq_polyOf]
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
theorem degreeZeroMuNoB4Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rw [degreeZeroMuNoB4Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroMuNoB4G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoB4G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

end DefectGroups810


#print axioms degreeZeroMuNoB4G1.eq_1
#print axioms degreeZeroMuNoB4G2.eq_1
#print axioms degreeZeroMuNoB4G3.eq_1
#print axioms degreeZeroMuNoB4G4.eq_1
#print axioms degreeZeroMuNoB4G5.eq_1
#print axioms degreeZeroMuNoB4G6.eq_1
#print axioms degreeZeroMuNoB4G7.eq_1
#print axioms degreeZeroMuNoB4G8.eq_1

end Max11DegreeRoutes
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
def degreeZeroMuNoC03G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6
    - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (35 / 2048 : k) • B ^ 4
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoC03G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoC03G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)
    - (15 / 64 : k) • (A * C0 * E0)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoC03G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)
    - (63 / 1024 * l : k) • (A ^ 2 * F0)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoC03G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 32 : k) • E0 ^ 2
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoC03G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoC03G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoC03G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoC03Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroMuNoC03G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoC03G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuNoC03Polynomial810,
    degreeZeroMuNoC03G1,
    degreeZeroMuNoC03G2,
    degreeZeroMuNoC03G3,
    degreeZeroMuNoC03G4,
    degreeZeroMuNoC03G5,
    degreeZeroMuNoC03G6,
    degreeZeroMuNoC03G7,
    degreeZeroMuNoC03G8]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuNoC03G1` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoC03G1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoC03G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (385 / 65536 : k), (-(385 / 4096) : k), (-(385 / 8192) : k),
      (-(7245 / 262144 * l) : k), (35 / 2048 : k), (105 / 512 : k),
      (315 / 8192 * l : k)]
      [
      [6, 0, 0, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0],
      [0, 4, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoC03G1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoC03G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroMuNoC03G1_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoC03G2` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoC03G2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoC03G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (105 / 1024 : k), (105 / 512 : k), (945 / 8192 * l : k),
      (35 / 512 : k), (315 / 8192 * l : k), (-(357 / 8192 * beta) : k),
      (-(45 / 2048 * gamma) : k)]
      [
      [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [3, 0, 0, 1, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoC03G2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoC03G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroMuNoC03G2_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoC03G3` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoC03G3_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoC03G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(15 / 64) : k), (-(63 / 1024 * l) : k), (-(15 / 128) : k),
      (-(63 / 1024 * l) : k), (21 / 1024 * beta : k), (-(15 / 128) : k),
      (-(15 / 64) : k)]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0]] := by
  simp only [degreeZeroMuNoC03G3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoC03G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroMuNoC03G3_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoC03G4` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoC03G4_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoC03G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(63 / 512 * l) : k), (-(15 / 64) : k), (-(63 / 512 * l) : k),
      (63 / 512 * beta : k), (15 / 128 * gamma : k), (-(15 / 128) : k),
      (-(63 / 1024 * l) : k)]
      [
      [1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 1, 0]] := by
  simp only [degreeZeroMuNoC03G4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoC03G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroMuNoC03G4_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoC03G5` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoC03G5_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoC03G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (63 / 1024 * beta : k), (15 / 128 * gamma : k), (165 / 1024 * delta : k),
      (1 / 16 * epsilon : k), (5 / 32 : k), (5 / 16 : k),
      (9 / 64 * l : k)]
      [
      [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]] := by
  simp only [degreeZeroMuNoC03G5, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoC03G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroMuNoC03G5_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoC03G6` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoC03G6_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoC03G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (5 / 16 : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k),
      (-(3 / 32 * gamma) : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k),
      (-(3 / 16 * gamma) : k)]
      [
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroMuNoC03G6, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoC03G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroMuNoC03G6_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoC03G7` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoC03G7_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoC03G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(15 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(7 / 64 * beta) : k),
      (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 4 * epsilon) : k),
      (-(15 / 64 * zeta) : k)]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0],
      [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoC03G7, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoC03G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroMuNoC03G7_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoC03G8` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoC03G8_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoC03G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(3 / 32 * eta) : k), (3 / 4 * gamma : k), (5 / 8 * delta : k),
      (1 / 2 * epsilon : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoC03G8, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoC03G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨⟨hCpos, hA, hB, hD, hE, hF, hG⟩, hA0, hB0⟩
  rw [speedRefl_degreeZeroMuNoC03G8_eq_polyOf]
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
theorem degreeZeroMuNoC03Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rw [degreeZeroMuNoC03Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroMuNoC03G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoC03G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

end DefectGroups810


#print axioms degreeZeroMuNoC03G1.eq_1
#print axioms degreeZeroMuNoC03G2.eq_1
#print axioms degreeZeroMuNoC03G3.eq_1
#print axioms degreeZeroMuNoC03G4.eq_1
#print axioms degreeZeroMuNoC03G5.eq_1
#print axioms degreeZeroMuNoC03G6.eq_1
#print axioms degreeZeroMuNoC03G7.eq_1
#print axioms degreeZeroMuNoC03G8.eq_1

end Max11DegreeRoutes
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
def degreeZeroMuNoE02G1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (385 / 65536 : k) • A ^ 6
    - (385 / 4096 : k) • (A ^ 3 * B ^ 2)
    - (385 / 8192 : k) • (A ^ 4 * C0)
    - (7245 / 262144 * l : k) • (A ^ 4 * B)
    + (35 / 2048 : k) • B ^ 4
    + (105 / 512 : k) • (A * B ^ 2 * C0)
    + (315 / 8192 * l : k) • (A * B ^ 3)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoE02G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (105 / 1024 : k) • (A ^ 2 * C0 ^ 2)
    + (105 / 512 : k) • (A ^ 2 * B * D0)
    + (945 / 8192 * l : k) • (A ^ 2 * B * C0)
    + (35 / 512 : k) • (A ^ 3 * E0)
    + (315 / 8192 * l : k) • (A ^ 3 * D0)
    - (357 / 8192 * beta : k) • (A ^ 3 * B)
    - (45 / 2048 * gamma : k) • A ^ 4

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoE02G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(5 / 128 : k) • C0 ^ 3
    - (15 / 64 : k) • (B * C0 * D0)
    - (63 / 1024 * l : k) • (B * C0 ^ 2)
    - (15 / 128 : k) • (B ^ 2 * E0)
    - (63 / 1024 * l : k) • (B ^ 2 * D0)
    + (21 / 1024 * beta : k) • B ^ 3
    - (15 / 128 : k) • (A * D0 ^ 2)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoE02G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 : k) • (A * C0 * E0)
    - (63 / 512 * l : k) • (A * C0 * D0)
    - (15 / 64 : k) • (A * B * F0)
    - (63 / 512 * l : k) • (A * B * E0)
    + (63 / 512 * beta : k) • (A * B * C0)
    + (15 / 128 * gamma : k) • (A * B ^ 2)
    - (15 / 128 : k) • (A ^ 2 * G0)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoE02G5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(63 / 1024 * l : k) • (A ^ 2 * F0)
    + (63 / 1024 * beta : k) • (A ^ 2 * D0)
    + (15 / 128 * gamma : k) • (A ^ 2 * C0)
    + (165 / 1024 * delta : k) • (A ^ 2 * B)
    + (1 / 16 * epsilon : k) • A ^ 3
    + (5 / 16 : k) • (D0 * F0)
    + (9 / 64 * l : k) • (D0 * E0)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoE02G6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (5 / 16 : k) • (C0 * G0)
    + (9 / 64 * l : k) • (C0 * F0)
    - (7 / 64 * beta : k) • (C0 * D0)
    - (3 / 32 * gamma : k) • C0 ^ 2
    + (9 / 64 * l : k) • (B * G0)
    - (7 / 64 * beta : k) • (B * E0)
    - (3 / 16 * gamma : k) • (B * D0)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoE02G7
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(15 / 64 * delta : k) • (B * C0)
    - (1 / 8 * epsilon : k) • B ^ 2
    - (7 / 64 * beta : k) • (A * F0)
    - (3 / 16 * gamma : k) • (A * E0)
    - (15 / 64 * delta : k) • (A * D0)
    - (1 / 4 * epsilon : k) • (A * C0)
    - (15 / 64 * zeta : k) • (A * B)

set_option maxHeartbeats 64000000 in
def degreeZeroMuNoE02G8
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(3 / 32 * eta : k) • A ^ 2
    + (3 / 4 * gamma : k) • G0
    + (5 / 8 * delta : k) • F0
    + (1 / 2 * epsilon : k) • E0
    + (3 / 8 * zeta : k) • D0
    + (1 / 4 * eta : k) • C0
    + (1 / 8 * theta : k) • B

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoE02Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoE02Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroMuNoE02G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroMuNoE02G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroMuNoE02Polynomial810,
    degreeZeroMuNoE02G1,
    degreeZeroMuNoE02G2,
    degreeZeroMuNoE02G3,
    degreeZeroMuNoE02G4,
    degreeZeroMuNoE02G5,
    degreeZeroMuNoE02G6,
    degreeZeroMuNoE02G7,
    degreeZeroMuNoE02G8]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuNoE02G1` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoE02G1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoE02G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (385 / 65536 : k), (-(385 / 4096) : k), (-(385 / 8192) : k),
      (-(7245 / 262144 * l) : k), (35 / 2048 : k), (105 / 512 : k),
      (315 / 8192 * l : k)]
      [
      [6, 0, 0, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0],
      [0, 4, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoE02G1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoE02G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  rw [speedRefl_degreeZeroMuNoE02G1_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoE02G2` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoE02G2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoE02G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (105 / 1024 : k), (105 / 512 : k), (945 / 8192 * l : k),
      (35 / 512 : k), (315 / 8192 * l : k), (-(357 / 8192 * beta) : k),
      (-(45 / 2048 * gamma) : k)]
      [
      [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [3, 0, 0, 1, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoE02G2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoE02G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  rw [speedRefl_degreeZeroMuNoE02G2_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoE02G3` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoE02G3_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoE02G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(5 / 128) : k), (-(15 / 64) : k), (-(63 / 1024 * l) : k),
      (-(15 / 128) : k), (-(63 / 1024 * l) : k), (21 / 1024 * beta : k),
      (-(15 / 128) : k)]
      [
      [0, 0, 3, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0]] := by
  simp only [degreeZeroMuNoE02G3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoE02G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  rw [speedRefl_degreeZeroMuNoE02G3_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoE02G4` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoE02G4_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoE02G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(15 / 64) : k), (-(63 / 512 * l) : k), (-(15 / 64) : k),
      (-(63 / 512 * l) : k), (63 / 512 * beta : k), (15 / 128 * gamma : k),
      (-(15 / 128) : k)]
      [
      [1, 0, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0],
      [1, 1, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1]] := by
  simp only [degreeZeroMuNoE02G4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoE02G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  rw [speedRefl_degreeZeroMuNoE02G4_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoE02G5` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoE02G5_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoE02G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(63 / 1024 * l) : k), (63 / 1024 * beta : k), (15 / 128 * gamma : k),
      (165 / 1024 * delta : k), (1 / 16 * epsilon : k), (5 / 16 : k),
      (9 / 64 * l : k)]
      [
      [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]] := by
  simp only [degreeZeroMuNoE02G5, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoE02G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  rw [speedRefl_degreeZeroMuNoE02G5_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoE02G6` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoE02G6_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoE02G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (5 / 16 : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k),
      (-(3 / 32 * gamma) : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k),
      (-(3 / 16 * gamma) : k)]
      [
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroMuNoE02G6, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoE02G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  rw [speedRefl_degreeZeroMuNoE02G6_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoE02G7` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoE02G7_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoE02G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(15 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(7 / 64 * beta) : k),
      (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 4 * epsilon) : k),
      (-(15 / 64 * zeta) : k)]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0],
      [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoE02G7, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoE02G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  rw [speedRefl_degreeZeroMuNoE02G7_eq_polyOf]
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
/-- Reflected form of `degreeZeroMuNoE02G8` (7 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuNoE02G8_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoE02G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(3 / 32 * eta) : k), (3 / 4 * gamma : k), (5 / 8 * delta : k),
      (1 / 2 * epsilon : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoE02G8, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoE02G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD, hF, hG⟩
  rw [speedRefl_degreeZeroMuNoE02G8_eq_polyOf]
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
theorem degreeZeroMuNoE02Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : E0LeadsMuCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoE02Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      2 * E0.natDegree := by
  rw [degreeZeroMuNoE02Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroMuNoE02G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroMuNoE02G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

end DefectGroups810


#print axioms degreeZeroMuNoE02G1.eq_1
#print axioms degreeZeroMuNoE02G2.eq_1
#print axioms degreeZeroMuNoE02G3.eq_1
#print axioms degreeZeroMuNoE02G4.eq_1
#print axioms degreeZeroMuNoE02G5.eq_1
#print axioms degreeZeroMuNoE02G6.eq_1
#print axioms degreeZeroMuNoE02G7.eq_1
#print axioms degreeZeroMuNoE02G8.eq_1

end Max11DegreeRoutes
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
def degreeZeroOmicronNoB5G1
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
    - (105 / 1024 : k) • (A * B ^ 3 * C0)
    - (945 / 65536 * l : k) • (A * B ^ 4)
    - (2475 / 16384 : k) • (A ^ 2 * B * C0 ^ 2)
    - (2475 / 16384 : k) • (A ^ 2 * B ^ 2 * D0)
    - (11151 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C0)
    - (795 / 8192 : k) • (A ^ 3 * C0 * D0)
    - (3591 / 131072 * l : k) • (A ^ 3 * C0 ^ 2)

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronNoB5G2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(725 / 8192 : k) • (A ^ 3 * B * E0)
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
    + (135 / 1024 : k) • (A * C0 ^ 2 * D0)

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronNoB5G3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  (189 / 8192 * l : k) • (A * C0 ^ 3)
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
    + (207 / 4096 * l : k) • (A ^ 2 * B * F0)

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronNoB5G4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X] :=
  -(273 / 4096 * beta : k) • (A ^ 2 * B * D0)
    - (261 / 2048 * gamma : k) • (A ^ 2 * B * C0)
    - (45 / 512 * delta : k) • (A ^ 2 * B ^ 2)
    + (99 / 8192 * l : k) • (A ^ 3 * G0)
    - (147 / 8192 * beta : k) • (A ^ 3 * E0)
    - (81 / 2048 * gamma : k) • (A ^ 3 * D0)
    - (225 / 4096 * delta : k) • (A ^ 3 * C0)
    - (33 / 512 * epsilon : k) • (A ^ 3 * B)
    - (495 / 32768 * zeta : k) • A ^ 4
    - (5 / 128 : k) • D0 ^ 3
    - (25 / 128 : k) • (C0 * D0 * E0)
    - (27 / 512 * l : k) • (C0 * D0 ^ 2)
    - (5 / 64 : k) • (C0 ^ 2 * F0)
    - (45 / 1024 * l : k) • (C0 ^ 2 * E0)
    + (7 / 512 * beta : k) • C0 ^ 3

set_option maxHeartbeats 64000000 in
def degreeZeroOmicronNoB5G5
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
def degreeZeroOmicronNoB5G6
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
def degreeZeroOmicronNoB5G7
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
def degreeZeroOmicronNoB5G8
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
theorem degreeZeroOmicronNoB5Polynomial810_eq_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoB5Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      degreeZeroOmicronNoB5G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 +
      degreeZeroOmicronNoB5G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 := by
  simp only [degreeZeroOmicronNoB5Polynomial810,
    degreeZeroOmicronNoB5G1,
    degreeZeroOmicronNoB5G2,
    degreeZeroOmicronNoB5G3,
    degreeZeroOmicronNoB5G4,
    degreeZeroOmicronNoB5G5,
    degreeZeroOmicronNoB5G6,
    degreeZeroOmicronNoB5G7,
    degreeZeroOmicronNoB5G8]
  simp only [neg_smul]
  abel

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroOmicronNoB5G1` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoB5G1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoB5G1 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(12705 / 1048576) : k), (-(34155 / 33554432 * l) : k), (3745 / 65536 : k),
      (1365 / 16384 : k), (103005 / 4194304 * l : k), (525 / 32768 : k),
      (19845 / 2097152 * l : k), (-(3927 / 2097152 * beta) : k), (-(105 / 1024) : k),
      (-(945 / 65536 * l) : k), (-(2475 / 16384) : k), (-(2475 / 16384) : k),
      (-(11151 / 131072 * l) : k), (-(795 / 8192) : k), (-(3591 / 131072 * l) : k)]
      [
      [6, 1, 0, 0, 0, 0, 0], [7, 0, 0, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0], [4, 1, 1, 0, 0, 0, 0],
      [4, 2, 0, 0, 0, 0, 0], [5, 0, 0, 1, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [6, 0, 0, 0, 0, 0, 0],
      [1, 3, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0],
      [2, 2, 1, 0, 0, 0, 0], [3, 0, 1, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0]] := by
  simp only [degreeZeroOmicronNoB5G1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoB5G1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G1 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroOmicronNoB5G1_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoB5G2` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoB5G2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoB5G2 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(725 / 8192) : k), (-(3591 / 65536 * l) : k), (4095 / 131072 * beta : k),
      (-(305 / 16384) : k), (-(3087 / 262144 * l) : k), (1953 / 131072 * beta : k),
      (495 / 16384 * gamma : k), (1089 / 131072 * delta : k), (45 / 1024 : k),
      (135 / 1024 : k), (567 / 16384 * l : k), (5 / 128 : k),
      (189 / 8192 * l : k), (-(189 / 32768 * beta) : k), (135 / 1024 : k)]
      [
      [3, 1, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0],
      [4, 0, 0, 0, 1, 0, 0], [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [5, 0, 0, 0, 0, 0, 0],
      [0, 1, 3, 0, 0, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0],
      [0, 3, 0, 1, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0]] := by
  simp only [degreeZeroOmicronNoB5G2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoB5G2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G2 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroOmicronNoB5G2_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoB5G3` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoB5G3_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoB5G3 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (189 / 8192 * l : k), (135 / 1024 : k), (15 / 64 : k),
      (567 / 4096 * l : k), (105 / 1024 : k), (63 / 1024 * l : k),
      (-(567 / 8192 * beta) : k), (-(45 / 1024 * gamma) : k), (225 / 2048 : k),
      (135 / 4096 * l : k), (195 / 2048 : k), (477 / 8192 * l : k),
      (-(273 / 8192 * beta) : k), (165 / 2048 : k), (207 / 4096 * l : k)]
      [
      [1, 0, 3, 0, 0, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 1, 1, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 1, 0], [1, 2, 0, 0, 1, 0, 0], [1, 2, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 1, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0], [2, 0, 1, 0, 1, 0, 0],
      [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0]] := by
  simp only [degreeZeroOmicronNoB5G3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoB5G3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G3 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroOmicronNoB5G3_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoB5G4` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoB5G4_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoB5G4 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (-(273 / 4096 * beta) : k), (-(261 / 2048 * gamma) : k), (-(45 / 512 * delta) : k),
      (99 / 8192 * l : k), (-(147 / 8192 * beta) : k), (-(81 / 2048 * gamma) : k),
      (-(225 / 4096 * delta) : k), (-(33 / 512 * epsilon) : k), (-(495 / 32768 * zeta) : k),
      (-(5 / 128) : k), (-(25 / 128) : k), (-(27 / 512 * l) : k),
      (-(5 / 64) : k), (-(45 / 1024 * l) : k), (7 / 512 * beta : k)]
      [
      [2, 1, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1],
      [3, 0, 0, 0, 1, 0, 0], [3, 0, 0, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0]] := by
  simp only [degreeZeroOmicronNoB5G4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoB5G4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G4 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroOmicronNoB5G4_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoB5G5` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoB5G5_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoB5G5 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
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
  simp only [degreeZeroOmicronNoB5G5, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoB5G5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G5 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroOmicronNoB5G5_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoB5G6` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoB5G6_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoB5G6 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
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
  simp only [degreeZeroOmicronNoB5G6, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoB5G6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G6 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroOmicronNoB5G6_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoB5G7` (15 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoB5G7_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoB5G7 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
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
  simp only [degreeZeroOmicronNoB5G7, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoB5G7_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G7 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroOmicronNoB5G7_eq_polyOf]
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
/-- Reflected form of `degreeZeroOmicronNoB5G8` (10 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronNoB5G8_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroOmicronNoB5G8 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
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
  simp only [degreeZeroOmicronNoB5G8, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoB5G8_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5G8 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE, hF, hG⟩, hA0⟩
  rw [speedRefl_degreeZeroOmicronNoB5G8_eq_polyOf]
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
theorem degreeZeroOmicronNoB5Polynomial810_natDegree_lt_of_groups
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BLeadsOmicronCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoB5Polynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rw [degreeZeroOmicronNoB5Polynomial810_eq_groups]
  exact natDegree_add8_lt810
    (degreeZeroOmicronNoB5G1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G7_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)
    (degreeZeroOmicronNoB5G8_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone)

end DefectGroups810


#print axioms degreeZeroOmicronNoB5G1.eq_1
#print axioms degreeZeroOmicronNoB5G2.eq_1
#print axioms degreeZeroOmicronNoB5G3.eq_1
#print axioms degreeZeroOmicronNoB5G4.eq_1
#print axioms degreeZeroOmicronNoB5G5.eq_1
#print axioms degreeZeroOmicronNoB5G6.eq_1
#print axioms degreeZeroOmicronNoB5G7.eq_1
#print axioms degreeZeroOmicronNoB5G8.eq_1

end Max11DegreeRoutes
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
