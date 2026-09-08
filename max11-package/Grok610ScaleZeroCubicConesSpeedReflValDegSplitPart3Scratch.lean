import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart2Scratch

/-! # SPEED: theorems of `Grok610ScaleZeroCubicConesSpeedReflValDegScratch`, part 3 of 16, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open scoped Polynomial.Bivariate
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
set_option maxRecDepth 8000000

section CubicKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_BC_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceBC610 A B C D E +
        degreeZeroKappaCubicNoBC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaCubic610, kappaCubicFaceBC610, degreeZeroKappaCubicNoBC610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaCubicNoBC610` (30 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoBC610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoBC610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (-(5 / 27) : k), (10 / 9 : k),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l) : k),
      (1 / 16 * l : k), (-(1 / 8 * l) : k), (1 / 16 * l : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha) : k), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta) : k),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoBC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBC610 A B C D E) :
    (degreeZeroKappaCubicNoBC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      B.natDegree + 2 * C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroKappaCubicNoBC610_eq_polyOf]
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



theorem cubicCone_BC_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBC610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaCubicFaceBC610 A B C D E).natDegree = B.natDegree + 2 * C.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, kappaCubicFaceBC610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoBC610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_BC_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt⟩
  omega



set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_BD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceBD610 A B C D E +
        degreeZeroKappaCubicNoBD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaCubic610, kappaCubicFaceBD610, degreeZeroKappaCubicNoBD610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaCubicNoBD610` (30 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoBD610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoBD610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (-(5 / 27) : k), (10 / 9 : k),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l) : k),
      (1 / 16 * l : k), (-(1 / 8 * l) : k), (1 / 16 * l : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha) : k), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta) : k),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 3, 0, 0, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoBD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBD610 A B C D E) :
    (degreeZeroKappaCubicNoBD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroKappaCubicNoBD610_eq_polyOf]
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



theorem cubicCone_BD_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBD610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaCubicFaceBD610 A B C D E).natDegree = 2 * B.natDegree + D.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, kappaCubicFaceBD610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hrest := degreeZeroKappaCubicNoBD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_BD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt⟩
  omega



set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_CD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceCD610 A B C D E +
        degreeZeroLambdaCubicNoCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroLambdaCubic610, lambdaCubicFaceCD610, degreeZeroLambdaCubicNoCD610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroLambdaCubicNoCD610` (34 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroLambdaCubicNoCD610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoCD610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27) : k),
      (-(5 / 27) : k), (-(10 / 27) : k), (5 / 9 : k),
      (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k), (-(1 / 96 * l) : k),
      (1 / 32 * l : k), (-(1 / 8 * l) : k), (-(1 / 8 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 16 * l) : k), (3 / 4 * l : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k), (-(7 / 432 * beta) : k),
      (-(7 / 216 * beta) : k), (-(35 / 1296 * beta) : k), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta) : k), (-(5 / 36 * delta) : k),
      (-(5 / 36 * delta) : k), (-(1 / 9 * epsilon) : k), (2 / 3 * epsilon : k),
      (-(1 / 12 * zeta) : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
      [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCD610 A B C D E) :
    (degreeZeroLambdaCubicNoCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroLambdaCubicNoCD610_eq_polyOf]
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



theorem cubicCone_CD_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCD610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt⟩
    omega
  have hc : (-(5 / 81 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (lambdaCubicFaceCD610 A B C D E).natDegree = 3 * C.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, lambdaCubicFaceCD610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoCD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_CD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt⟩
  omega



set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_CE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicFaceCE610 A B C D E +
        degreeZeroOmicronCubicNoCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroOmicronCubic610, omicronCubicFaceCE610, degreeZeroOmicronCubicNoCE610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroOmicronCubicNoCE610` (44 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronCubicNoCE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroOmicronCubicNoCE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 486) : k), (5 / 81 : k), (10 / 81 : k),
      (25 / 486 : k), (5 / 54 : k), (-(5 / 27) : k),
      (-(5 / 27) : k), (-(5 / 6912 * l) : k), (1 / 864 * l : k),
      (-(1 / 288 * l) : k), (-(1 / 96 * l) : k), (7 / 96 * l : k),
      (1 / 24 * l : k), (1 / 16 * l : k), (-(1 / 8 * l) : k),
      (-(1 / 4 * l) : k), (-(1 / 8 * l) : k), (-(3 / 16 * l) : k),
      (4 / 81 * alpha : k), (1 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
      (-(2 / 27 * alpha) : k), (-(2 / 9 * alpha) : k), (-(4 / 81 * alpha) : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k), (7 / 1296 * beta : k),
      (7 / 648 * beta : k), (-(7 / 216 * beta) : k), (-(7 / 144 * beta) : k),
      (-(7 / 108 * beta) : k), (7 / 36 * beta : k), (-(5 / 432 * delta) : k),
      (5 / 108 * delta : k), (5 / 324 * delta : k), (-(5 / 36 * delta) : k),
      (1 / 27 * epsilon : k), (-(1 / 9 * epsilon) : k), (-(1 / 9 * epsilon) : k),
      (-(1 / 12 * zeta) : k), (-(1 / 6 * zeta) : k), (-(1 / 18 * eta) : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 4, 0, 0, 0], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [0, 3, 0, 1, 0],
      [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 1, 2, 0], [4, 0, 0, 1, 0],
      [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]] :=
  rfl


set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubicNoCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCE610 A B C D E) :
    (degreeZeroOmicronCubicNoCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  rw [speedRefl_degreeZeroOmicronCubicNoCE610_eq_polyOf]
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



theorem cubicCone_CE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCE610 A B C D E)
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (omicronCubicFaceCE610 A B C D E).natDegree = 2 * C.natDegree + E.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, omicronCubicFaceCE610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
  have hrest := degreeZeroOmicronCubicNoCE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroOmicronCubic610_eq_CE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt⟩
  omega



set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_DE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceDE610 A B C D E +
        degreeZeroKappaCubicNoDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaCubic610, kappaCubicFaceDE610, degreeZeroKappaCubicNoDE610]
  all_goals module


end CubicKills610

end Max11DegreeRoutes

end
