import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart101Scratch

/-! # SPEED: theorems of `Grok610ScaleZeroCubicConesSpeedReflValDegScratch`, part 4 of 16, so that no single
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

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaCubicNoDE610` (30 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k),
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
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeDE610 A B C D E) :
    (degreeZeroKappaCubicNoDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  rw [speedRefl_degreeZeroKappaCubicNoDE610_eq_polyOf]
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



theorem cubicCone_DE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeDE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt⟩
    omega
  have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicFaceDE610 A B C D E).natDegree = D.natDegree + E.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, kappaCubicFaceDE610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaCubicNoDE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_DE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hEpos, hDE, hAlt, hBlt, hClt⟩
  omega



set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_ABE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceABE610 A B C D E +
        degreeZeroKappaCubicNoABE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaCubic610, kappaCubicFaceABE610, degreeZeroKappaCubicNoABE610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaCubicNoABE610` (30 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoABE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoABE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 27) : k), (-(5 / 27) : k), (10 / 9 : k),
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
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoABE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABE610 A B C D E) :
    (degreeZeroKappaCubicNoABE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  rw [speedRefl_degreeZeroKappaCubicNoABE610_eq_polyOf]
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



theorem cubicCone_ABE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt⟩
    omega
  have hc : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicFaceABE610 A B C D E).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, kappaCubicFaceABE610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoABE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_ABE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hBpos, hEpos, hAB, hAE, hClt, hDlt⟩
  omega



set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubic610_eq_ACD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceACD610 A B C D E +
        degreeZeroMuCubicNoACD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroMuCubic610, muCubicFaceACD610, degreeZeroMuCubicNoACD610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroMuCubicNoACD610` (47 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuCubicNoACD610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroMuCubicNoACD610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 1458) : k), (5 / 54 : k), (5 / 162 : k),
      (20 / 243 : k), (-(5 / 27) : k), (-(10 / 27) : k),
      (-(5 / 27) : k), (35 / 248832 * l : k), (5 / 2304 * l : k),
      (1 / 144 * l : k), (1 / 96 * l : k), (1 / 192 * l : k),
      (1 / 16 * l : k), (3 / 128 * l : k), (-(1 / 8 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 8 * l) : k), (-(1 / 16 * l) : k),
      (3 / 8 * l : k), (2 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
      (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
      (4 / 9 * alpha : k), (7 / 15552 * beta : k), (7 / 1296 * beta : k),
      (7 / 5184 * beta : k), (7 / 432 * beta : k), (-(7 / 108 * beta) : k),
      (-(35 / 432 * beta) : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 3456 * delta : k), (5 / 432 * delta : k), (5 / 216 * delta : k),
      (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k), (-(1 / 9 * epsilon) : k),
      (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k), (-(1 / 8 * zeta) : k),
      (1 / 2 * zeta : k), (-(1 / 18 * eta) : k), (1 / 3 * eta : k),
      (1 / 72 * theta : k), (1 / 6 * theta : k)]
      [
      [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
      [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [6, 0, 0, 0, 0],
      [4, 0, 1, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0],
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [1, 3, 0, 0, 0],
      [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
      [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
      [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
      [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
      [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [3, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0],
      [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]] :=
  rfl


set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoACD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACD610 A B C D E) :
    (degreeZeroMuCubicNoACD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * C.natDegree + D.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroMuCubicNoACD610_eq_polyOf]
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



theorem cubicCone_ACD_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACD610 A B C D E)
    (hdeg : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muCubicFaceACD610 A B C D E).natDegree = 2 * C.natDegree + D.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muCubicFaceACD610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
  have hrest := degreeZeroMuCubicNoACD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroMuCubic610_eq_ACD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hDpos, hAC, hAD, hBlt, hElt⟩
  omega



set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_ACE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicFaceACE610 A B C D E +
        degreeZeroOmicronCubicNoACE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroOmicronCubic610, omicronCubicFaceACE610, degreeZeroOmicronCubicNoACE610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroOmicronCubicNoACE610` (44 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronCubicNoACE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroOmicronCubicNoACE610 l alpha beta delta epsilon zeta eta theta A B C D E =
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
theorem degreeZeroOmicronCubicNoACE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACE610 A B C D E) :
    (degreeZeroOmicronCubicNoACE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  rw [speedRefl_degreeZeroOmicronCubicNoACE610_eq_polyOf]
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



theorem cubicCone_ACE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACE610 A B C D E)
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (omicronCubicFaceACE610 A B C D E).natDegree = 2 * C.natDegree + E.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, omicronCubicFaceACE610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
  have hrest := degreeZeroOmicronCubicNoACE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroOmicronCubic610_eq_ACE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hEpos, hAC, hAE, hBlt, hDlt⟩
  omega



set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_ADE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceADE610 A B C D E +
        degreeZeroKappaCubicNoADE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaCubic610, kappaCubicFaceADE610, degreeZeroKappaCubicNoADE610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaCubicNoADE610` (30 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoADE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoADE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k),
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
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoADE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeADE610 A B C D E) :
    (degreeZeroKappaCubicNoADE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  rw [speedRefl_degreeZeroKappaCubicNoADE610_eq_polyOf]
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



end CubicKills610

end Max11DegreeRoutes

end
/-! # SPEED: theorems of `Grok610ScaleZeroCubicConesSpeedReflValDegScratch`, part 5 of 16, so that no single
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

theorem cubicCone_ADE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeADE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt⟩
    omega
  have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicFaceADE610 A B C D E).natDegree = D.natDegree + E.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, kappaCubicFaceADE610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaCubicNoADE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_ADE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hEpos, hAD, hAE, hBlt, hClt⟩
  omega



set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_BCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceBCE610 A B C D E +
        degreeZeroKappaCubicNoBCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaCubic610, kappaCubicFaceBCE610, degreeZeroKappaCubicNoBCE610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaCubicNoBCE610` (30 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoBCE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoBCE610 l alpha beta delta epsilon zeta eta theta A B C D E =
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
theorem degreeZeroKappaCubicNoBCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCE610 A B C D E) :
    (degreeZeroKappaCubicNoBCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      B.natDegree + 2 * C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  rw [speedRefl_degreeZeroKappaCubicNoBCE610_eq_polyOf]
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



theorem cubicCone_BCE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaCubicFaceBCE610 A B C D E).natDegree = B.natDegree + 2 * C.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, kappaCubicFaceBCE610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoBCE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_BCE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hCpos, hEpos, hBC, hBE, hAlt, hDlt⟩
  omega



set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubic610_eq_BDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceBDE610 A B C D E +
        degreeZeroMuCubicNoBDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroMuCubic610, muCubicFaceBDE610, degreeZeroMuCubicNoBDE610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroMuCubicNoBDE610` (47 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuCubicNoBDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroMuCubicNoBDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 1458) : k), (5 / 54 : k), (5 / 162 : k),
      (20 / 243 : k), (-(5 / 27) : k), (-(10 / 27) : k),
      (-(5 / 27) : k), (35 / 248832 * l : k), (5 / 2304 * l : k),
      (1 / 144 * l : k), (1 / 96 * l : k), (1 / 192 * l : k),
      (1 / 16 * l : k), (3 / 128 * l : k), (-(1 / 8 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 8 * l) : k), (-(1 / 16 * l) : k),
      (3 / 8 * l : k), (2 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
      (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
      (4 / 9 * alpha : k), (7 / 15552 * beta : k), (7 / 1296 * beta : k),
      (7 / 5184 * beta : k), (7 / 432 * beta : k), (-(7 / 108 * beta) : k),
      (-(35 / 432 * beta) : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 3456 * delta : k), (5 / 432 * delta : k), (5 / 216 * delta : k),
      (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k), (-(1 / 9 * epsilon) : k),
      (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k), (-(1 / 8 * zeta) : k),
      (1 / 2 * zeta : k), (-(1 / 18 * eta) : k), (1 / 3 * eta : k),
      (1 / 72 * theta : k), (1 / 6 * theta : k)]
      [
      [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
      [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0],
      [4, 0, 1, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0],
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [1, 3, 0, 0, 0],
      [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
      [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
      [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
      [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
      [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [3, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0],
      [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]] :=
  rfl


set_option maxHeartbeats 32000000 in
theorem degreeZeroMuCubicNoBDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBDE610 A B C D E) :
    (degreeZeroMuCubicNoBDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      B.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  rw [speedRefl_degreeZeroMuCubicNoBDE610_eq_polyOf]
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



theorem cubicCone_BDE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBDE610 A B C D E)
    (hdeg : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt⟩
    omega
  have hc : (-(5 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muCubicFaceBDE610 A B C D E).natDegree = B.natDegree + 2 * D.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muCubicFaceBDE610]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroMuCubicNoBDE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroMuCubic610_eq_BDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, hEpos, hBD, hBE, hAlt, hClt⟩
  omega



set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_CDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceCDE610 A B C D E +
        degreeZeroKappaCubicNoCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaCubic610, kappaCubicFaceCDE610, degreeZeroKappaCubicNoCDE610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaCubicNoCDE610` (30 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoCDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k),
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
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCDE610 A B C D E) :
    (degreeZeroKappaCubicNoCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  rw [speedRefl_degreeZeroKappaCubicNoCDE610_eq_polyOf]
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



theorem cubicCone_CDE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeCDE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt⟩
    omega
  have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicFaceCDE610 A B C D E).natDegree = D.natDegree + E.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, kappaCubicFaceCDE610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaCubicNoCDE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_CDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, hEpos, hCD, hCE, hAlt, hBlt⟩
  omega



set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_ACDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceACDE610 A B C D E +
        degreeZeroKappaCubicNoACDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaCubic610, kappaCubicFaceACDE610, degreeZeroKappaCubicNoACDE610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaCubicNoACDE610` (30 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoACDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoACDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (-(5 / 27) : k), (-(5 / 27) : k),
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
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoACDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACDE610 A B C D E) :
    (degreeZeroKappaCubicNoACDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  rw [speedRefl_degreeZeroKappaCubicNoACDE610_eq_polyOf]
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



theorem cubicCone_ACDE_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeACDE610 A B C D E)
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
    omega
  have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicFaceACDE610 A B C D E).natDegree = D.natDegree + E.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, kappaCubicFaceACDE610]
    rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  have hrest := degreeZeroKappaCubicNoACDE610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroKappaCubic610_eq_ACDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hAC, hAD, hAE, hBlt⟩
  omega



end CubicKills610

end Max11DegreeRoutes

end
/-! # SPEED: theorems of `Grok610ScaleZeroCubicConesSpeedReflValDegScratch`, part 6 of 16, so that no single
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

set_option maxHeartbeats 32000000 in
theorem cubicInner_BE_identity
    (b e : k) :
    ((-2 / 8505 : k) * b ^ 4 + (1 / 405 : k) * b ^ 2 * e + (1 / 135 : k) * e ^ 2) * lambdaCubicInnerBE610 b e +
      ((-1 / 3402 : k) * b ^ 3 + (2 / 567 : k) * b * e) * primitiveCubicInnerBE610 b e =
      e ^ 4 := by
  simp only [lambdaCubicInnerBE610, primitiveCubicInnerBE610]
  ring


set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_BE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceBE610 A B C D E +
        degreeZeroLambdaCubicNoBE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroLambdaCubic610, lambdaCubicFaceBE610, degreeZeroLambdaCubicNoBE610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroLambdaCubicNoBE610` (32 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroLambdaCubicNoBE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoBE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (-(5 / 27) : k), (-(10 / 27) : k),
      (-(5 / 81) : k), (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k),
      (-(1 / 96 * l) : k), (1 / 32 * l : k), (-(1 / 8 * l) : k),
      (-(1 / 8 * l) : k), (-(3 / 16 * l) : k), (-(3 / 16 * l) : k),
      (3 / 4 * l : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
      (4 / 9 * alpha : k), (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k),
      (-(7 / 432 * beta) : k), (-(7 / 216 * beta) : k), (-(35 / 1296 * beta) : k),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (-(5 / 432 * delta) : k),
      (-(5 / 36 * delta) : k), (-(5 / 36 * delta) : k), (-(1 / 9 * epsilon) : k),
      (2 / 3 * epsilon : k), (-(1 / 12 * zeta) : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 2, 1, 0, 0], [1, 0, 0, 2, 0], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
      [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
      [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0],
      [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoBE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBE610 A B C D E) :
    (degreeZeroLambdaCubicNoBE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  rw [speedRefl_degreeZeroLambdaCubicNoBE610_eq_polyOf]
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


theorem lambdaCubicFaceBE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBE610 A B C D E)
    (hBne : B ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicFaceBE610 A B C D E).coeff (4 * B.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerBE610 B.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, lambdaCubicFaceBE610, lambdaCubicInnerBE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4 : (B ^ 4).natDegree = 4 * B.natDegree := by
    exact natDegree_pow _ _
  have hcf_B4 : (B ^ 4).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (4 * B.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4, hcf_B2E, hcf_E2]
  ring


set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubic610_eq_BE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceBE610 A B C D E +
        degreeZeroPrimitiveCubicNoBE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceBE610, degreeZeroPrimitiveCubicNoBE610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroPrimitiveCubicNoBE610` (75 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPrimitiveCubicNoBE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroPrimitiveCubicNoBE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 2916) : k), (-(5 / 108) : k), (5 / 324 : k),
      (-(25 / 243) : k), (-(5 / 54) : k), (10 / 27 : k),
      (5 / 27 : k), (5 / 27 : k), (5 / 9 : k),
      (5 / 27 : k), (-(10 / 9) : k), (-(10 / 27) : k),
      (5 / 27648 * l : k), (25 / 6912 * l : k), (-(17 / 13824 * l) : k),
      (1 / 128 * l : k), (1 / 288 * l : k), (13 / 576 * l : k),
      (-(5 / 192 * l) : k), (-(1 / 32 * l) : k), (1 / 16 * l : k),
      (1 / 8 * l : k), (3 / 8 * l : k), (1 / 16 * l : k),
      (3 / 16 * l : k), (9 / 32 * l : k), (-(3 / 4 * l) : k),
      (-(3 / 8 * l) : k), (-(3 / 4 * l) : k), (-(1 / 81 * alpha) : k),
      (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k), (4 / 27 * alpha : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
      (35 / 62208 * beta : k), (49 / 5184 * beta : k), (-(7 / 1728 * beta) : k),
      (7 / 432 * beta : k), (-(7 / 216 * beta) : k), (7 / 144 * beta : k),
      (35 / 432 * beta : k), (35 / 1728 * beta : k), (7 / 36 * beta : k),
      (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k), (-(7 / 18 * beta) : k),
      (-(7 / 108 * beta) : k), (7 / 12 * beta : k), (1 / 576 * delta : k),
      (5 / 216 * delta : k), (-(5 / 216 * delta) : k), (5 / 36 * delta : k),
      (5 / 36 * delta : k), (-(5 / 12 * delta) : k), (-(1 / 18 * epsilon) : k),
      (2 / 9 * epsilon : k), (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k),
      (1 / 192 * zeta : k), (1 / 24 * zeta : k), (1 / 12 * zeta : k),
      (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k), (-(1 / 36 * eta) : k),
      (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k), (1 / 72 * theta : k),
      (1 / 6 * theta : k), (-(1 / 12 * theta) : k), (1 * theta : k)]
      [
      [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [1, 3, 1, 0, 0],
      [2, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0], [1, 0, 2, 1, 0],
      [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0],
      [7, 0, 0, 0, 0], [5, 0, 1, 0, 0], [4, 2, 0, 0, 0], [4, 0, 0, 0, 1],
      [3, 1, 0, 1, 0], [3, 0, 2, 0, 0], [2, 2, 1, 0, 0], [1, 4, 0, 0, 0],
      [2, 0, 1, 0, 1], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 0, 3, 0, 0],
      [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1],
      [0, 0, 1, 2, 0], [2, 3, 0, 0, 0], [2, 1, 0, 0, 1], [2, 0, 1, 1, 0],
      [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1],
      [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0],
      [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
      [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1],
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [2, 0, 0, 1, 0],
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
      [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0],
      [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] :=
  rfl


set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubicNoBE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBE610 A B C D E) :
    (degreeZeroPrimitiveCubicNoBE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  rw [speedRefl_degreeZeroPrimitiveCubicNoBE610_eq_polyOf]
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


theorem primitiveCubicFaceBE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBE610 A B C D E)
    (hBne : B ≠ 0)
    (hEne : E ≠ 0)
    : (primitiveCubicFaceBE610 A B C D E).coeff (5 * B.natDegree) =
      (1 / 243 : k) * primitiveCubicInnerBE610 B.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, primitiveCubicFaceBE610, primitiveCubicInnerBE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 5 * B.natDegree := by
    exact natDegree_pow _ _
  have hcf_B5 : (B ^ 5).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B5, hcf_B3E]
  ring


set_option maxHeartbeats 16000000 in
theorem cubicCone_BE_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBE610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hlambdainner : lambdaCubicInnerBE610 B.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoBE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceBE610_coeff_top (hcone := hcone) (hBne := hBne) (hEne := hEne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_BE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerBE610 B.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoBE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceBE610_coeff_top (hcone := hcone) (hBne := hBne) (hEne := hEne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hBpos, hEpos, hBE, hAlt, hClt, hDlt⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_BE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_BE_identity B.leadingCoeff E.leadingCoeff
  have hpow : E.leadingCoeff ^ 4 = 0 := by
    rw [hlambdainner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)



set_option maxHeartbeats 32000000 in
theorem cubicInner_ABC_identity
    (a b c : k) :
    ((-73 / 2880 : k) * a * b * c + (-1 / 120 : k) * b ^ 3) * kappaCubicInnerABC610 a b c +
      ((1 / 120 : k) * a * b ^ 2 + (-1 / 15 : k) * c ^ 2) * lambdaCubicInnerABC610 a b c +
      ((-1 / 2880 : k) * b * c) * muCubicInnerABC610 a b c =
      c ^ 5 := by
  simp only [kappaCubicInnerABC610, lambdaCubicInnerABC610, muCubicInnerABC610, omicronCubicInnerABC610, primitiveCubicInnerABC610]
  ring


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_ABC_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceABC610 A B C D E +
        degreeZeroKappaCubicNoABC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaCubic610, kappaCubicFaceABC610, degreeZeroKappaCubicNoABC610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaCubicNoABC610` (29 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoABC610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoABC610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 27) : k), (10 / 9 : k), (7 / 6912 * l : k),
      (5 / 288 * l : k), (-(1 / 192 * l) : k), (1 / 16 * l : k),
      (-(1 / 8 * l) : k), (1 / 16 * l : k), (-(3 / 16 * l) : k),
      (3 / 4 * l : k), (3 / 8 * l : k), (-(4 / 81 * alpha) : k),
      (4 / 9 * alpha : k), (4 / 9 * alpha : k), (35 / 10368 * beta : k),
      (7 / 144 * beta : k), (-(7 / 432 * beta) : k), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (7 / 72 * beta : k), (5 / 432 * delta : k),
      (5 / 36 * delta : k), (-(5 / 72 * delta) : k), (5 / 6 * delta : k),
      (2 / 3 * epsilon : k), (1 / 24 * zeta : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [0, 2, 0, 1, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0],
      [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
      [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0],
      [1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubicNoABC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABC610 A B C D E) :
    (degreeZeroKappaCubicNoABC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroKappaCubicNoABC610_eq_polyOf]
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


theorem kappaCubicFaceABC610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABC610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    : (kappaCubicFaceABC610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicInnerABC610 A.leadingCoeff B.leadingCoeff C.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, kappaCubicFaceABC610, kappaCubicInnerABC610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB3, hcf_BC2]
  ring


set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_ABC_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceABC610 A B C D E +
        degreeZeroLambdaCubicNoABC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroLambdaCubic610, lambdaCubicFaceABC610, degreeZeroLambdaCubicNoABC610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroLambdaCubicNoABC610` (32 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroLambdaCubicNoABC610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoABC610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 27) : k), (-(5 / 27) : k), (-(10 / 27) : k),
      (5 / 9 : k), (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k),
      (-(1 / 96 * l) : k), (1 / 32 * l : k), (-(1 / 8 * l) : k),
      (-(1 / 8 * l) : k), (-(3 / 16 * l) : k), (-(3 / 16 * l) : k),
      (3 / 4 * l : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
      (4 / 9 * alpha : k), (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k),
      (-(7 / 432 * beta) : k), (-(7 / 216 * beta) : k), (-(35 / 1296 * beta) : k),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (-(5 / 432 * delta) : k),
      (-(5 / 36 * delta) : k), (-(5 / 36 * delta) : k), (-(1 / 9 * epsilon) : k),
      (2 / 3 * epsilon : k), (-(1 / 12 * zeta) : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 0, 0, 2],
      [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
      [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
      [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0],
      [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoABC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABC610 A B C D E) :
    (degreeZeroLambdaCubicNoABC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroLambdaCubicNoABC610_eq_polyOf]
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


end CubicKills610

end Max11DegreeRoutes

end
