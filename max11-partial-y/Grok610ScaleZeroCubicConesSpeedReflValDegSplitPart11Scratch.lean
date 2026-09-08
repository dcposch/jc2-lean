import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart10Scratch

/-! # SPEED: theorems of `Grok610ScaleZeroCubicConesSpeedReflValDegScratch`, part 11 of 16, so that no single
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

set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubic610_eq_ABCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceABCE610 A B C D E +
        degreeZeroLambdaCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroLambdaCubic610, lambdaCubicFaceABCE610, degreeZeroLambdaCubicNoABCE610]
  all_goals module


set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroLambdaCubicNoABCE610` (30 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroLambdaCubicNoABCE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoABCE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 27) : k), (-(10 / 27) : k), (-(5 / 6912 * l) : k),
      (-(1 / 288 * l) : k), (-(1 / 96 * l) : k), (1 / 32 * l : k),
      (-(1 / 8 * l) : k), (-(1 / 8 * l) : k), (-(3 / 16 * l) : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (-(4 / 27 * alpha) : k),
      (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (2 / 9 * alpha : k),
      (-(7 / 2592 * beta) : k), (-(7 / 432 * beta) : k), (-(7 / 216 * beta) : k),
      (-(35 / 1296 * beta) : k), (7 / 36 * beta : k), (7 / 36 * beta : k),
      (-(5 / 432 * delta) : k), (-(5 / 36 * delta) : k), (-(5 / 36 * delta) : k),
      (-(1 / 9 * epsilon) : k), (2 / 3 * epsilon : k), (-(1 / 12 * zeta) : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 0, 0, 2, 0], [0, 1, 1, 1, 0], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoABCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCE610 A B C D E) :
    (degreeZeroLambdaCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  rw [speedRefl_degreeZeroLambdaCubicNoABCE610_eq_polyOf]
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
set_option maxHeartbeats 64000000 in


theorem lambdaCubicFaceABCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicFaceABCE610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, lambdaCubicFaceABCE610, lambdaCubicInnerABCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  simp only [← mul_assoc]
  rw [hcf_AB2C, hcf_B4, hcf_B2E, hcf_C3, hcf_E2]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuCubic610_eq_ABCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceABCE610 A B C D E +
        degreeZeroMuCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroMuCubic610, muCubicFaceABCE610, degreeZeroMuCubicNoABCE610]
  all_goals module


set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuCubicNoABCE610` (44 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuCubicNoABCE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroMuCubicNoABCE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 54 : k), (-(5 / 27) : k), (-(5 / 27) : k),
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
      [1, 2, 0, 1, 0], [1, 0, 0, 1, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0],
      [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
      [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0],
      [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
      [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]] :=
  rfl


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuCubicNoABCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCE610 A B C D E) :
    (degreeZeroMuCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  rw [speedRefl_degreeZeroMuCubicNoABCE610_eq_polyOf]
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
set_option maxHeartbeats 64000000 in


theorem muCubicFaceABCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (muCubicFaceABCE610 A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 1458 : k) * muCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muCubicFaceABCE610, muCubicInnerABCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_ABC2 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC2 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_ABC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
    omega
  have hcf_B3C : ((B ^ 3 * C)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  simp only [← mul_assoc]
  rw [hcf_A2B3, hcf_ABC2, hcf_B3C, hcf_BCE]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubic610_eq_ABCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicFaceABCE610 A B C D E +
        degreeZeroOmicronCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroOmicronCubic610, omicronCubicFaceABCE610, degreeZeroOmicronCubicNoABCE610]
  all_goals module


set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroOmicronCubicNoABCE610` (41 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronCubicNoABCE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroOmicronCubicNoABCE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (10 / 81 : k), (25 / 486 : k), (-(5 / 27) : k),
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
      [1, 1, 1, 1, 0], [0, 3, 0, 1, 0], [0, 1, 0, 1, 1], [0, 0, 1, 2, 0],
      [4, 0, 0, 1, 0], [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0],
      [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1],
      [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0],
      [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0],
      [1, 3, 0, 0, 0], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
      [0, 0, 0, 1, 1], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
      [0, 0, 1, 1, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
      [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [0, 0, 0, 1, 0]] :=
  rfl


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoABCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCE610 A B C D E) :
    (degreeZeroOmicronCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  rw [speedRefl_degreeZeroOmicronCubicNoABCE610_eq_polyOf]
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
set_option maxHeartbeats 64000000 in


theorem omicronCubicFaceABCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (omicronCubicFaceABCE610 A B C D E).coeff (A.natDegree + 4 * B.natDegree) =
      (1 / 486 : k) * omicronCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, omicronCubicFaceABCE610, omicronCubicInnerABCE610, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  simp only [← mul_assoc]
  rw [hcf_AB4, hcf_AB2E, hcf_B2C2, hcf_C2E]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveCubic610_eq_ABCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceABCE610 A B C D E +
        degreeZeroPrimitiveCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceABCE610, degreeZeroPrimitiveCubicNoABCE610]
  all_goals module


set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroPrimitiveCubicNoABCE610` (70 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPrimitiveCubicNoABCE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroPrimitiveCubicNoABCE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 108) : k), (-(5 / 54) : k), (5 / 27 : k),
      (5 / 27 : k), (5 / 9 : k), (-(10 / 9) : k),
      (-(10 / 27) : k), (5 / 27648 * l : k), (25 / 6912 * l : k),
      (-(17 / 13824 * l) : k), (1 / 128 * l : k), (1 / 288 * l : k),
      (13 / 576 * l : k), (-(5 / 192 * l) : k), (-(1 / 32 * l) : k),
      (1 / 16 * l : k), (1 / 8 * l : k), (3 / 8 * l : k),
      (1 / 16 * l : k), (3 / 16 * l : k), (9 / 32 * l : k),
      (-(3 / 4 * l) : k), (-(3 / 8 * l) : k), (-(3 / 4 * l) : k),
      (-(1 / 81 * alpha) : k), (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k), (35 / 62208 * beta : k), (49 / 5184 * beta : k),
      (-(7 / 1728 * beta) : k), (7 / 432 * beta : k), (-(7 / 216 * beta) : k),
      (7 / 144 * beta : k), (35 / 432 * beta : k), (35 / 1728 * beta : k),
      (7 / 36 * beta : k), (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k),
      (-(7 / 18 * beta) : k), (-(7 / 108 * beta) : k), (7 / 12 * beta : k),
      (1 / 576 * delta : k), (5 / 216 * delta : k), (-(5 / 216 * delta) : k),
      (5 / 36 * delta : k), (5 / 36 * delta : k), (-(5 / 12 * delta) : k),
      (-(1 / 18 * epsilon) : k), (2 / 9 * epsilon : k), (2 / 27 * epsilon : k),
      (-(2 / 3 * epsilon) : k), (1 / 192 * zeta : k), (1 / 24 * zeta : k),
      (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k),
      (-(1 / 36 * eta) : k), (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k),
      (1 / 72 * theta : k), (1 / 6 * theta : k), (-(1 / 12 * theta) : k),
      (1 * theta : k)]
      [
      [2, 2, 0, 1, 0], [2, 0, 0, 1, 1], [1, 1, 0, 2, 0], [1, 0, 2, 1, 0],
      [0, 2, 1, 1, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0], [7, 0, 0, 0, 0],
      [5, 0, 1, 0, 0], [4, 2, 0, 0, 0], [4, 0, 0, 0, 1], [3, 1, 0, 1, 0],
      [3, 0, 2, 0, 0], [2, 2, 1, 0, 0], [1, 4, 0, 0, 0], [2, 0, 1, 0, 1],
      [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 0, 3, 0, 0], [0, 3, 0, 1, 0],
      [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0],
      [2, 3, 0, 0, 0], [2, 1, 0, 0, 1], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0], [4, 0, 1, 0, 0],
      [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0],
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 2, 0],
      [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
      [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
      [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [2, 1, 0, 0, 0],
      [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] :=
  rfl


set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveCubicNoABCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCE610 A B C D E) :
    (degreeZeroPrimitiveCubicNoABCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  rw [speedRefl_degreeZeroPrimitiveCubicNoABCE610_eq_polyOf]
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
set_option maxHeartbeats 64000000 in


theorem primitiveCubicFaceABCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (primitiveCubicFaceABCE610 A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 2916 : k) * primitiveCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, primitiveCubicFaceABCE610, primitiveCubicInnerABCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BC2 : ((A ^ 2 * B * C ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BC2 : ((A ^ 2 * B * C ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB3C : ((A * B ^ 3 * C)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3C : ((A * B ^ 3 * C)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_AB3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCE : ((A * B * C * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCE : ((A * B * C * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ABCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
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
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  simp only [← mul_assoc]
  rw [hcf_A3B3, hcf_A2BC2, hcf_AB3C, hcf_ABCE, hcf_B5, hcf_B3E, hcf_BC3]
  ring


set_option maxHeartbeats 64000000 in
theorem cubicCone_ABCE_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCE610 A B C D E)
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
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoABCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceABCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
      omega
    rw [degreeZeroKappaCubic610_eq_ABCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoABCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceABCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_ABCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoABCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceABCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
      omega
    rw [degreeZeroMuCubic610_eq_ABCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1458 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronCubicNoABCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := omicronCubicFaceABCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_ABCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 486 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerABCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoABCE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceABCE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hAB, hAC, hAE, hDlt⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_ABCE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2916 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_ABCE_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff
  have hpow : E.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner, homicroninner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)



set_option maxHeartbeats 64000000 in
theorem cubicInner_ABDE_identity
    (a b d e : k) :
    ((-23 / 5400 : k) * a ^ 2 * d + (1 / 1350 : k) * b ^ 3) * kappaCubicInnerABDE610 a b d e +
      ((-2 / 675 : k) * a * b ^ 2 + (2 / 225 : k) * b * d) * lambdaCubicInnerABDE610 a b d e +
      ((-1 / 300 : k) * a * d) * muCubicInnerABDE610 a b d e +
      ((-1 / 450 : k) * b ^ 2 + (1 / 75 : k) * e) * omicronCubicInnerABDE610 a b d e +
      ((-1 / 1080 : k) * d) * primitiveCubicInnerABDE610 a b d e =
      d ^ 4 := by
  simp only [kappaCubicInnerABDE610, lambdaCubicInnerABDE610, muCubicInnerABDE610, omicronCubicInnerABDE610, primitiveCubicInnerABDE610]
  ring


end CubicKills610

end Max11DegreeRoutes

end
