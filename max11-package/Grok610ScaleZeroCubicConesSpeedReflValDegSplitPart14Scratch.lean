import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart13Scratch

/-! # SPEED: theorems of `Grok610ScaleZeroCubicConesSpeedReflValDegScratch`, part 14 of 16, so that no single
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
/-- Reflected form of `degreeZeroOmicronCubicNoBCDE610` (40 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronCubicNoBCDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroOmicronCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 486) : k), (5 / 81 : k), (10 / 81 : k),
      (-(5 / 6912 * l) : k), (1 / 864 * l : k), (-(1 / 288 * l) : k),
      (-(1 / 96 * l) : k), (7 / 96 * l : k), (1 / 24 * l : k),
      (1 / 16 * l : k), (-(1 / 8 * l) : k), (-(1 / 4 * l) : k),
      (-(1 / 8 * l) : k), (-(3 / 16 * l) : k), (4 / 81 * alpha : k),
      (1 / 81 * alpha : k), (-(2 / 27 * alpha) : k), (-(2 / 27 * alpha) : k),
      (-(2 / 9 * alpha) : k), (-(4 / 81 * alpha) : k), (2 / 9 * alpha : k),
      (-(7 / 2592 * beta) : k), (7 / 1296 * beta : k), (7 / 648 * beta : k),
      (-(7 / 216 * beta) : k), (-(7 / 144 * beta) : k), (-(7 / 108 * beta) : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta) : k), (5 / 108 * delta : k),
      (5 / 324 * delta : k), (-(5 / 36 * delta) : k), (1 / 27 * epsilon : k),
      (-(1 / 9 * epsilon) : k), (-(1 / 9 * epsilon) : k), (-(1 / 12 * zeta) : k),
      (-(1 / 6 * zeta) : k), (-(1 / 18 * eta) : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
      [
      [1, 4, 0, 0, 0], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [4, 0, 0, 1, 0],
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


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E) :
    (degreeZeroOmicronCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  rw [speedRefl_degreeZeroOmicronCubicNoBCDE610_eq_polyOf]
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


theorem omicronCubicFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCDE610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (omicronCubicFaceBCDE610 A B C D E).coeff (3 * B.natDegree + D.natDegree) =
      (1 / 486 : k) * omicronCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, omicronCubicFaceBCDE610, omicronCubicInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
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
  simp only [← mul_assoc]
  rw [hcf_B3D, hcf_B2C2, hcf_BDE, hcf_C2E, hcf_CD2]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveCubic610_eq_BCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceBCDE610 A B C D E +
        degreeZeroPrimitiveCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceBCDE610, degreeZeroPrimitiveCubicNoBCDE610]
  all_goals module


set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroPrimitiveCubicNoBCDE610` (71 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPrimitiveCubicNoBCDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroPrimitiveCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 2916) : k), (-(5 / 108) : k), (5 / 324 : k),
      (-(25 / 243) : k), (-(5 / 54) : k), (10 / 27 : k),
      (5 / 27 : k), (5 / 27 : k), (5 / 27648 * l : k),
      (25 / 6912 * l : k), (-(17 / 13824 * l) : k), (1 / 128 * l : k),
      (1 / 288 * l : k), (13 / 576 * l : k), (-(5 / 192 * l) : k),
      (-(1 / 32 * l) : k), (1 / 16 * l : k), (1 / 8 * l : k),
      (3 / 8 * l : k), (1 / 16 * l : k), (3 / 16 * l : k),
      (9 / 32 * l : k), (-(3 / 4 * l) : k), (-(3 / 8 * l) : k),
      (-(3 / 4 * l) : k), (-(1 / 81 * alpha) : k), (-(1 / 27 * alpha) : k),
      (-(1 / 27 * alpha) : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
      (4 / 27 * alpha : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (35 / 62208 * beta : k),
      (49 / 5184 * beta : k), (-(7 / 1728 * beta) : k), (7 / 432 * beta : k),
      (-(7 / 216 * beta) : k), (7 / 144 * beta : k), (35 / 432 * beta : k),
      (35 / 1728 * beta : k), (7 / 36 * beta : k), (-(7 / 36 * beta) : k),
      (-(7 / 72 * beta) : k), (-(7 / 18 * beta) : k), (-(7 / 108 * beta) : k),
      (7 / 12 * beta : k), (1 / 576 * delta : k), (5 / 216 * delta : k),
      (-(5 / 216 * delta) : k), (5 / 36 * delta : k), (5 / 36 * delta : k),
      (-(5 / 12 * delta) : k), (-(1 / 18 * epsilon) : k), (2 / 9 * epsilon : k),
      (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k), (1 / 192 * zeta : k),
      (1 / 24 * zeta : k), (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k),
      (-(1 / 4 * zeta) : k), (-(1 / 36 * eta) : k), (-(1 / 3 * eta) : k),
      (-(1 / 3 * eta) : k), (1 / 72 * theta : k), (1 / 6 * theta : k),
      (-(1 / 12 * theta) : k), (1 * theta : k)]
      [
      [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [1, 3, 1, 0, 0],
      [2, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0], [1, 0, 2, 1, 0],
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


set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveCubicNoBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E) :
    (degreeZeroPrimitiveCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  rw [speedRefl_degreeZeroPrimitiveCubicNoBCDE610_eq_polyOf]
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


theorem primitiveCubicFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCDE610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (primitiveCubicFaceBCDE610 A B C D E).coeff (5 * B.natDegree) =
      (1 / 243 : k) * primitiveCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, primitiveCubicFaceBCDE610, primitiveCubicInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
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
  simp only [← mul_assoc]
  rw [hcf_B5, hcf_B3E, hcf_B2CD, hcf_BC3, hcf_CDE, hcf_D3]
  ring


set_option maxHeartbeats 64000000 in
theorem cubicCone_BCDE_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E)
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
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoBCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceBCDE610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
      omega
    rw [degreeZeroKappaCubic610_eq_BCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 27 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoBCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceBCDE610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_BCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoBCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceBCDE610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
      omega
    rw [degreeZeroMuCubic610_eq_BCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronCubicNoBCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := omicronCubicFaceBCDE610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_BCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 486 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoBCDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceBCDE610_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_BCDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_BCDE_identity B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff
  have hpow : E.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner, homicroninner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)



set_option maxHeartbeats 64000000 in
theorem cubicInner_ABCDE_identity
    (a b c d e : k) :
    ((-1 / 29070 : k) * a ^ 4 * b ^ 2 + (2 / 1995 : k) * a ^ 4 * e + (31 / 67830 : k) * a ^ 3 * b * d + (-83 / 67830 : k) * a ^ 3 * c ^ 2 + (26 / 305235 : k) * a ^ 2 * b ^ 2 * c + (43 / 35910 : k) * a ^ 2 * c * e + (-3631 / 2441880 : k) * a ^ 2 * d ^ 2 + (-319 / 2747115 : k) * a * b ^ 4 + (-2 / 3591 : k) * a * b ^ 2 * e + (3361 / 1017450 : k) * a * b * c * d + (-4586 / 915705 : k) * a * c ^ 3 + (937 / 508725 : k) * a * e ^ 2 + (2339 / 1017450 : k) * b ^ 3 * d + (704 / 80325 : k) * b ^ 2 * c ^ 2 + (-1696 / 508725 : k) * b * d * e + (-1678 / 72675 : k) * c ^ 2 * e + (-22711 / 1017450 : k) * c * d ^ 2) * kappaCubicInnerABCDE610 a b c d e +
      ((872 / 305235 : k) * a * b ^ 2 * d + (-16 / 1995 : k) * a * d * e + (10456 / 4578525 : k) * b ^ 3 * c + (-4412 / 508725 : k) * b * c * e + (-232 / 20349 : k) * b * d ^ 2 + (208 / 101745 : k) * c ^ 2 * d) * lambdaCubicInnerABCDE610 a b c d e +
      ((-1 / 43605 : k) * a ^ 3 * b ^ 2 + (4 / 5985 : k) * a ^ 3 * e + (31 / 101745 : k) * a ^ 2 * b * d + (-83 / 101745 : k) * a ^ 2 * c ^ 2 + (-31 / 17955 : k) * a * c * e + (-137 / 244188 : k) * a * d ^ 2 + (-83 / 13735575 : k) * b ^ 4 + (134 / 1526175 : k) * b ^ 2 * e + (-3 / 6650 : k) * b * c * d + (-104 / 915705 : k) * c ^ 3 + (-1103 / 508725 : k) * e ^ 2) * muCubicInnerABCDE610 a b c d e +
      ((-4 / 855 : k) * a * b * e + (7 / 1530 : k) * b ^ 2 * d + (104 / 14535 : k) * b * c ^ 2 + (-499 / 24225 : k) * d * e) * omicronCubicInnerABCDE610 a b c d e +
      ((-1 / 87210 : k) * a ^ 2 * b ^ 2 + (2 / 5985 : k) * a ^ 2 * e + (31 / 203490 : k) * a * b * d + (-83 / 203490 : k) * a * c ^ 2 + (4 / 17955 : k) * b ^ 2 * c + (-13 / 11970 : k) * c * e + (-1 / 1080 : k) * d ^ 2) * primitiveCubicInnerABCDE610 a b c d e =
      d ^ 5 := by
  simp only [kappaCubicInnerABCDE610, lambdaCubicInnerABCDE610, muCubicInnerABCDE610, omicronCubicInnerABCDE610, primitiveCubicInnerABCDE610]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubic610_eq_ABCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceABCDE610 A B C D E +
        degreeZeroKappaCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaCubic610, kappaCubicFaceABCDE610, degreeZeroKappaCubicNoABCDE610]
  all_goals module


set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroKappaCubicNoABCDE610` (27 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoABCDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
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
      [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1],
      [1, 1, 0, 1, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
      [0, 0, 0, 2, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0],
      [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1],
      [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoABCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCDE610 A B C D E) :
    (degreeZeroKappaCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  rw [speedRefl_degreeZeroKappaCubicNoABCDE610_eq_polyOf]
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


theorem kappaCubicFaceABCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (kappaCubicFaceABCDE610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, kappaCubicFaceABCDE610, kappaCubicInnerABCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2D : ((B ^ 2 * D)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE : ((D * E)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_B2D, hcf_BC2, hcf_DE]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubic610_eq_ABCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceABCDE610 A B C D E +
        degreeZeroLambdaCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroLambdaCubic610, lambdaCubicFaceABCDE610, degreeZeroLambdaCubicNoABCDE610]
  all_goals module


set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroLambdaCubicNoABCDE610` (28 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroLambdaCubicNoABCDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
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
      [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
      [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
      [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0],
      [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoABCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABCDE610 A B C D E) :
    (degreeZeroLambdaCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  rw [speedRefl_degreeZeroLambdaCubicNoABCDE610_eq_polyOf]
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


theorem lambdaCubicFaceABCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABCDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicFaceABCDE610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerABCDE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hAB, hAC, hAD, hAE⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, lambdaCubicFaceABCDE610, lambdaCubicInnerABCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
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
  have hdeg_BCD : ((B * C * D)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    omega
  have hcf_BCD : ((B * C * D)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
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
  rw [hcf_AB2C, hcf_AD2, hcf_B4, hcf_B2E, hcf_BCD, hcf_C3, hcf_E2]
  ring


end CubicKills610

end Max11DegreeRoutes

end
