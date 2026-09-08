import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart5Scratch

/-! # SPEED: theorems of `Grok810ScaleZeroConeExhaustionSpeedReflValDegScratch`, part 6 of 8, so that no single
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

section ExhaustG0Affine810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupHighG0Rest810_l0_eq_noG0_add_linearTerms
    (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupHighG0Rest810 0 A B C0 D0 E0 F0 G0 =
      rhoBaseGroupHighG0Rest810 0 A B C0 D0 E0 F0 0 +
        rhoBaseG0LinearTerms810 A B C0 D0 E0 F0 G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, rhoBaseGroupHighG0Rest810, rhoBaseG0LinearTerms810, zero_mul,
    mul_zero, zero_smul, smul_zero]
  module


set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupPolynomial810_l0_eq_noG0_add_linear
    (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupPolynomial810 0 A B C0 D0 E0 F0 G0 =
      rhoBaseGroupHighG0Rest810 0 A B C0 D0 E0 F0 0 +
        rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 * G0 := by
  rw [rhoBaseGroupPolynomial810_eq_G02_add_rest,
    rhoBaseGroupHighG0Rest810_l0_eq_noG0_add_linearTerms,
    rhoBaseG0LinearTerms810_eq_coeff_mul]
  simp only [mul_zero, zero_mul, zero_smul, zero_add]


theorem rhoThetaGroupPolynomial810_eq_noG0_add_G0
    (A B C0 D0 E0 G0 : k[X]) :
    rhoThetaGroupPolynomial810 A B C0 D0 E0 G0 =
      rhoThetaGroupPolynomial810 A B C0 D0 E0 0 + G0 := by
  have h1 : (1 / 1 : k) = 1 := by norm_num
  simp only [rhoThetaGroupPolynomial810, h1, one_smul, zero_mul, mul_zero,
    zero_smul, smul_zero]
  abel


set_option maxHeartbeats 400000000 in
/-- Reflected form of `rhoBetaGroupPolynomial810` (23 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoBetaGroupPolynomial810_eq_polyOf_dupfix
    (A B C0 D0 E0 F0 : k[X]) :
    rhoBetaGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (2601 / 1048576 : k), (-(15687 / 262144) : k), (-(189 / 8192) : k),
      (567 / 16384 : k), (1701 / 8192 : k), (273 / 4096 : k),
      (273 / 2048 : k), (483 / 16384 : k), (-(91 / 1024) : k),
      (-(7 / 128) : k), (-(7 / 128) : k), (-(21 / 64) : k),
      (-(77 / 512) : k), (-(21 / 256) : k), (-(77 / 512) : k),
      (-(35 / 256) : k), (7 / 64 : k), (7 / 64 : k),
      (7 / 32 : k), (7 / 32 : k), (7 / 64 : k),
      (7 / 32 : k), (-(7 / 16) : k)]
      [
      [7, 0, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0], [1, 4, 0, 0, 0, 0],
      [2, 2, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0], [3, 1, 0, 1, 0, 0], [4, 0, 0, 0, 1, 0],
      [0, 2, 2, 0, 0, 0], [0, 3, 0, 1, 0, 0], [1, 0, 3, 0, 0, 0], [1, 1, 1, 1, 0, 0],
      [1, 2, 0, 0, 1, 0], [2, 0, 0, 2, 0, 0], [2, 0, 1, 0, 1, 0], [2, 1, 0, 0, 0, 1],
      [0, 0, 1, 2, 0, 0], [0, 0, 2, 0, 1, 0], [0, 1, 0, 1, 1, 0], [0, 1, 1, 0, 0, 1],
      [1, 0, 0, 0, 2, 0], [1, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2]] := by
  simp only [rhoBetaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 16000000 in
theorem rhoBetaGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  rw [speedRefl_rhoBetaGroupPolynomial810_eq_polyOf_dupfix]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `rhoGammaGroupPolynomial810` (17 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoGammaGroupPolynomial810_eq_polyOf_dupfix
    (A B C0 D0 E0 F0 : k[X]) :
    rhoGammaGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (-(765 / 16384) : k), (135 / 1024 : k), (531 / 2048 : k),
      (63 / 1024 : k), (-(27 / 256) : k), (-(39 / 128) : k),
      (-(75 / 256) : k), (-(75 / 256) : k), (-(69 / 256) : k),
      (-(33 / 512) : k), (3 / 16 : k), (3 / 16 : k),
      (3 / 8 : k), (9 / 64 : k), (3 / 8 : k),
      (9 / 32 : k), (-(3 / 4) : k)]
      [
      [5, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0], [3, 1, 1, 0, 0, 0], [4, 0, 0, 1, 0, 0],
      [0, 3, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0], [1, 2, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0],
      [2, 1, 0, 0, 1, 0], [3, 0, 0, 0, 0, 1], [0, 0, 2, 1, 0, 0], [0, 1, 0, 2, 0, 0],
      [0, 1, 1, 0, 1, 0], [0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 1],
      [0, 0, 0, 0, 1, 1]] := by
  simp only [rhoGammaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 16000000 in
theorem rhoGammaGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  rw [speedRefl_rhoGammaGroupPolynomial810_eq_polyOf_dupfix]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `rhoDeltaGroupPolynomial810` (16 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoDeltaGroupPolynomial810_eq_polyOf_dupfix
    (A B C0 D0 E0 F0 : k[X]) :
    rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (-(2805 / 262144) : k), (2925 / 16384 : k), (1395 / 16384 : k),
      (-(135 / 4096) : k), (-(405 / 1024) : k), (-(195 / 1024) : k),
      (-(195 / 512) : k), (-(105 / 1024) : k), (5 / 64 : k),
      (15 / 32 : k), (25 / 128 : k), (15 / 64 : k),
      (25 / 64 : k), (5 / 16 : k), (-(5 / 16) : k),
      (-(5 / 8) : k)]
      [
      [6, 0, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0], [0, 4, 0, 0, 0, 0],
      [1, 2, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0], [2, 1, 0, 1, 0, 0], [3, 0, 0, 0, 1, 0],
      [0, 0, 3, 0, 0, 0], [0, 1, 1, 1, 0, 0], [0, 2, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0],
      [1, 0, 1, 0, 1, 0], [1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0], [0, 0, 0, 1, 0, 1]] := by
  simp only [rhoDeltaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 16000000 in
theorem rhoDeltaGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  rw [speedRefl_rhoDeltaGroupPolynomial810_eq_polyOf_dupfix]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `rhoEpsilonGroupPolynomial810` (11 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoEpsilonGroupPolynomial810_eq_polyOf_dupfix
    (A B C0 D0 E0 F0 : k[X]) :
    rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (51 / 512 : k), (-(9 / 64) : k), (-(27 / 64) : k),
      (-(33 / 256) : k), (1 / 4 : k), (7 / 32 : k),
      (7 / 16 : k), (3 / 8 : k), (5 / 32 : k),
      (-(1 / 2) : k), (-(1 / 2) : k)]
      [
      [4, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0], [2, 1, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0],
      [0, 1, 2, 0, 0, 0], [0, 2, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0], [1, 1, 0, 0, 1, 0],
      [2, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0], [0, 0, 1, 0, 0, 1]] := by
  simp only [rhoEpsilonGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 16000000 in
theorem rhoEpsilonGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  rw [speedRefl_rhoEpsilonGroupPolynomial810_eq_polyOf_dupfix]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `rhoZetaGroupPolynomial810` (10 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoZetaGroupPolynomial810_eq_polyOf_dupfix
    (A B C0 D0 E0 F0 : k[X]) :
    rhoZetaGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (153 / 8192 : k), (-(405 / 2048) : k), (-(63 / 512) : k),
      (27 / 128 : k), (3 / 16 : k), (3 / 8 : k),
      (21 / 128 : k), (-(3 / 16) : k), (-(3 / 8) : k),
      (-(3 / 8) : k)]
      [
      [5, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0],
      [1, 0, 2, 0, 0, 0], [1, 1, 0, 1, 0, 0], [2, 0, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0],
      [0, 0, 1, 0, 1, 0], [0, 1, 0, 0, 0, 1]] := by
  simp only [rhoZetaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 16000000 in
theorem rhoZetaGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  rw [speedRefl_rhoZetaGroupPolynomial810_eq_polyOf_dupfix]
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


end ExhaustG0Affine810

end Max11DegreeRoutes

end
