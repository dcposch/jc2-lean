import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart6Scratch

/-! # SPEED: theorems of `Grok810ScaleZeroConeExhaustionSpeedReflValDegScratch`, part 7 of 8, so that no single
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

set_option maxHeartbeats 400000000 in
/-- Reflected form of `rhoEtaGroupPolynomial810` (7 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoEtaGroupPolynomial810_eq_polyOf_dupfix
    (A B C0 D0 E0 F0 : k[X]) :
    rhoEtaGroupPolynomial810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (-(51 / 512) : k), (3 / 64 : k), (9 / 32 : k),
      (9 / 64 : k), (-(1 / 4) : k), (-(1 / 4) : k),
      (-(1 / 4) : k)]
      [
      [3, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0], [2, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0], [0, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 1]] := by
  simp only [rhoEtaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 16000000 in
theorem rhoEtaGroupPolynomial810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  rw [speedRefl_rhoEtaGroupPolynomial810_eq_polyOf_dupfix]
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
/-- Reflected form of `rhoThetaGroupPolynomial810` (7 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoThetaGroupPolynomial810_eq_polyOf_dupfix
    (A B C0 D0 E0 G0 : k[X]) :
    rhoThetaGroupPolynomial810 A B C0 D0 E0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, G0]
      [
      (-(51 / 4096) : k), (9 / 128 : k), (9 / 128 : k),
      (-(1 / 16) : k), (-(1 / 8) : k), (-(1 / 8) : k),
      (1 / 1 : k)]
      [
      [4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0],
      [0, 1, 0, 1, 0, 0], [1, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]] := by
  simp only [rhoThetaGroupPolynomial810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 16000000 in
theorem rhoThetaGroupPolynomial810_noG0_natDegree_le_zero_of_constants
    {A B C0 D0 E0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) :
    (rhoThetaGroupPolynomial810 A B C0 D0 E0 0).natDegree ≤ 0 := by
  rw [speedRefl_rhoThetaGroupPolynomial810_eq_polyOf_dupfix]
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
/-- Reflected form of `rhoBaseGroupHighG0Rest810` (83 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoBaseGroupHighG0Rest810_eq_polyOf_dupfix
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseGroupHighG0Rest810 l A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
      [
      (19635 / 1048576 : k), (369495 / 268435456 * l : k), (-(17115 / 131072) : k),
      (-(315 / 2048) : k), (-(189945 / 4194304 * l) : k), (-(3255 / 131072) : k),
      (-(61425 / 4194304 * l) : k), (315 / 8192 : k), (1575 / 4096 : k),
      (14175 / 262144 * l : k), (6185 / 16384 : k), (6115 / 16384 : k),
      (28161 / 131072 * l : k), (1495 / 8192 : k), (27279 / 524288 * l : k),
      (1425 / 8192 : k), (27279 / 262144 * l : k), (515 / 16384 : k),
      (4977 / 262144 * l : k), (-(265 / 2048) : k), (-(125 / 2048) : k),
      (-(567 / 16384 * l) : k), (-(255 / 1024) : k), (-(375 / 512) : k),
      (-(3339 / 16384 * l) : k), (-(235 / 1024) : k), (-(1071 / 8192 * l) : k),
      (-(735 / 2048) : k), (-(1071 / 16384 * l) : k), (-(735 / 2048) : k),
      (-(705 / 1024) : k), (-(3213 / 8192 * l) : k), (-(165 / 512) : k),
      (-(189 / 1024 * l) : k), (-(455 / 2048) : k), (-(261 / 4096 * l) : k),
      (-(425 / 2048) : k), (-(981 / 8192 * l) : k), (-(255 / 2048) : k),
      (-(459 / 4096 * l) : k), (-(459 / 32768 * l) : k), (15 / 128 : k),
      (63 / 4096 * l : k), (45 / 128 : k), (45 / 128 : k),
      (189 / 1024 * l : k), (85 / 256 : k), (45 / 512 * l : k),
      (85 / 256 : k), (45 / 256 * l : k), (15 / 256 : k),
      (27 / 512 * l : k), (15 / 128 : k), (85 / 128 : k),
      (45 / 256 * l : k), (5 / 16 : k), (171 / 1024 * l : k),
      (5 / 16 : k), (5 / 8 : k), (171 / 512 * l : k),
      (45 / 128 : k), (81 / 256 * l : k), (81 / 1024 * l : k),
      (75 / 256 : k), (81 / 1024 * l : k), (45 / 256 : k),
      (81 / 512 * l : k), (81 / 1024 * l : k), (-(5 / 16) : k),
      (-(5 / 16) : k), (-(9 / 64 * l) : k), (-(5 / 8) : k),
      (-(9 / 64 * l) : k), (-(5 / 16) : k), (-(9 / 32 * l) : k),
      (-(9 / 128 * l) : k), (-(5 / 16) : k), (-(5 / 16) : k),
      (-(9 / 32 * l) : k), (-(9 / 64 * l) : k), (-(5 / 16) : k),
      (-(9 / 64 * l) : k), (-(9 / 64 * l) : k)]
      [
      [7, 1, 0, 0, 0, 0, 0], [8, 0, 0, 0, 0, 0, 0], [4, 3, 0, 0, 0, 0, 0], [5, 1, 1, 0, 0, 0, 0],
      [5, 2, 0, 0, 0, 0, 0], [6, 0, 0, 1, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0],
      [2, 3, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [3, 1, 2, 0, 0, 0, 0], [3, 2, 0, 1, 0, 0, 0],
      [3, 2, 1, 0, 0, 0, 0], [4, 0, 1, 1, 0, 0, 0], [4, 0, 2, 0, 0, 0, 0], [4, 1, 0, 0, 1, 0, 0],
      [4, 1, 0, 1, 0, 0, 0], [5, 0, 0, 0, 0, 1, 0], [5, 0, 0, 0, 1, 0, 0], [0, 3, 2, 0, 0, 0, 0],
      [0, 4, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 3, 0, 0, 0, 0], [1, 2, 1, 1, 0, 0, 0],
      [1, 2, 2, 0, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0], [1, 3, 0, 1, 0, 0, 0], [2, 0, 2, 1, 0, 0, 0],
      [2, 0, 3, 0, 0, 0, 0], [2, 1, 0, 2, 0, 0, 0], [2, 1, 1, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0],
      [2, 2, 0, 0, 0, 1, 0], [2, 2, 0, 0, 1, 0, 0], [3, 0, 0, 1, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0],
      [3, 0, 1, 0, 0, 1, 0], [3, 0, 1, 0, 1, 0, 0], [3, 1, 0, 0, 0, 0, 1], [3, 1, 0, 0, 0, 1, 0],
      [4, 0, 0, 0, 0, 0, 1], [0, 0, 3, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [0, 1, 1, 2, 0, 0, 0],
      [0, 1, 2, 0, 1, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 2, 0, 1, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 2, 1, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1], [0, 3, 0, 0, 0, 1, 0],
      [1, 0, 0, 3, 0, 0, 0], [1, 0, 1, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [1, 0, 2, 0, 0, 1, 0],
      [1, 0, 2, 0, 1, 0, 0], [1, 1, 0, 0, 2, 0, 0], [1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0],
      [1, 1, 1, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 2, 0, 0, 0, 0, 1], [2, 0, 0, 0, 1, 1, 0],
      [2, 0, 0, 0, 2, 0, 0], [2, 0, 0, 1, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0], [2, 0, 1, 0, 0, 0, 1],
      [0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 2, 0, 0, 0, 1],
      [0, 1, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0, 1],
      [1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 1, 0, 1]] := by
  simp only [rhoBaseGroupHighG0Rest810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 16000000 in
theorem rhoBaseGroupHighG0Rest810_noG0_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoBaseGroupHighG0Rest810 0 A B C0 D0 E0 F0 0).natDegree ≤ 0 := by
  rw [speedRefl_rhoBaseGroupHighG0Rest810_eq_polyOf_dupfix]
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
/-- Reflected form of `rhoBaseG0LinearCoeff810` (7 monomials, 6 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_rhoBaseG0LinearCoeff810_eq_polyOf
    (A B C0 D0 E0 F0 : k[X]) :
    rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0]
      [
      (-(255 / 2048) : k), (15 / 256 : k), (45 / 128 : k),
      (45 / 256 : k), (-(5 / 16) : k), (-(5 / 16) : k),
      (-(5 / 16) : k)]
      [
      [3, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0], [2, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0], [0, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 1]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem rhoBaseG0LinearCoeff810_natDegree_le_zero_of_constants
    {A B C0 D0 E0 F0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    (rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0).natDegree ≤ 0 := by
  rw [speedRefl_rhoBaseG0LinearCoeff810_eq_polyOf]
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


theorem degreeZeroPrimitivePolynomial810_l0_eq_C_add_C_mul_G0
    (beta gamma delta epsilon zeta eta theta : k)
    {A B C0 D0 E0 F0 G0 : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0) (hF : F0.natDegree = 0) :
    ∃ c d : k,
      degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 =
        C c + C d * G0 := by
  have hbeta :=
    rhoBetaGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC hD
      hE hF
  have hgamma :=
    rhoGammaGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC hD
      hE hF
  have hdelta :=
    rhoDeltaGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC hD
      hE hF
  have hepsilon :=
    rhoEpsilonGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC
      hD hE hF
  have hzeta :=
    rhoZetaGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC hD
      hE hF
  have heta :=
    rhoEtaGroupPolynomial810_natDegree_le_zero_of_constants hA hB hC hD
      hE hF
  have htheta0 :=
    rhoThetaGroupPolynomial810_noG0_natDegree_le_zero_of_constants hA hB
      hC hD hE
  have hbase0 :=
    rhoBaseGroupHighG0Rest810_noG0_natDegree_le_zero_of_constants hA hB
      hC hD hE hF
  have hlin0 :=
    rhoBaseG0LinearCoeff810_natDegree_le_zero_of_constants hA hB hC hD hE
      hF
  let pconst : k[X] :=
    rhoBaseGroupHighG0Rest810 0 A B C0 D0 E0 F0 0 +
      beta • rhoBetaGroupPolynomial810 A B C0 D0 E0 F0 +
      gamma • rhoGammaGroupPolynomial810 A B C0 D0 E0 F0 +
      delta • rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0 +
      epsilon • rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0 +
      zeta • rhoZetaGroupPolynomial810 A B C0 D0 E0 F0 +
      eta • rhoEtaGroupPolynomial810 A B C0 D0 E0 F0 +
      theta • rhoThetaGroupPolynomial810 A B C0 D0 E0 0
  have hpconst :
      pconst.natDegree ≤ 0 := by
    have h1 := hbase0
    have h2 := natDegree_smul_le_of_le810 beta hbeta
    have h3 := natDegree_smul_le_of_le810 gamma hgamma
    have h4 := natDegree_smul_le_of_le810 delta hdelta
    have h5 := natDegree_smul_le_of_le810 epsilon hepsilon
    have h6 := natDegree_smul_le_of_le810 zeta hzeta
    have h7 := natDegree_smul_le_of_le810 eta heta
    have h8 := natDegree_smul_le_of_le810 theta htheta0
    exact natDegree_add8_le810 h1 h2 h3 h4 h5 h6 h7 h8
  have hlinC :
      rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 =
        C ((rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0).coeff 0) :=
    eq_C_of_natDegree_le_zero hlin0
  have hpC : pconst = C (pconst.coeff 0) :=
    eq_C_of_natDegree_le_zero hpconst
  refine ⟨pconst.coeff 0,
    (rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0).coeff 0 + theta, ?_⟩
  have hprim :
      degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 =
        pconst +
          (rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 + C theta) * G0 := by
    have hthetaG : theta • G0 = C theta * G0 := by rw [smul_eq_C_mul]
    simp only [degreeZeroPrimitivePolynomial810, pconst]
    rw [rhoBaseGroupPolynomial810_l0_eq_noG0_add_linear,
      rhoThetaGroupPolynomial810_eq_noG0_add_G0, smul_add, hthetaG]
    have hdist :
        (rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 + C theta) * G0 =
          rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 * G0 + C theta * G0 :=
      add_mul _ _ _
    rw [hdist]
    abel
  rw [hprim]
  conv_lhs => rw [hpC, hlinC]
  rw [← C_add]


theorem uniqueHighG0DegGtOne_l0_impossible
    (beta gamma delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 F0 G0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighG0DegGtOneL0Cone810 A B C0 D0 E0 F0 G0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial810 0 beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C j) :
    False := by
  rcases hcone with ⟨hG, hA, hB, hC, hD, hE, hF⟩
  obtain ⟨c, d, hform⟩ :=
    degreeZeroPrimitivePolynomial810_l0_eq_C_add_C_mul_G0 beta gamma
      delta epsilon zeta eta theta hA hB hC hD hE hF
  have hder' : C d * G0.derivative = C j := by
    have hcongr := congrArg derivative hform
    have : derivative (C c + C d * G0) = C j := hcongr.symm.trans hder
    simpa [derivative_add, derivative_C, derivative_C_mul] using this
  have hdne : d ≠ 0 := by
    intro hd0
    have : C j = 0 := by
      simpa [hd0, zero_mul] using hder'.symm
    exact hj (C_eq_zero.mp this)
  have hGder : G0.derivative = C (j / d) := by
    have hleft : C d⁻¹ * (C d * G0.derivative) = G0.derivative := by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hdne, C_1, one_mul]
    have hright : C d⁻¹ * C j = C (j / d) := by
      rw [← C_mul, div_eq_inv_mul, mul_comm]
    have hscale := congrArg (fun p : k[X] => C d⁻¹ * p) hder'
    exact hleft.symm.trans (hscale.trans hright)
  have hGdeg :
      G0.natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 G0 (j / d)
      (div_ne_zero hj hdne) hGder
  omega


end ExhaustG0Affine810

section ExhaustClosed810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Remaining cones after this file's named unique faces and Newton
ties.  Unique-`G₀` of degree greater than one with `l = 0` is empty:
the primitive is affine in `G₀`, so `d ρ = C j` forces `deg G₀ = 1`.
Unique-`G₀` of degree one on a source-mapped core is empty by the
parent `uniqueHighG0DegOne_existsPrimitive_false`.  Named leftover:
unique-`G₀` of degree one on mixed-residual letters whose source maps
were dropped by the parent residual, and mixed supports of three or
more nonconstant letters that are not a named unique face or Newton
tie.  The next unused row is the degree-one Jacobian coefficient
already spent on the mapped unique-`G₀` degree-one chamber.  The
theorems `normalized810ScaleZero_impossible` and
`planeKeller810ScaleZeroExclusion_closed` are not claimed. -/
theorem normalized810ScaleZero_coneExhaustionResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      ¬ ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
      (UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0 → l = 0) ∧
      ¬ B5LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AB23RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C03LeadsMixedBPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ D03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ E02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ F02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C0D0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ UniqueG0WithBCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AMaximalCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ E0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ F0LeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
          G0.natDegree = 0) ∧
      ¬ UniqueHighG0DegGtOneL0Cone810 A B C0 D0 E0 F0 G0 ∧
      ¬ A6BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ A6LeadsMuMixedBCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ A6LeadsMuMixedC0Cone810 A B C0 D0 E0 F0 G0 ∧
      ¬ A6LeadsMuMixedD0Cone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AC02RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ ABC0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AE03RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AE06RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BE02RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AD05RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ C0E0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ AF07RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BD03RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
      ¬ BC03RatioTieCone810 A B C0 D0 E0 F0 G0 := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
      hder, hxi, hmu, hom, hARatio, hG0l, hB5, hAB, hCA, hCB, hDA, hE,
      hF, hCD, hGB⟩ :=
    normalized810ScaleZero_coneMixedResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, cXi, cMu, cOm, A, B, C0, D0, E0, F0, G0, ht, hj, hjdiv, hHsq,
    hder, hxi, hmu, hom, hARatio, hG0l, hB5, hAB, hCA, hCB, hDA, hE, hF,
    hCD, hGB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hAmax
    exact xi_A7_impossible_of_A_maximal l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hAmax hxi
  · intro hBleads
    exact omicron_B5_impossible_of_B_leads l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hBleads hom
  · intro hCleads
    exact mu_C03_impossible_of_C0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hCleads hmu
  · intro hDleads
    exact omicron_D03_impossible_of_D0_leads l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hDleads hom
  · intro hEleads
    exact mu_E02_impossible_of_E0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hEleads hmu
  · intro hFleads
    exact xi_F02_impossible_of_F0_leads l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hFleads hxi
  · intro hconst
    exact degreeZeroPrimitivePolynomial810_false_of_constant_core l
      beta gamma delta epsilon zeta eta theta (j / t) A B C0 D0 E0 F0
      G0 hjdiv hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.1
      hconst.2.2.2.2.1 hconst.2.2.2.2.2.1 hconst.2.2.2.2.2.2 hder
  · intro hGgt
    have hl0 : l = 0 := by
      by_contra hlne
      have hGpos : 0 < G0.natDegree := Nat.lt_trans (by decide) hGgt.1
      exact uniqueNonconstantG0_impossible_of_l_ne l beta gamma delta
        epsilon zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hlne hjdiv
        hGgt.2.1 hGgt.2.2.1 hGgt.2.2.2.1 hGgt.2.2.2.2.1
        hGgt.2.2.2.2.2.1 hGgt.2.2.2.2.2.2 hGpos hder
    subst hl0
    exact uniqueHighG0DegGtOne_l0_impossible beta gamma delta epsilon
      zeta eta theta (j / t) A B C0 D0 E0 F0 G0 hjdiv hGgt hder
  · intro hA6B
    exact mu_A6_impossible_of_A6B l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hA6B hmu
  · intro hA6Bm
    exact mu_A6_impossible_of_mixedB l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hA6Bm hmu
  · intro hA6C
    exact mu_A6_impossible_of_mixedC0 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hA6C hmu
  · intro hA6D
    exact mu_A6_impossible_of_mixedD0 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hA6D hmu
  · intro hAC02
    exact mu_xi_AC02_impossible l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hAC02 hmu hxi
  · intro hABC0
    exact mu_xi_ABC0_impossible l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hABC0 hmu hxi
  · intro hAE03
    exact mu_A6_impossible_of_AE03 l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hAE03 hmu
  · intro hAE06
    exact mu_xi_AE06_impossible l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hAE06 hmu hxi
  · intro hBE02
    exact mu_omicron_BE02_impossible l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hBE02 hmu hom
  · intro hAD05
    exact mu_xi_AD05_impossible l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hAD05 hmu hxi
  · intro hC0E0
    exact xi_C0E0_impossible l beta gamma delta epsilon zeta eta theta
      A B C0 D0 E0 F0 G0 hC0E0 hxi
  · intro hAF07
    exact mu_A6_impossible_of_AF07 l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hAF07 hmu
  · intro hBD03
    exact mu_B4_impossible_of_BD03 l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hBD03 hmu
  · intro hBC03
    exact mu_C03_impossible_of_BC03 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hBC03 hmu


theorem normalized810ScaleZero_impossible_of_exhaustionResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hres :
      (∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
          cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
        t ≠ 0 ∧ j ≠ 0 ∧ j / t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
          derivative
              (degreeZeroPrimitivePolynomial810 l beta gamma delta
                epsilon zeta eta theta A B C0 D0 E0 F0 G0) =
            Polynomial.C (j / t) ∧
          (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          ¬ ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
          (UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0 → l = 0) ∧
          ¬ B5LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AB23RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C03LeadsMixedBPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ D03LeadsMixedAPosCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ E02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ F02LeadsMixedCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C0D0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ UniqueG0WithBCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AMaximalCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ D0LeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ E0LeadsMuCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ F0LeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
              D0.natDegree = 0 ∧ E0.natDegree = 0 ∧ F0.natDegree = 0 ∧
              G0.natDegree = 0) ∧
          ¬ UniqueHighG0DegGtOneL0Cone810 A B C0 D0 E0 F0 G0 ∧
          ¬ A6BLeadsOmicronCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ A6LeadsMuMixedBCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ A6LeadsMuMixedC0Cone810 A B C0 D0 E0 F0 G0 ∧
          ¬ A6LeadsMuMixedD0Cone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AC02RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ ABC0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AE03RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AE06RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ BE02RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AD05RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ C0E0RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ AF07RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ BD03RatioTieCone810 A B C0 D0 E0 F0 G0 ∧
          ¬ BC03RatioTieCone810 A B C0 D0 E0 F0 G0) →
        False) :
    False :=
  hres (normalized810ScaleZero_coneExhaustionResidual hsource)


end ExhaustClosed810

end Max11DegreeRoutes

end
