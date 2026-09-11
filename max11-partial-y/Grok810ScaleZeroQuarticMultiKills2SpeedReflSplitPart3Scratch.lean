import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBasePart27Scratch
import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBasePart29Scratch
import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBasePart32Scratch
import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBasePart33Scratch
import Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitPart2Scratch

/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills2SpeedReflScratch`, part 3 of 4, so that no single
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

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoBDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDEG810 A B C D E F G) :
    (degreeZeroMuQuarticNoBDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroMuQuarticNoBDEG810_eq_polyOf]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroNuQuarticNoBDEG810` (57 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroNuQuarticNoBDEG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroNuQuarticNoBDEG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 4096) : k), (45 / 1024 : k), (15 / 1024 : k),
      (35 / 512 : k), (-(5 / 128) : k), (-(5 / 128) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (-(15 / 128) : k), (5 / 16 : k), (105 / 4194304 * l : k),
      (135 / 262144 * l : k), (9 / 4096 * l : k), (9 / 8192 * l : k),
      (9 / 16384 * l : k), (63 / 4096 * l : k), (315 / 32768 * l : k),
      (9 / 1024 * l : k), (-(9 / 256 * l) : k), (-(9 / 512 * l) : k),
      (-(63 / 1024 * l) : k), (-(63 / 512 * l) : k), (-(21 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 128 * l : k),
      (7 / 65536 * beta : k), (7 / 4096 * beta : k), (-(7 / 16384 * beta) : k),
      (7 / 1024 * beta : k), (7 / 256 * beta : k), (63 / 1024 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (3 / 128 * gamma : k), (5 / 128 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (-(3 / 16 * gamma) : k), (15 / 32768 * delta : k),
      (5 / 1024 * delta : k), (15 / 512 * delta : k), (-(15 / 64 * delta) : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (-(1 / 16 * epsilon) : k),
      (-(1 / 4 * epsilon) : k), (1 / 2 * epsilon : k), (1 / 512 * zeta : k),
      (-(15 / 128 * zeta) : k), (3 / 8 * zeta : k), (-(1 / 32 * eta) : k),
      (1 / 4 * eta : k), (1 / 128 * theta : k), (1 / 8 * theta : k)]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 1, 0, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0],
      [0, 1, 1, 0, 1, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0], [6, 0, 0, 0, 0, 0, 0],
      [4, 0, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0],
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [5, 0, 0, 0, 0, 0, 0],
      [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [degreeZeroNuQuarticNoBDEG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoBDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDEG810 A B C D E F G) :
    (degreeZeroNuQuarticNoBDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      B.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroNuQuarticNoBDEG810_eq_polyOf]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroOmicronQuarticNoBDEG810` (98 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronQuarticNoBDEG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroOmicronQuarticNoBDEG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 65536) : k), (-(45 / 16384) : k), (15 / 16384 : k),
      (-(35 / 2048) : k), (-(5 / 2048) : k), (-(5 / 2048) : k),
      (-(5 / 2048) : k), (25 / 1024 : k), (15 / 512 : k),
      (35 / 1024 : k), (15 / 1024 : k), (135 / 1024 : k),
      (45 / 1024 : k), (-(5 / 128) : k), (-(5 / 128) : k),
      (-(15 / 128) : k), (-(5 / 32) : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (5 / 16 : k), (135 / 33554432 * l : k),
      (225 / 2097152 * l : k), (-(171 / 4194304 * l) : k), (81 / 262144 * l : k),
      (-(9 / 65536 * l) : k), (99 / 131072 * l : k), (-(45 / 131072 * l) : k),
      (-(189 / 65536 * l) : k), (9 / 8192 * l : k), (-(9 / 4096 * l) : k),
      (27 / 8192 * l : k), (45 / 4096 * l : k), (99 / 4096 * l : k),
      (9 / 8192 * l : k), (189 / 8192 * l : k), (567 / 16384 * l : k),
      (9 / 512 * l : k), (-(9 / 256 * l) : k), (-(27 / 1024 * l) : k),
      (-(9 / 128 * l) : k), (-(45 / 512 * l) : k), (-(45 / 1024 * l) : k),
      (-(27 / 512 * l) : k), (9 / 64 * l : k), (9 / 128 * l : k),
      (35 / 2097152 * beta : k), (49 / 131072 * beta : k), (-(35 / 131072 * beta) : k),
      (7 / 8192 * beta : k), (-(7 / 4096 * beta) : k), (21 / 8192 * beta : k),
      (-(91 / 8192 * beta) : k), (-(189 / 32768 * beta) : k), (7 / 512 * beta : k),
      (7 / 512 * beta : k), (35 / 1024 * beta : k), (21 / 256 * beta : k),
      (7 / 512 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (3 / 2048 * gamma : k), (-(9 / 1024 * gamma) : k), (-(3 / 512 * gamma) : k),
      (3 / 128 * gamma : k), (3 / 128 * gamma : k), (9 / 128 * gamma : k),
      (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k), (-(3 / 16 * gamma) : k),
      (9 / 131072 * delta : k), (5 / 4096 * delta : k), (-(5 / 4096 * delta) : k),
      (5 / 128 * delta : k), (5 / 512 * delta : k), (45 / 512 * delta : k),
      (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k), (-(15 / 128 * delta) : k),
      (-(1 / 256 * epsilon) : k), (1 / 32 * epsilon : k), (1 / 32 * epsilon : k),
      (-(1 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k), (-(3 / 16 * epsilon) : k),
      (9 / 32768 * zeta : k), (3 / 1024 * zeta : k), (9 / 512 * zeta : k),
      (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k), (3 / 8 * zeta : k),
      (-(1 / 512 * eta) : k), (-(1 / 32 * eta) : k), (-(3 / 32 * eta) : k),
      (1 / 4 * eta : k), (1 / 1024 * theta : k), (1 / 64 * theta : k),
      (-(3 / 128 * theta) : k), (1 / 8 * theta : k)]
      [
      [3, 3, 0, 0, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0],
      [2, 1, 0, 0, 0, 0, 1], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0],
      [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0], [0, 2, 1, 1, 0, 0, 0],
      [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1],
      [0, 1, 0, 1, 0, 1, 0], [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1],
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0], [2, 0, 1, 0, 1, 0, 0], [1, 2, 0, 0, 1, 0, 0],
      [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1],
      [0, 0, 0, 0, 0, 2, 0], [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0],
      [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0],
      [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0],
      [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0],
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]] := by
  simp only [degreeZeroOmicronQuarticNoBDEG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoBDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDEG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoBDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroOmicronQuarticNoBDEG810_eq_polyOf]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroPiQuarticNoBDEG810` (91 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPiQuarticNoBDEG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPiQuarticNoBDEG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 64 : k), (15 / 256 : k),
      (-(5 / 16) : k), (-(15 / 16) : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (45 / 131072 * l : k),
      (-(3 / 32768 * l) : k), (-(45 / 32768 * l) : k), (9 / 4096 * l : k),
      (9 / 4096 * l : k), (-(27 / 4096 * l) : k), (9 / 4096 * l : k),
      (-(189 / 4096 * l) : k), (-(63 / 4096 * l) : k), (-(27 / 1024 * l) : k),
      (9 / 512 * l : k), (63 / 1024 * l : k), (9 / 128 * l : k),
      (27 / 256 * l : k), (9 / 256 * l : k), (63 / 512 * l : k),
      (189 / 512 * l : k), (63 / 512 * l : k), (-(9 / 64 * l) : k),
      (-(9 / 32 * l) : k), (-(27 / 64 * l) : k), (-(9 / 32 * l) : k),
      (-(27 / 128 * l) : k), (-(9 / 16 * l) : k), (-(3 / 32 * l) : k),
      (9 / 8 * l : k), (7 / 4096 * beta : k), (7 / 4096 * beta : k),
      (-(7 / 1024 * beta) : k), (7 / 512 * beta : k), (7 / 512 * beta : k),
      (-(21 / 256 * beta) : k), (-(7 / 256 * beta) : k), (-(63 / 512 * beta) : k),
      (-(7 / 64 * beta) : k), (7 / 32 * beta : k), (21 / 128 * beta : k),
      (7 / 16 * beta : k), (7 / 32 * beta : k), (7 / 32 * beta : k),
      (-(7 / 8 * beta) : k), (-(3 / 32 * gamma) : k), (-(15 / 256 * gamma) : k),
      (3 / 16 * gamma : k), (3 / 8 * gamma : k), (3 / 4 * gamma : k),
      (1 / 8 * gamma : k), (-(3 / 4 * gamma) : k), (-(3 / 4 * gamma) : k),
      (5 / 512 * delta : k), (-(15 / 256 * delta) : k), (-(5 / 128 * delta) : k),
      (5 / 32 * delta : k), (5 / 32 * delta : k), (15 / 32 * delta : k),
      (15 / 32 * delta : k), (-(5 / 8 * delta) : k), (-(5 / 4 * delta) : k),
      (1 / 4 * epsilon : k), (1 / 2 * epsilon : k), (-(1 / 2 * epsilon) : k),
      (-(1 * epsilon) : k), (-(1 / 2 * epsilon) : k), (3 / 32 * zeta : k),
      (5 / 32 * zeta : k), (-(3 / 8 * zeta) : k), (-(3 / 4 * zeta) : k),
      (-(3 / 4 * zeta) : k), (1 / 16 * eta : k), (-(1 / 2 * eta) : k),
      (-(1 / 4 * eta) : k), (2 * eta : k), (-(1 / 4 * theta) : k),
      (1 * theta : k)]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [4, 1, 1, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0],
      [3, 1, 0, 0, 1, 0, 0], [3, 0, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0],
      [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0],
      [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0],
      [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0],
      [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0],
      [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [3, 1, 1, 0, 0, 0, 0],
      [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0],
      [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0],
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [degreeZeroPiQuarticNoBDEG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoBDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDEG810 A B C D E F G) :
    (degreeZeroPiQuarticNoBDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroPiQuarticNoBDEG810_eq_polyOf]
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


set_option maxHeartbeats 16000000 in
theorem quarticCone_BDEG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDEG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerBDEG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoBDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceBDEG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_BDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerBDEG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoBDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceBDEG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_BDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerBDEG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoBDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceBDEG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (B.natDegree + 2 * D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_BDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerBDEG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoBDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceBDEG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_BDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerBDEG810 B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoBDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceBDEG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * B.natDegree + 2 * D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hBpos, hDpos, hEpos, hGpos, hBD, hBE, hBG, hAlt, hClt, hFlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_BDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_BDEG_identity B.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff
  have hpow : B.leadingCoeff ^ 7 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, homicroninner, hpiinner] at hid
    simpa using hid.symm
  have hlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  exact hlc ((pow_eq_zero_iff (by decide : (7 : ℕ) ≠ 0)).mp hpow)



set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoBDFG810` (33 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoBDFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoBDFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k), (63 / 262144 * l : k), (45 / 8192 * l : k),
      (-(9 / 16384 * l) : k), (27 / 1024 * l : k), (-(9 / 512 * l) : k),
      (9 / 1024 * l : k), (-(63 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 128 * l : k),
      (35 / 32768 * beta : k), (21 / 1024 * beta : k), (7 / 1024 * beta : k),
      (7 / 64 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (7 / 8 * beta : k), (-(3 / 16 * gamma) : k), (3 / 4 * gamma : k),
      (5 / 1024 * delta : k), (5 / 64 * delta : k), (-(15 / 128 * delta) : k),
      (5 / 8 * delta : k), (1 / 2 * epsilon : k), (3 / 128 * zeta : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0],
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroKappaQuarticNoBDFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoBDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroKappaQuarticNoBDFG810_eq_polyOf]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroMuQuarticNoBDFG810` (41 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoBDFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoBDFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (-(5 / 64) : k), (-(5 / 128) : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (-(5 / 128) : k),
      (5 / 16 : k), (5 / 32 : k), (-(45 / 262144 * l) : k),
      (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k), (63 / 8192 * l : k),
      (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k), (-(9 / 512 * l) : k),
      (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (-(7 / 8192 * beta) : k),
      (-(7 / 1024 * beta) : k), (7 / 512 * beta : k), (21 / 1024 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k),
      (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k), (-(5 / 64 * delta) : k),
      (-(15 / 64 * delta) : k), (5 / 8 * delta : k), (-(1 / 8 * epsilon) : k),
      (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k), (3 / 8 * zeta : k),
      (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0],
      [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuQuarticNoBDFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoBDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoBDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroMuQuarticNoBDFG810_eq_polyOf]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroNuQuarticNoBDFG810` (56 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroNuQuarticNoBDFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroNuQuarticNoBDFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 4096) : k), (45 / 1024 : k), (15 / 1024 : k),
      (35 / 512 : k), (-(5 / 128) : k), (-(5 / 128) : k),
      (-(5 / 128) : k), (-(15 / 64) : k), (-(15 / 128) : k),
      (5 / 16 : k), (105 / 4194304 * l : k), (135 / 262144 * l : k),
      (9 / 4096 * l : k), (9 / 8192 * l : k), (9 / 16384 * l : k),
      (63 / 4096 * l : k), (315 / 32768 * l : k), (9 / 1024 * l : k),
      (-(9 / 256 * l) : k), (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k),
      (-(63 / 512 * l) : k), (-(21 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 128 * l : k), (7 / 65536 * beta : k),
      (7 / 4096 * beta : k), (-(7 / 16384 * beta) : k), (7 / 1024 * beta : k),
      (7 / 256 * beta : k), (63 / 1024 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k), (3 / 128 * gamma : k),
      (5 / 128 * gamma : k), (-(3 / 32 * gamma) : k), (-(3 / 16 * gamma) : k),
      (-(3 / 16 * gamma) : k), (15 / 32768 * delta : k), (5 / 1024 * delta : k),
      (15 / 512 * delta : k), (-(15 / 64 * delta) : k), (-(15 / 128 * delta) : k),
      (5 / 8 * delta : k), (-(1 / 16 * epsilon) : k), (-(1 / 4 * epsilon) : k),
      (1 / 2 * epsilon : k), (1 / 512 * zeta : k), (-(15 / 128 * zeta) : k),
      (3 / 8 * zeta : k), (-(1 / 32 * eta) : k), (1 / 4 * eta : k),
      (1 / 128 * theta : k), (1 / 8 * theta : k)]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 1, 0, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0], [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0],
      [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0],
      [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1],
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0],
      [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [degreeZeroNuQuarticNoBDFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoBDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoBDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + F.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroNuQuarticNoBDFG810_eq_polyOf]
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


set_option maxHeartbeats 16000000 in
theorem quarticCone_BDFG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBDFG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerBDFG810 B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoBDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceBDFG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_BDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerBDFG810 B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoBDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceBDFG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_BDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerBDFG810 B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoBDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceBDFG810_coeff_top (hcone := hcone) (hBne := hBne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * B.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hBpos, hDpos, hFpos, hGpos, hBD, hBF, hBG, hAlt, hClt, hElt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_BDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_BDFG_identity B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff
  have hpow : B.leadingCoeff ^ 7 = 0 := by
    rw [hkappainner, hmuinner, hnuinner] at hid
    simpa using hid.symm
  have hlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  exact hlc ((pow_eq_zero_iff (by decide : (7 : ℕ) ≠ 0)).mp hpow)



set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoCDEF810` (33 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoCDEF810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (63 / 262144 * l : k), (45 / 8192 * l : k),
      (-(9 / 16384 * l) : k), (27 / 1024 * l : k), (-(9 / 512 * l) : k),
      (9 / 1024 * l : k), (-(63 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 128 * l : k),
      (35 / 32768 * beta : k), (21 / 1024 * beta : k), (7 / 1024 * beta : k),
      (7 / 64 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (7 / 8 * beta : k), (-(3 / 16 * gamma) : k), (3 / 4 * gamma : k),
      (5 / 1024 * delta : k), (5 / 64 * delta : k), (-(15 / 128 * delta) : k),
      (5 / 8 * delta : k), (1 / 2 * epsilon : k), (3 / 128 * zeta : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0],
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroKappaQuarticNoCDEF810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoCDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEF810 A B C D E F G) :
    (degreeZeroKappaQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      C.natDegree + F.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroKappaQuarticNoCDEF810_eq_polyOf]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroMuQuarticNoCDEF810` (40 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoCDEF810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k), (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k),
      (-(9 / 8192 * l) : k), (63 / 8192 * l : k), (-(9 / 1024 * l) : k),
      (-(9 / 512 * l) : k), (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k),
      (-(63 / 1024 * l) : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k),
      (7 / 512 * beta : k), (21 / 1024 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (3 / 128 * gamma : k),
      (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k),
      (-(5 / 1024 * delta) : k), (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k),
      (5 / 8 * delta : k), (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k),
      (-(3 / 64 * zeta) : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [4, 1, 0, 0, 0, 0, 0],
      [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [3, 1, 0, 0, 0, 0, 0],
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuQuarticNoCDEF810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroMuQuarticNoCDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEF810 A B C D E F G) :
    (degreeZeroMuQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroMuQuarticNoCDEF810_eq_polyOf]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroNuQuarticNoCDEF810` (57 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroNuQuarticNoCDEF810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroNuQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 4096) : k), (45 / 1024 : k), (15 / 1024 : k),
      (35 / 512 : k), (-(5 / 128) : k), (-(5 / 128) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (-(15 / 128) : k), (5 / 16 : k), (105 / 4194304 * l : k),
      (135 / 262144 * l : k), (9 / 4096 * l : k), (9 / 8192 * l : k),
      (9 / 16384 * l : k), (63 / 4096 * l : k), (315 / 32768 * l : k),
      (9 / 1024 * l : k), (-(9 / 256 * l) : k), (-(9 / 512 * l) : k),
      (-(63 / 1024 * l) : k), (-(63 / 512 * l) : k), (-(21 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 128 * l : k),
      (7 / 65536 * beta : k), (7 / 4096 * beta : k), (-(7 / 16384 * beta) : k),
      (7 / 1024 * beta : k), (7 / 256 * beta : k), (63 / 1024 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (3 / 128 * gamma : k), (5 / 128 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (-(3 / 16 * gamma) : k), (15 / 32768 * delta : k),
      (5 / 1024 * delta : k), (15 / 512 * delta : k), (-(15 / 64 * delta) : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (-(1 / 16 * epsilon) : k),
      (-(1 / 4 * epsilon) : k), (1 / 2 * epsilon : k), (1 / 512 * zeta : k),
      (-(15 / 128 * zeta) : k), (3 / 8 * zeta : k), (-(1 / 32 * eta) : k),
      (1 / 4 * eta : k), (1 / 128 * theta : k), (1 / 8 * theta : k)]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 1, 0, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0],
      [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1], [6, 0, 0, 0, 0, 0, 0],
      [4, 0, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0],
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [5, 0, 0, 0, 0, 0, 0],
      [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [degreeZeroNuQuarticNoCDEF810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoCDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEF810 A B C D E F G) :
    (degreeZeroNuQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * C.natDegree + D.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroNuQuarticNoCDEF810_eq_polyOf]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroXiQuarticNoCDEF810` (58 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiQuarticNoCDEF810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroXiQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
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
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 0, 0, 1, 0, 1], [4, 0, 0, 1, 0, 0, 0], [3, 1, 1, 0, 0, 0, 0],
      [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0],
      [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0], [3, 0, 0, 1, 0, 0, 0],
      [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0],
      [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0],
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroXiQuarticNoCDEF810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoCDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEF810 A B C D E F G) :
    (degreeZeroXiQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroXiQuarticNoCDEF810_eq_polyOf]
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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroOmicronQuarticNoCDEF810` (99 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronQuarticNoCDEF810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroOmicronQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 65536) : k), (-(45 / 16384) : k), (15 / 16384 : k),
      (-(35 / 2048) : k), (-(21 / 4096) : k), (-(5 / 2048) : k),
      (-(5 / 2048) : k), (-(5 / 2048) : k), (25 / 1024 : k),
      (15 / 512 : k), (35 / 1024 : k), (15 / 1024 : k),
      (5 / 128 : k), (135 / 1024 : k), (45 / 1024 : k),
      (-(5 / 128) : k), (-(5 / 128) : k), (-(15 / 128) : k),
      (-(5 / 32) : k), (-(5 / 64) : k), (5 / 16 : k),
      (135 / 33554432 * l : k), (225 / 2097152 * l : k), (-(171 / 4194304 * l) : k),
      (81 / 262144 * l : k), (-(9 / 65536 * l) : k), (99 / 131072 * l : k),
      (-(45 / 131072 * l) : k), (-(189 / 65536 * l) : k), (9 / 8192 * l : k),
      (-(9 / 4096 * l) : k), (27 / 8192 * l : k), (45 / 4096 * l : k),
      (99 / 4096 * l : k), (9 / 8192 * l : k), (189 / 8192 * l : k),
      (567 / 16384 * l : k), (9 / 512 * l : k), (-(9 / 256 * l) : k),
      (-(27 / 1024 * l) : k), (-(9 / 128 * l) : k), (-(45 / 512 * l) : k),
      (-(45 / 1024 * l) : k), (-(27 / 512 * l) : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (35 / 2097152 * beta : k), (49 / 131072 * beta : k),
      (-(35 / 131072 * beta) : k), (7 / 8192 * beta : k), (-(7 / 4096 * beta) : k),
      (21 / 8192 * beta : k), (-(91 / 8192 * beta) : k), (-(189 / 32768 * beta) : k),
      (7 / 512 * beta : k), (7 / 512 * beta : k), (35 / 1024 * beta : k),
      (21 / 256 * beta : k), (7 / 512 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (3 / 2048 * gamma : k), (-(9 / 1024 * gamma) : k),
      (-(3 / 512 * gamma) : k), (3 / 128 * gamma : k), (3 / 128 * gamma : k),
      (9 / 128 * gamma : k), (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (9 / 131072 * delta : k), (5 / 4096 * delta : k),
      (-(5 / 4096 * delta) : k), (5 / 128 * delta : k), (5 / 512 * delta : k),
      (45 / 512 * delta : k), (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k),
      (-(15 / 128 * delta) : k), (-(1 / 256 * epsilon) : k), (1 / 32 * epsilon : k),
      (1 / 32 * epsilon : k), (-(1 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k),
      (-(3 / 16 * epsilon) : k), (9 / 32768 * zeta : k), (3 / 1024 * zeta : k),
      (9 / 512 * zeta : k), (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k),
      (3 / 8 * zeta : k), (-(1 / 512 * eta) : k), (-(1 / 32 * eta) : k),
      (-(3 / 32 * eta) : k), (1 / 4 * eta : k), (1 / 1024 * theta : k),
      (1 / 64 * theta : k), (-(3 / 128 * theta) : k), (1 / 8 * theta : k)]
      [
      [3, 3, 0, 0, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0],
      [0, 5, 0, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 1], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0],
      [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0],
      [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 1],
      [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0],
      [0, 0, 0, 0, 0, 1, 1], [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0],
      [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0],
      [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0], [2, 0, 1, 0, 1, 0, 0],
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0], [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0],
      [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0],
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0],
      [2, 2, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0],
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]] := by
  simp only [degreeZeroOmicronQuarticNoCDEF810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoCDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEF810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoCDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * C.natDegree + F.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroOmicronQuarticNoCDEF810_eq_polyOf]
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


set_option maxHeartbeats 16000000 in
theorem quarticCone_CDEF_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCDEF810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerCDEF810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoCDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceCDEF810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (C.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_CDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 16 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerCDEF810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoCDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceCDEF810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_CDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerCDEF810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoCDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceCDEF810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * C.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_CDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerCDEF810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoCDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceCDEF810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * C.natDegree + E.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_CDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerCDEF810 C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoCDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceCDEF810_coeff_top (hcone := hcone) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * C.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hCpos, hDpos, hEpos, hFpos, hCD, hCE, hCF, hAlt, hBlt, hGlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_CDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_CDEF_identity C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
  have hpow : F.leadingCoeff ^ 3 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner] at hid
    simpa using hid.symm
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  exact hlc ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hpow)



end QuarticKills810

end Max11DegreeRoutes

end
