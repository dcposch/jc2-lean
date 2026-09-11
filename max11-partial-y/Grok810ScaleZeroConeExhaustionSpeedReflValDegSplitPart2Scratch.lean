import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitBaseScratch

/-! # SPEED: theorems of `Grok810ScaleZeroConeExhaustionSpeedReflValDegScratch`, part 2 of 8, so that no single
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

section ExhaustRests810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoAC02_natDegree_lt_of_ABC0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ABC0RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAC02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, htie, h4b, h5b, hD, hE, hF, hG⟩
  unfold degreeZeroXiNoAC02Polynomial810
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil, Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff, hD, hE, hF, hG, Nat.mul_zero]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoAE06_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE06RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAE06Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hEpos, htie, hB, hC, hD, hF, hG⟩
  unfold degreeZeroMuNoAE06Polynomial810
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil, Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff, hB, hC, hD, hF, hG, Nat.mul_zero]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoAE06_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE06RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAE06Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hEpos, htie, hB, hC, hD, hF, hG⟩
  unfold degreeZeroXiNoAE06Polynomial810
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil, Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff, hB, hC, hD, hF, hG, Nat.mul_zero]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoBE02_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BE02RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoBE02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, htie, hA, hC, hD, hF, hG⟩
  unfold degreeZeroMuNoBE02Polynomial810
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil, Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff, hA, hC, hD, hF, hG, Nat.mul_zero]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoBE02_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BE02RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoBE02Polynomial810 l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, htie, hA, hC, hD, hF, hG⟩
  unfold degreeZeroOmicronNoBE02Polynomial810
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil, Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff, hA, hC, hD, hF, hG, Nat.mul_zero]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoAD05_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AD05RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAD05Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hDpos, htie, hB, hC, hE, hF, hG⟩
  unfold degreeZeroMuNoAD05Polynomial810
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil, Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff, hB, hC, hE, hF, hG, Nat.mul_zero]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoAD05_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AD05RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAD05Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hDpos, htie, hB, hC, hE, hF, hG⟩
  unfold degreeZeroXiNoAD05Polynomial810
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil, Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff, hB, hC, hE, hF, hG, Nat.mul_zero]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoC0E0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0E0RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoC0E0Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      2 * C0.natDegree + E0.natDegree := by
  rcases hcone with ⟨hCpos, hEpos, htie, hA, hB, hD, hF, hG⟩
  unfold degreeZeroXiNoC0E0Polynomial810
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil, Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff, hA, hB, hD, hF, hG, Nat.mul_zero]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cone degree bound. -/
private theorem cone810time_part2_degreeZeroMuNoC03Polynomial810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
        [(385 / 65536 : k), (-(385 / 4096) : k), (-(385 / 8192) : k), (-(7245 / 262144 * l) : k), (35 / 2048 : k), (105 / 512 : k), (315 / 8192 * l : k), (105 / 1024 : k), (105 / 512 : k), (945 / 8192 * l : k), (35 / 512 : k), (315 / 8192 * l : k), (-(357 / 8192 * beta) : k), (-(45 / 2048 * gamma) : k), (-(15 / 64) : k), (-(63 / 1024 * l) : k), (-(15 / 128) : k), (-(63 / 1024 * l) : k), (21 / 1024 * beta : k), (-(15 / 128) : k), (-(15 / 64) : k), (-(63 / 512 * l) : k), (-(15 / 64) : k), (-(63 / 512 * l) : k), (63 / 512 * beta : k), (15 / 128 * gamma : k), (-(15 / 128) : k), (-(63 / 1024 * l) : k), (63 / 1024 * beta : k), (15 / 128 * gamma : k), (165 / 1024 * delta : k), (1 / 16 * epsilon : k), (5 / 32 : k), (5 / 16 : k), (9 / 64 * l : k), (5 / 16 : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 32 * gamma) : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 4 * epsilon) : k), (-(15 / 64 * zeta) : k), (-(3 / 32 * eta) : k), (3 / 4 * gamma : k), (5 / 8 * delta : k), (1 / 2 * epsilon : k), (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
        [[6, 0, 0, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [3, 0, 0, 1, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoC03Polynomial810, Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_right, Max11ReflectDeg.mono_nil_left, pow_zero, pow_one, mul_one, one_mul, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0), zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoC03_natDegree_lt_of_BC03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BC03RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, htie, hA, hD, hE, hF, hG⟩
  rw [cone810time_part2_degreeZeroMuNoC03Polynomial810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil, Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff, hA, hD, hE, hF, hG, Nat.mul_zero]
  repeat' apply And.intro
  all_goals omega


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cone degree bound. -/
private theorem cone810time_part2_degreeZeroMuNoB4Polynomial810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuNoB4Polynomial810 l beta gamma delta epsilon zeta eta theta A B C0 D0 E0 F0 G0 =
      Max11ReflectDeg.polyOf [A, B, C0, D0, E0, F0, G0]
        [(385 / 65536 : k), (-(385 / 4096) : k), (-(385 / 8192) : k), (-(7245 / 262144 * l) : k), (105 / 512 : k), (315 / 8192 * l : k), (105 / 1024 : k), (105 / 512 : k), (945 / 8192 * l : k), (35 / 512 : k), (315 / 8192 * l : k), (-(357 / 8192 * beta) : k), (-(45 / 2048 * gamma) : k), (-(5 / 128) : k), (-(15 / 64) : k), (-(63 / 1024 * l) : k), (-(15 / 128) : k), (-(63 / 1024 * l) : k), (21 / 1024 * beta : k), (-(15 / 128) : k), (-(15 / 64) : k), (-(63 / 512 * l) : k), (-(15 / 64) : k), (-(63 / 512 * l) : k), (63 / 512 * beta : k), (15 / 128 * gamma : k), (-(15 / 128) : k), (-(63 / 1024 * l) : k), (63 / 1024 * beta : k), (15 / 128 * gamma : k), (165 / 1024 * delta : k), (1 / 16 * epsilon : k), (5 / 32 : k), (5 / 16 : k), (9 / 64 * l : k), (5 / 16 : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 32 * gamma) : k), (9 / 64 * l : k), (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 8 * epsilon) : k), (-(7 / 64 * beta) : k), (-(3 / 16 * gamma) : k), (-(15 / 64 * delta) : k), (-(1 / 4 * epsilon) : k), (-(15 / 64 * zeta) : k), (-(3 / 32 * eta) : k), (3 / 4 * gamma : k), (5 / 8 * delta : k), (1 / 2 * epsilon : k), (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
        [[6, 0, 0, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [4, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [3, 0, 0, 1, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 1, 0], [2, 0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuNoB4Polynomial810, Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_right, Max11ReflectDeg.mono_nil_left, pow_zero, pow_one, mul_one, one_mul, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0), zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoB4_natDegree_lt_of_BD03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BD03RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, htie, hA, hC, hE, hF, hG⟩
  rw [cone810time_part2_degreeZeroMuNoB4Polynomial810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil, Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, max_lt_iff, hA, hC, hE, hF, hG, Nat.mul_zero]
  repeat' apply And.intro
  all_goals omega


end ExhaustRests810

section ExhaustCombinedDeg810

variable {k : Type*} [Field k] [CharZero k]
set_option maxHeartbeats 64000000 in

theorem muA6Face810_natDegree
    {A : k[X]} (hA : A ≠ 0) :
    (muA6Face810 A).natDegree = 6 * A.natDegree := by
  have hc : (385 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muA6Face810]
  rw [natDegree_smul _ hc, natDegree_pow]
set_option maxHeartbeats 64000000 in


theorem muAC02Combined810_coeff (A C0 : k[X]) (n : ℕ) :
    (muAC02Combined810 A C0).coeff n =
      (385 / 65536 : k) * (A ^ 6).coeff n -
        (385 / 8192 : k) * (A ^ 4 * C0).coeff n +
          (105 / 1024 : k) * (A ^ 2 * C0 ^ 2).coeff n -
            (5 / 128 : k) * (C0 ^ 3).coeff n := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muAC02Combined810, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
  ring


end ExhaustCombinedDeg810

end Max11DegreeRoutes

end
