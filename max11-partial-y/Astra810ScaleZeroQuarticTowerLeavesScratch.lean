import Astra810ScaleZeroQuarticChamberBCDEFG12Part02Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part26Scratch

/-! # Five residual tower leaves for `(8,10)` at scale zero

All five requested leaves are closed by the theorems below.
No requested leaves remain open in this file.
The shared N7 + (1/4) A C kappa auxiliary supplies strict load bands.
The kappa, mu, pi and N6 faces then imply the tracked Open-I identity.
The N6 argument also covers deg(B) = 0 without an extra wall premise.
Only tracked modules are imported. Refined leaf hypotheses are explicit.
The contradiction is a nonzero multiple of F.leadingCoeff * G.leadingCoeff^3.
Every compute_degree target has at most six monomials.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- Degree envelope shared by the five residual leaves. -/
def QuarticTowerLeavesDegrees810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    2 * C.natDegree = A.natDegree + 2 * B.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    G.natDegree = A.natDegree + 2 * B.natDegree ∧
    4 * D.natDegree ≤ A.natDegree + 6 * B.natDegree ∧
    4 * E.natDegree ≤ 3 * A.natDegree + 6 * B.natDegree

set_option maxHeartbeats 64000000 in
/-- The auxiliary retains the degree bound of N7 on this chamber. -/
theorem degreeZeroTowerLeavesAux810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree := by
  have hcone := hc.1
  obtain ⟨ha, hab, hac, had, hae, haf, hag⟩ := hcone
  have hn := degreeZeroN7TowerQuartic810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G
    ha hprim homi hnu hkap
  have hm : ((1 / 4 : k) • (A * C * (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G))).natDegree ≤
      3 * A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have h1 : (A * C * (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤
        (A * C).natDegree + (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    have h2 : (A * C).natDegree ≤ A.natDegree + C.natDegree := natDegree_mul_le
    rw [hkap] at h1
    omega
  exact natDegree_add_le810 hn hm

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestFree1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestFree1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (23 / 8192 : k), (-(5 / 512) : k), (-(125 / 2048) : k),
      (-(265 / 2048) : k), (15 / 256 : k), (85 / 256 : k)]
      [
      [1, 5, 0, 0, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0], [0, 4, 0, 1, 0, 0, 0], [0, 3, 2, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 1, 0]] := by
  simp only [bandAuxBCDEFG12RestFree1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestFree2810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestFree2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (85 / 256 : k), (45 / 128 : k), (45 / 128 : k),
      (-(5 / 16) : k), (-(5 / 16) : k), (15 / 128 : k)]
      [
      [0, 2, 0, 1, 1, 0, 0], [0, 1, 2, 0, 1, 0, 0], [0, 1, 1, 2, 0, 0, 0], [0, 1, 0, 0, 1, 0, 1],
      [0, 1, 0, 0, 0, 2, 0], [0, 0, 3, 1, 0, 0, 0]] := by
  simp only [bandAuxBCDEFG12RestFree2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestFree3810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestFree3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(5 / 8) : k), (-(5 / 16) : k),
      (-(5 / 16) : k), (-(15 / 512) : k)]
      [
      [0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0],
      [1, 2, 1, 1, 0, 0, 0]] := by
  simp only [bandAuxBCDEFG12RestFree3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestL1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (693 / 1048576 * l : k), (-(315 / 2097152 * l) : k), (315 / 131072 * l : k),
      (-(315 / 262144 * l) : k), (2205 / 524288 * l : k), (315 / 32768 * l : k)]
      [
      [6, 0, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0], [4, 1, 0, 1, 0, 0, 0],
      [4, 0, 2, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 1]] := by
  simp only [bandAuxBCDEFG12RestL1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestL2810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(81 / 131072 * l) : k), (-(45 / 8192 * l) : k), (225 / 8192 * l : k),
      (-(45 / 16384 * l) : k), (-(45 / 524288 * l) : k), (-(45 / 16384 * l) : k)]
      [
      [3, 2, 1, 0, 0, 0, 0], [3, 1, 0, 0, 0, 1, 0], [3, 0, 1, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0],
      [2, 4, 0, 0, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0]] := by
  simp only [bandAuxBCDEFG12RestL2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestL3810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 4096 * l) : k), (9 / 8192 * l : k), (27 / 256 * l : k),
      (-(27 / 1024 * l) : k), (81 / 2048 * l : k), (-(27 / 4096 * l) : k)]
      [
      [2, 1, 1, 1, 0, 0, 0], [2, 0, 3, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0],
      [2, 0, 0, 0, 2, 0, 0], [1, 3, 0, 1, 0, 0, 0]] := by
  simp only [bandAuxBCDEFG12RestL3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestL4810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 2048 * l) : k), (-(9 / 512 * l) : k), (9 / 32 * l : k),
      (-(9 / 128 * l) : k), (-(567 / 16384 * l) : k), (27 / 512 * l : k)]
      [
      [1, 2, 2, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 0, 0, 2, 0],
      [0, 4, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0]] := by
  simp only [bandAuxBCDEFG12RestL4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestL5810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 256 * l : k), (45 / 512 * l : k), (189 / 1024 * l : k),
      (-(9 / 64 * l) : k), (-(9 / 32 * l) : k), (63 / 4096 * l : k)]
      [
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1],
      [0, 1, 0, 0, 1, 1, 0], [0, 0, 4, 0, 0, 0, 0]] := by
  simp only [bandAuxBCDEFG12RestL5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestL6810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 128 * l) : k), (-(9 / 32 * l) : k), (-(9 / 64 * l) : k),
      (-(9 / 64 * l) : k), (9 / 16 * l : k)]
      [
      [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0],
      [0, 0, 0, 0, 0, 0, 2]] := by
  simp only [bandAuxBCDEFG12RestL6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestBeta1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestBeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (315 / 131072 * beta : k), (-(35 / 65536 * beta) : k), (35 / 4096 * beta : k),
      (-(35 / 8192 * beta) : k), (175 / 16384 * beta : k), (-(7 / 16384 * beta) : k)]
      [
      [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0],
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0]] := by
  simp only [bandAuxBCDEFG12RestBeta1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestBeta2810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestBeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 1024 * beta : k), (-(21 / 2048 * beta) : k), (49 / 32768 * beta : k),
      (-(7 / 1024 * beta) : k), (7 / 128 * beta : k), (-(7 / 128 * beta) : k)]
      [
      [2, 0, 1, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0],
      [1, 0, 0, 0, 2, 0, 0], [0, 3, 0, 1, 0, 0, 0]] := by
  simp only [bandAuxBCDEFG12RestBeta2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestBeta3810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestBeta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(91 / 1024 * beta) : k), (7 / 32 * beta : k), (7 / 32 * beta : k),
      (7 / 64 * beta : k), (7 / 64 * beta : k), (-(7 / 16 * beta) : k)]
      [
      [0, 2, 2, 0, 0, 0, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]] := by
  simp only [bandAuxBCDEFG12RestBeta3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestBeta4810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestBeta4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 64 * beta) : k), (-(21 / 1024 * beta) : k), (35 / 1024 * beta : k),
      (7 / 32 * beta : k)]
      [
      [1, 0, 0, 1, 0, 1, 0], [2, 1, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 1], [1, 0, 1, 0, 0, 0, 1]] := by
  simp only [bandAuxBCDEFG12RestBeta4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestGamma1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestGamma1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(27 / 256 * gamma) : k), (9 / 64 * gamma : k), (3 / 8 * gamma : k),
      (3 / 16 * gamma : k), (3 / 16 * gamma : k), (-(3 / 4 * gamma) : k)]
      [
      [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]] := by
  simp only [bandAuxBCDEFG12RestGamma1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestDelta1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestDelta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 4096 * delta : k), (-(15 / 8192 * delta) : k), (15 / 512 * delta : k),
      (-(15 / 1024 * delta) : k), (45 / 2048 * delta : k), (-(5 / 1024 * delta) : k)]
      [
      [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0],
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0]] := by
  simp only [bandAuxBCDEFG12RestDelta1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestDelta2810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestDelta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 64 * delta : k), (-(5 / 128 * delta) : k), (-(135 / 4096 * delta) : k),
      (25 / 128 * delta : k), (15 / 32 * delta : k), (5 / 64 * delta : k)]
      [
      [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0]] := by
  simp only [bandAuxBCDEFG12RestDelta2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestDelta3810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestDelta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 8 * delta) : k), (-(5 / 16 * delta) : k), (-(5 / 64 * delta) : k),
      (15 / 128 * delta : k)]
      [
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [1, 1, 0, 0, 0, 1, 0], [2, 0, 0, 0, 0, 0, 1]] := by
  simp only [bandAuxBCDEFG12RestDelta3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestEpsilon1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestEpsilon1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 32 * epsilon : k), (1 / 4 * epsilon : k), (-(1 / 2 * epsilon) : k),
      (-(1 / 2 * epsilon) : k)]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]] := by
  simp only [bandAuxBCDEFG12RestEpsilon1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestZeta1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestZeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 * zeta : k), (-(3 / 512 * zeta) : k), (3 / 32 * zeta : k),
      (-(3 / 64 * zeta) : k), (27 / 128 * zeta : k), (-(3 / 8 * zeta) : k)]
      [
      [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0]] := by
  simp only [bandAuxBCDEFG12RestZeta1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestZeta2810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestZeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 8 * zeta) : k), (-(3 / 16 * zeta) : k), (3 / 128 * zeta : k),
      (3 / 8 * zeta : k)]
      [
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1]] := by
  simp only [bandAuxBCDEFG12RestZeta2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestEta1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestEta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 64 * eta : k), (-(1 / 4 * eta) : k), (-(1 / 4 * eta) : k)]
      [
      [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]] := by
  simp only [bandAuxBCDEFG12RestEta1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_bandAuxBCDEFG12RestTheta1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestTheta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 32 * theta : k), (-(1 / 64 * theta) : k), (1 / 4 * theta : k),
      (-(1 / 8 * theta) : k), (-(1 / 16 * theta) : k), (1 / 1 * theta : k)]
      [
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]] := by
  simp only [bandAuxBCDEFG12RestTheta1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Every non-pure auxiliary monomial is strictly below the candidate pure load degree, including equality at the old tower face. -/
theorem towerLeavesAuxRest810_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hd : 5 * A.natDegree + 8 * B.natDegree ≤ 2 * d)
    (hl : l = 0 ∨ 8 * A.natDegree ≤ d)
    (hbeta : beta = 0 ∨ 7 * A.natDegree ≤ d)
    (hdelta : delta = 0 ∨ 6 * A.natDegree ≤ d)
    (hzeta : zeta = 0 ∨ 5 * A.natDegree ≤ d)
    (htheta : theta = 0 ∨ 4 * A.natDegree ≤ d)
    : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  simp only [QuarticTowerLeavesDegrees810, QuarticRatioConeA810] at hc
  rcases hc with ⟨⟨ha, hab, hac, had, hae, haf, hag⟩,
    h0, h1, h2, h3, h4⟩
  have hc0 : (bandAuxBCDEFG12RestFree1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra810t_front_bandAuxBCDEFG12RestFree1810_eq_polyOf]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc1 : (bandAuxBCDEFG12RestFree2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra810t_front_bandAuxBCDEFG12RestFree2810_eq_polyOf]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc2 : (bandAuxBCDEFG12RestFree3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra810t_front_bandAuxBCDEFG12RestFree3810_eq_polyOf]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc3 : (bandAuxBCDEFG12RestL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestL1810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc4 : (bandAuxBCDEFG12RestL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestL2810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc5 : (bandAuxBCDEFG12RestL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestL3810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc6 : (bandAuxBCDEFG12RestL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL4810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestL4810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc7 : (bandAuxBCDEFG12RestL5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL5810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestL5810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc8 : (bandAuxBCDEFG12RestL6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL6810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestL6810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc9 : (bandAuxBCDEFG12RestBeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestBeta1810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc10 : (bandAuxBCDEFG12RestBeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestBeta2810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc11 : (bandAuxBCDEFG12RestBeta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestBeta3810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc12 : (bandAuxBCDEFG12RestBeta4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta4810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestBeta4810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc13 : (bandAuxBCDEFG12RestGamma1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra810t_front_bandAuxBCDEFG12RestGamma1810_eq_polyOf]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc14 : (bandAuxBCDEFG12RestDelta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    · simp only [bandAuxBCDEFG12RestDelta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestDelta1810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc15 : (bandAuxBCDEFG12RestDelta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    · simp only [bandAuxBCDEFG12RestDelta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestDelta2810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc16 : (bandAuxBCDEFG12RestDelta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    · simp only [bandAuxBCDEFG12RestDelta3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestDelta3810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc17 : (bandAuxBCDEFG12RestEpsilon1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra810t_front_bandAuxBCDEFG12RestEpsilon1810_eq_polyOf]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc18 : (bandAuxBCDEFG12RestZeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hzeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestZeta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestZeta1810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc19 : (bandAuxBCDEFG12RestZeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hzeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestZeta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestZeta2810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc20 : (bandAuxBCDEFG12RestEta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra810t_front_bandAuxBCDEFG12RestEta1810_eq_polyOf]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add, max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc21 : (bandAuxBCDEFG12RestTheta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases htheta with hz | hdload
    · simp only [bandAuxBCDEFG12RestTheta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · rw [astra810t_front_bandAuxBCDEFG12RestTheta1810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - ha hab hac had hae haf hag h0 h1 h2 h3 h4 hd hdload
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  simp only [bandAuxBCDEFG12Rest810]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc0 hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9) hc10) hc11) hc12) hc13) hc14) hc15) hc16) hc17) hc18) hc19) hc20) hc21)

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills l whenever its pure-A term reaches the old tower face. -/
theorem quarticTowerLeaves_l_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 11 * A.natDegree)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    l = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 8 * A.natDegree := by
    apply towerLeavesAuxRest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticBetaTowerFace810 beta A + n7QuarticDeltaTowerFace810 delta A + n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 8 * A.natDegree := by
    simp only [S, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticLTowerFace810 l A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    dsimp [S]
    abel
  have hlead : (n7QuarticLTowerFace810 l A).natDegree = 8 * A.natDegree := by
    simp only [n7QuarticLTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills beta whenever its pure-A term reaches the old tower face. -/
theorem quarticTowerLeaves_beta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 9 * A.natDegree)
    (hl0 : l = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    beta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
    apply towerLeavesAuxRest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticDeltaTowerFace810 delta A + n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 7 * A.natDegree := by
    simp only [S, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticBetaTowerFace810 beta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, n7QuarticLTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticBetaTowerFace810 beta A).natDegree = 7 * A.natDegree := by
    simp only [n7QuarticBetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills delta whenever its pure-A term reaches the old tower face. -/
theorem quarticTowerLeaves_delta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 7 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    delta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
    apply towerLeavesAuxRest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 6 * A.natDegree := by
    simp only [S, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticDeltaTowerFace810 delta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticDeltaTowerFace810 delta A).natDegree = 6 * A.natDegree := by
    simp only [n7QuarticDeltaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills zeta whenever its pure-A term reaches the old tower face. -/
theorem quarticTowerLeaves_zeta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 5 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    zeta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
    apply towerLeavesAuxRest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inl hdelta0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 5 * A.natDegree := by
    simp only [S, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticZetaTowerFace810 zeta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, hdelta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticZetaTowerFace810 zeta A).natDegree = 5 * A.natDegree := by
    simp only [n7QuarticZetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills theta whenever its pure-A term reaches the old tower face. -/
theorem quarticTowerLeaves_theta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 3 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (hzeta0 : zeta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    theta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
    apply towerLeavesAuxRest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inl hdelta0
    · exact Or.inl hzeta0
    · exact Or.inr (by omega)
  have hrem := hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticThetaTowerFace810 theta A +
      (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, hdelta0, hzeta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
  have hlead : (n7QuarticThetaTowerFace810 theta A).natDegree = 4 * A.natDegree := by
    simp only [n7QuarticThetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- Strict bands for all five pure-A loads throughout the common degree envelope. -/
theorem quarticTowerLeaves_loadBands810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) ∧
    (beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) ∧
    (delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) ∧
    (zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree) ∧
    (theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) := by
  have haux := degreeZeroTowerLeavesAux810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G
    hc hprim homi hnu hkap
  have hl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 11 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      exact quarticTowerLeaves_l_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) haux
  have hbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 9 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      exact quarticTowerLeaves_beta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 haux
  have hdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 7 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      have hbeta0 : beta = 0 := by
        rcases hbeta with hz | hh
        · exact hz
        · omega
      exact quarticTowerLeaves_delta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 hbeta0 haux
  have hzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 5 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      have hbeta0 : beta = 0 := by
        rcases hbeta with hz | hh
        · exact hz
        · omega
      have hdelta0 : delta = 0 := by
        rcases hdelta with hz | hh
        · exact hz
        · omega
      exact quarticTowerLeaves_zeta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 hbeta0 hdelta0 haux
  have htheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 3 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      have hbeta0 : beta = 0 := by
        rcases hbeta with hz | hh
        · exact hz
        · omega
      have hdelta0 : delta = 0 := by
        rcases hdelta with hz | hh
        · exact hz
        · omega
      have hzeta0 : zeta = 0 := by
        rcases hzeta with hz | hh
        · exact hz
        · omega
      exact quarticTowerLeaves_theta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 hbeta0 hdelta0 hzeta0 haux
  exact ⟨hl, hbeta, hdelta, hzeta, htheta⟩


set_option maxHeartbeats 64000000 in
/-- The homogeneous Open-I polynomial face. -/
def towerLeavesOpenIKappaFace810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3) +
    (-15 / 128 : k) • (B * C ^ 2) +
    (5 / 16 : k) • (B * G) +
    (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def towerLeavesOpenIKappaRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-15 / 128 : k) • (B ^ 2 * D) +
    (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIKappaRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * l : k) • (A ^ 5) +
    (45 / 8192 * l : k) • (A ^ 3 * C) +
    (-9 / 16384 * l : k) • (A ^ 2 * B ^ 2) +
    (27 / 1024 * l : k) • (A ^ 2 * E) +
    (-9 / 512 * l : k) • (A * B * D) +
    (9 / 1024 * l : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def towerLeavesOpenIKappaRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 64 * l : k) • (A * G) +
    (-63 / 1024 * l : k) • (B ^ 2 * C) +
    (9 / 64 * l : k) • (B * F) +
    (9 / 64 * l : k) • (C * E) +
    (9 / 128 * l : k) • (D ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIKappaRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * beta : k) • (A ^ 4) +
    (21 / 1024 * beta : k) • (A ^ 2 * C) +
    (7 / 1024 * beta : k) • (A * B ^ 2) +
    (7 / 64 * beta : k) • (A * E) +
    (-7 / 64 * beta : k) • (B * D) +
    (-7 / 128 * beta : k) • (C ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomials. -/
def towerLeavesOpenIKappaRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 8 * beta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def towerLeavesOpenIKappaRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 16 * gamma : k) • (B * C) +
    (3 / 4 * gamma : k) • (F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def towerLeavesOpenIKappaRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 1024 * delta : k) • (A ^ 3) +
    (5 / 64 * delta : k) • (A * C) +
    (-15 / 128 * delta : k) • (B ^ 2) +
    (5 / 8 * delta : k) • (E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomials. -/
def towerLeavesOpenIKappaRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 2 * epsilon : k) • (D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def towerLeavesOpenIKappaRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * zeta : k) • (A ^ 2) +
    (3 / 8 * zeta : k) • (C)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomials. -/
def towerLeavesOpenIKappaRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • (B)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomials. -/
def towerLeavesOpenIKappaRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • (A)

set_option maxHeartbeats 64000000 in
/-- The remainder after the homogeneous face. -/
def towerLeavesOpenIKappaRest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  towerLeavesOpenIKappaRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIKappaRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIKappaRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIKappaRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIKappaRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIKappaRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIKappaRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIKappaRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIKappaRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIKappaRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIKappaRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The carrier splits exactly into face and remainder. -/
theorem towerLeavesOpenIKappasplit810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      towerLeavesOpenIKappaFace810 A B C D E F G + towerLeavesOpenIKappaRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, towerLeavesOpenIKappaFace810, towerLeavesOpenIKappaRest810, towerLeavesOpenIKappaRest0810, towerLeavesOpenIKappaRest1810, towerLeavesOpenIKappaRest2810, towerLeavesOpenIKappaRest3810, towerLeavesOpenIKappaRest4810, towerLeavesOpenIKappaRest5810, towerLeavesOpenIKappaRest6810, towerLeavesOpenIKappaRest7810, towerLeavesOpenIKappaRest8810, towerLeavesOpenIKappaRest9810, towerLeavesOpenIKappaRest10810]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest0810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIKappaRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
]
      [
] := by
  simp only [towerLeavesOpenIKappaRest0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest0810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIKappaRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-15 / 128 : k), (5 / 16 : k)]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest1810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIKappaRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * l : k), (45 / 8192 * l : k), (-9 / 16384 * l : k),
      (27 / 1024 * l : k), (9 / 1024 * l : k)]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 0, 2, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIKappaRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * l : k), (45 / 8192 * l : k), (-9 / 16384 * l : k),
      (27 / 1024 * l : k), (-9 / 512 * l : k), (9 / 1024 * l : k)]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest2810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIKappaRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 64 * l : k), (-63 / 1024 * l : k), (9 / 64 * l : k),
      (9 / 64 * l : k)]
      [
      [1, 0, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest2810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIKappaRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 64 * l : k), (-63 / 1024 * l : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 128 * l : k)]
      [
      [1, 0, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest3810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIKappaRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 32768 * beta : k), (21 / 1024 * beta : k), (7 / 1024 * beta : k),
      (7 / 64 * beta : k), (-7 / 128 * beta : k)]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 0, 2, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest3810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIKappaRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 32768 * beta : k), (21 / 1024 * beta : k), (7 / 1024 * beta : k),
      (7 / 64 * beta : k), (-7 / 64 * beta : k), (-7 / 128 * beta : k)]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest4810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIKappaRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 8 * beta : k)]
      [
      [0, 0, 0, 0, 0, 0, 1]] := by
  simp only [towerLeavesOpenIKappaRest4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest4810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIKappaRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 8 * beta : k)]
      [
      [0, 0, 0, 0, 0, 0, 1]] := by
  simp only [towerLeavesOpenIKappaRest4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest5810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIKappaRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 16 * gamma : k), (3 / 4 * gamma : k)]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [towerLeavesOpenIKappaRest5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest5810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIKappaRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 16 * gamma : k), (3 / 4 * gamma : k)]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [towerLeavesOpenIKappaRest5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest6810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIKappaRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 1024 * delta : k), (5 / 64 * delta : k), (-15 / 128 * delta : k),
      (5 / 8 * delta : k)]
      [
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest6810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIKappaRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 1024 * delta : k), (5 / 64 * delta : k), (-15 / 128 * delta : k),
      (5 / 8 * delta : k)]
      [
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest7810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIKappaRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
]
      [
] := by
  simp only [towerLeavesOpenIKappaRest7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest7810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIKappaRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 2 * epsilon : k)]
      [
      [0, 0, 0, 1, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest8810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIKappaRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 128 * zeta : k), (3 / 8 * zeta : k)]
      [
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest8810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIKappaRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 128 * zeta : k), (3 / 8 * zeta : k)]
      [
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest9810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIKappaRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * eta : k)]
      [
      [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest9810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIKappaRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * eta : k)]
      [
      [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest10810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIKappaRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)]
      [
      [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIKappaRest10810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIKappaRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)]
      [
      [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIKappaRest10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- The strict bands put every remainder chunk below the face. -/
theorem towerLeavesOpenIKapparest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (towerLeavesOpenIKappaRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
  rcases hc with ⟨⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩, hCEq, hFEq, hGEq, hDbound, hEbound⟩
  have hr0 : (towerLeavesOpenIKappaRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIKappaRest0810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIKappaRest0810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr1 : (towerLeavesOpenIKappaRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIKappaRest1810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest1810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIKappaRest1810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest1810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr2 : (towerLeavesOpenIKappaRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIKappaRest2810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest2810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIKappaRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest2810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr3 : (towerLeavesOpenIKappaRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIKappaRest3810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest3810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIKappaRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest3810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr4 : (towerLeavesOpenIKappaRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIKappaRest4810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest4810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIKappaRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest4810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr5 : (towerLeavesOpenIKappaRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIKappaRest5810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIKappaRest5810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr6 : (towerLeavesOpenIKappaRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbdelta with hz | hb
      · simp only [towerLeavesOpenIKappaRest6810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest6810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbdelta with hz | hb
      · simp only [towerLeavesOpenIKappaRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest6810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr7 : (towerLeavesOpenIKappaRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIKappaRest7810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIKappaRest7810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr8 : (towerLeavesOpenIKappaRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbzeta with hz | hb
      · simp only [towerLeavesOpenIKappaRest8810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest8810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbzeta with hz | hb
      · simp only [towerLeavesOpenIKappaRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest8810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr9 : (towerLeavesOpenIKappaRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIKappaRest9810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIKappaRest9810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr10 : (towerLeavesOpenIKappaRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbtheta with hz | hb
      · simp only [towerLeavesOpenIKappaRest10810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest10810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbtheta with hz | hb
      · simp only [towerLeavesOpenIKappaRest10810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIKappaRest10810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  unfold towerLeavesOpenIKappaRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10)

set_option maxHeartbeats 64000000 in
/-- Coefficient of the homogeneous face at its common degree. -/
theorem towerLeavesOpenIKappaface_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    (towerLeavesOpenIKappaFace810 A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) =
      (5 / 512 : k) * kappaQuarticOpenIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hc with ⟨⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩, hCEq, hFEq, hGEq, hDbound, hEbound⟩
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A * B ^ 3).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    try simp only [natDegree_pow]
    all_goals omega
  have hm0 : (A * B ^ 3).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (B * C ^ 2).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    try simp only [natDegree_pow]
    all_goals omega
  have hm1 : (B * C ^ 2).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (B * G).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    try simp only [natDegree_pow]
    all_goals omega
  have hm2 : (B * G).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C * F).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    try simp only [natDegree_pow]
    all_goals omega
  have hm3 : (C * F).coeff (A.natDegree + 3 * B.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [towerLeavesOpenIKappaFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, kappaQuarticOpenIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar Open-I face vanishes. -/
theorem towerLeavesOpenIKappaFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    kappaQuarticOpenIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := towerLeavesOpenIKapparest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta
  have ht := towerLeavesOpenIKappaface_coeff810 A B C D E F G hc hDle hEle hBne hCne hFne hGne
  have hd : 0 < A.natDegree + 3 * B.natDegree := by
    rcases hc with ⟨⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩, hCEq, hFEq, hGEq, hDbound, hEbound⟩
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree by omega)
  rw [towerLeavesOpenIKappasplit810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

set_option maxHeartbeats 64000000 in
/-- The homogeneous Open-I polynomial face. -/
def towerLeavesOpenIMuFace810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C) +
    (-5 / 64 : k) • (A * B * F) +
    (-5 / 128 : k) • (C ^ 3) +
    (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIMuRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 128 : k) • (A * D ^ 2) +
    (35 / 2048 : k) • (B ^ 4) +
    (-15 / 128 : k) • (B ^ 2 * E) +
    (-15 / 64 : k) • (B * C * D) +
    (5 / 16 : k) • (D * F) +
    (5 / 32 : k) • (E ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIMuRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-45 / 262144 * l : k) • (A ^ 4 * B) +
    (-9 / 8192 * l : k) • (A ^ 3 * D) +
    (-9 / 8192 * l : k) • (A ^ 2 * B * C) +
    (-9 / 1024 * l : k) • (A ^ 2 * F) +
    (63 / 8192 * l : k) • (A * B ^ 3) +
    (-9 / 512 * l : k) • (A * B * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIMuRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-9 / 512 * l : k) • (A * C * D) +
    (-63 / 1024 * l : k) • (B ^ 2 * D) +
    (-63 / 1024 * l : k) • (B * C ^ 2) +
    (9 / 64 * l : k) • (B * G) +
    (9 / 64 * l : k) • (C * F) +
    (9 / 64 * l : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIMuRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 8192 * beta : k) • (A ^ 3 * B) +
    (-7 / 1024 * beta : k) • (A ^ 2 * D) +
    (7 / 512 * beta : k) • (A * B * C) +
    (-7 / 64 * beta : k) • (A * F) +
    (21 / 1024 * beta : k) • (B ^ 3) +
    (-7 / 64 * beta : k) • (B * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomials. -/
def towerLeavesOpenIMuRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 64 * beta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def towerLeavesOpenIMuRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * gamma : k) • (A * B ^ 2) +
    (-3 / 16 * gamma : k) • (B * D) +
    (-3 / 32 * gamma : k) • (C ^ 2) +
    (3 / 4 * gamma : k) • (G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def towerLeavesOpenIMuRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 1024 * delta : k) • (A ^ 2 * B) +
    (-5 / 64 * delta : k) • (A * D) +
    (-15 / 64 * delta : k) • (B * C) +
    (5 / 8 * delta : k) • (F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def towerLeavesOpenIMuRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 8 * epsilon : k) • (B ^ 2) +
    (1 / 2 * epsilon : k) • (E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def towerLeavesOpenIMuRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 64 * zeta : k) • (A * B) +
    (3 / 8 * zeta : k) • (D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomials. -/
def towerLeavesOpenIMuRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • (C)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomials. -/
def towerLeavesOpenIMuRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • (B)

set_option maxHeartbeats 64000000 in
/-- The remainder after the homogeneous face. -/
def towerLeavesOpenIMuRest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  towerLeavesOpenIMuRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIMuRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIMuRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIMuRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIMuRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIMuRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIMuRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIMuRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIMuRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIMuRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIMuRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The carrier splits exactly into face and remainder. -/
theorem towerLeavesOpenIMusplit810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      towerLeavesOpenIMuFace810 A B C D E F G + towerLeavesOpenIMuRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroMuQuartic810, towerLeavesOpenIMuFace810, towerLeavesOpenIMuRest810, towerLeavesOpenIMuRest0810, towerLeavesOpenIMuRest1810, towerLeavesOpenIMuRest2810, towerLeavesOpenIMuRest3810, towerLeavesOpenIMuRest4810, towerLeavesOpenIMuRest5810, towerLeavesOpenIMuRest6810, towerLeavesOpenIMuRest7810, towerLeavesOpenIMuRest8810, towerLeavesOpenIMuRest9810, towerLeavesOpenIMuRest10810]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest0810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIMuRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2048 : k), (-15 / 128 : k), (5 / 32 : k)]
      [
      [0, 4, 0, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest0810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIMuRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-5 / 128 : k), (35 / 2048 : k), (-15 / 128 : k),
      (-15 / 64 : k), (5 / 16 : k), (5 / 32 : k)]
      [
      [1, 0, 0, 2, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest1810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIMuRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-45 / 262144 * l : k), (-9 / 8192 * l : k), (-9 / 1024 * l : k),
      (63 / 8192 * l : k), (-9 / 512 * l : k)]
      [
      [4, 1, 0, 0, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 3, 0, 0, 0, 0, 0],
      [1, 1, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIMuRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-45 / 262144 * l : k), (-9 / 8192 * l : k), (-9 / 8192 * l : k),
      (-9 / 1024 * l : k), (63 / 8192 * l : k), (-9 / 512 * l : k)]
      [
      [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest2810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIMuRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-63 / 1024 * l : k), (9 / 64 * l : k), (9 / 64 * l : k)]
      [
      [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0]] := by
  simp only [towerLeavesOpenIMuRest2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest2810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIMuRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-9 / 512 * l : k), (-63 / 1024 * l : k), (-63 / 1024 * l : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k)]
      [
      [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest3810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIMuRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-7 / 8192 * beta : k), (7 / 512 * beta : k), (-7 / 64 * beta : k),
      (21 / 1024 * beta : k), (-7 / 64 * beta : k)]
      [
      [3, 1, 0, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0],
      [0, 1, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest3810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIMuRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-7 / 8192 * beta : k), (-7 / 1024 * beta : k), (7 / 512 * beta : k),
      (-7 / 64 * beta : k), (21 / 1024 * beta : k), (-7 / 64 * beta : k)]
      [
      [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest4810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIMuRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
]
      [
] := by
  simp only [towerLeavesOpenIMuRest4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest4810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIMuRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-7 / 64 * beta : k)]
      [
      [0, 0, 1, 1, 0, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest5810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIMuRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 128 * gamma : k), (-3 / 32 * gamma : k), (3 / 4 * gamma : k)]
      [
      [1, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]] := by
  simp only [towerLeavesOpenIMuRest5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest5810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIMuRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 128 * gamma : k), (-3 / 16 * gamma : k), (-3 / 32 * gamma : k),
      (3 / 4 * gamma : k)]
      [
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]] := by
  simp only [towerLeavesOpenIMuRest5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest6810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIMuRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-5 / 1024 * delta : k), (-15 / 64 * delta : k), (5 / 8 * delta : k)]
      [
      [2, 1, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [towerLeavesOpenIMuRest6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest6810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIMuRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-5 / 1024 * delta : k), (-5 / 64 * delta : k), (-15 / 64 * delta : k),
      (5 / 8 * delta : k)]
      [
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [towerLeavesOpenIMuRest6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest7810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIMuRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-1 / 8 * epsilon : k), (1 / 2 * epsilon : k)]
      [
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest7810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIMuRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-1 / 8 * epsilon : k), (1 / 2 * epsilon : k)]
      [
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest8810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIMuRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 64 * zeta : k)]
      [
      [1, 1, 0, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest8810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIMuRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 64 * zeta : k), (3 / 8 * zeta : k)]
      [
      [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest9810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIMuRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * eta : k)]
      [
      [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest9810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIMuRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * eta : k)]
      [
      [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest10810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIMuRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)]
      [
      [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIMuRest10810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIMuRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)]
      [
      [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIMuRest10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- The strict bands put every remainder chunk below the face. -/
theorem towerLeavesOpenIMurest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (towerLeavesOpenIMuRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
  rcases hc with ⟨⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩, hCEq, hFEq, hGEq, hDbound, hEbound⟩
  have hr0 : (towerLeavesOpenIMuRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIMuRest0810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIMuRest0810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr1 : (towerLeavesOpenIMuRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIMuRest1810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest1810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIMuRest1810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest1810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr2 : (towerLeavesOpenIMuRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIMuRest2810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest2810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIMuRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest2810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr3 : (towerLeavesOpenIMuRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIMuRest3810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest3810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIMuRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest3810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr4 : (towerLeavesOpenIMuRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIMuRest4810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest4810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIMuRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest4810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr5 : (towerLeavesOpenIMuRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIMuRest5810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIMuRest5810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr6 : (towerLeavesOpenIMuRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbdelta with hz | hb
      · simp only [towerLeavesOpenIMuRest6810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest6810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbdelta with hz | hb
      · simp only [towerLeavesOpenIMuRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest6810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr7 : (towerLeavesOpenIMuRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIMuRest7810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIMuRest7810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr8 : (towerLeavesOpenIMuRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbzeta with hz | hb
      · simp only [towerLeavesOpenIMuRest8810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest8810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbzeta with hz | hb
      · simp only [towerLeavesOpenIMuRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest8810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr9 : (towerLeavesOpenIMuRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIMuRest9810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIMuRest9810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr10 : (towerLeavesOpenIMuRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbtheta with hz | hb
      · simp only [towerLeavesOpenIMuRest10810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest10810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbtheta with hz | hb
      · simp only [towerLeavesOpenIMuRest10810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIMuRest10810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  unfold towerLeavesOpenIMuRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10)

set_option maxHeartbeats 64000000 in
/-- Coefficient of the homogeneous face at its common degree. -/
theorem towerLeavesOpenIMuface_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    (towerLeavesOpenIMuFace810 A B C D E F G).coeff (3 * C.natDegree) =
      (5 / 512 : k) * muQuarticOpenIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hc with ⟨⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩, hCEq, hFEq, hGEq, hDbound, hEbound⟩
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A * B ^ 2 * C).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    try simp only [natDegree_pow]
    all_goals omega
  have hm0 : (A * B ^ 2 * C).coeff (3 * C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A * B * F).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    try simp only [natDegree_pow]
    all_goals omega
  have hm1 : (A * B * F).coeff (3 * C.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (C ^ 3).natDegree = 3 * C.natDegree := by
    try simp only [natDegree_pow]
    all_goals omega
  have hm2 : (C ^ 3).coeff (3 * C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C * G).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hCne hGne]
    try simp only [natDegree_pow]
    all_goals omega
  have hm3 : (C * G).coeff (3 * C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [towerLeavesOpenIMuFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, muQuarticOpenIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar Open-I face vanishes. -/
theorem towerLeavesOpenIMuFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    muQuarticOpenIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := towerLeavesOpenIMurest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta
  have ht := towerLeavesOpenIMuface_coeff810 A B C D E F G hc hDle hEle hBne hCne hFne hGne
  have hd : 0 < 3 * C.natDegree := by
    rcases hc with ⟨⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩, hCEq, hFEq, hGEq, hDbound, hEbound⟩
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree by omega)
  rw [towerLeavesOpenIMusplit810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

set_option maxHeartbeats 64000000 in
/-- The homogeneous Open-I polynomial face. -/
def towerLeavesOpenIPiFace810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4) +
    (-45 / 512 : k) • (A * B ^ 2 * C ^ 2) +
    (5 / 64 : k) • (A * B ^ 2 * G) +
    (5 / 32 : k) • (A * B * C * F) +
    (-5 / 16 : k) • (A * F ^ 2) +
    (15 / 256 : k) • (C ^ 4) +
    (-5 / 16 : k) • (C ^ 2 * G) +
    (5 / 4 : k) • (G ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIPiRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-15 / 128 : k) • (A * B ^ 3 * D) +
    (5 / 16 : k) • (A * B * D * E) +
    (5 / 32 : k) • (A * C * D ^ 2) +
    (-35 / 256 : k) • (B ^ 4 * C) +
    (25 / 128 : k) • (B ^ 3 * F) +
    (45 / 64 : k) • (B ^ 2 * C * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIPiRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 128 : k) • (B ^ 2 * D ^ 2) +
    (45 / 64 : k) • (B * C ^ 2 * D) +
    (-5 / 8 : k) • (B * D * G) +
    (-15 / 16 : k) • (B * E * F) +
    (-15 / 16 : k) • (C * D * F) +
    (-5 / 8 : k) • (C * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomials. -/
def towerLeavesOpenIPiRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIPiRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 131072 * l : k) • (A ^ 4 * B * C) +
    (-45 / 32768 * l : k) • (A ^ 4 * F) +
    (-3 / 32768 * l : k) • (A ^ 3 * B ^ 3) +
    (9 / 4096 * l : k) • (A ^ 3 * B * E) +
    (9 / 4096 * l : k) • (A ^ 3 * C * D) +
    (-27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIPiRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2) +
    (-27 / 1024 * l : k) • (A ^ 2 * C * F) +
    (9 / 512 * l : k) • (A ^ 2 * D * E) +
    (-189 / 4096 * l : k) • (A * B ^ 3 * C) +
    (63 / 1024 * l : k) • (A * B ^ 2 * F) +
    (9 / 128 * l : k) • (A * B * C * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIPiRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 256 * l : k) • (A * B * D ^ 2) +
    (9 / 256 * l : k) • (A * C ^ 2 * D) +
    (-9 / 64 * l : k) • (A * E * F) +
    (-63 / 4096 * l : k) • (B ^ 5) +
    (63 / 512 * l : k) • (B ^ 3 * E) +
    (189 / 512 * l : k) • (B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIPiRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 512 * l : k) • (B * C ^ 3) +
    (-9 / 32 * l : k) • (B * C * G) +
    (-27 / 64 * l : k) • (B * D * F) +
    (-9 / 32 * l : k) • (B * E ^ 2) +
    (-27 / 128 * l : k) • (C ^ 2 * F) +
    (-9 / 16 * l : k) • (C * D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def towerLeavesOpenIPiRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 32 * l : k) • (D ^ 3) +
    (9 / 8 * l : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIPiRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 4096 * beta : k) • (A ^ 3 * B * C) +
    (-7 / 1024 * beta : k) • (A ^ 3 * F) +
    (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3) +
    (7 / 512 * beta : k) • (A ^ 2 * B * E) +
    (7 / 512 * beta : k) • (A ^ 2 * C * D) +
    (-21 / 256 * beta : k) • (A * B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIPiRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 256 * beta : k) • (A * B * C ^ 2) +
    (-7 / 64 * beta : k) • (A * C * F) +
    (7 / 32 * beta : k) • (A * D * E) +
    (-63 / 512 * beta : k) • (B ^ 3 * C) +
    (21 / 128 * beta : k) • (B ^ 2 * F) +
    (7 / 16 * beta : k) • (B * C * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 3 monomials. -/
def towerLeavesOpenIPiRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 32 * beta : k) • (B * D ^ 2) +
    (7 / 32 * beta : k) • (C ^ 2 * D) +
    (-7 / 8 * beta : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIPiRest11810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 32 * gamma : k) • (A * B ^ 2 * C) +
    (3 / 16 * gamma : k) • (A * D ^ 2) +
    (-15 / 256 * gamma : k) • (B ^ 4) +
    (3 / 8 * gamma : k) • (B ^ 2 * E) +
    (3 / 4 * gamma : k) • (B * C * D) +
    (1 / 8 * gamma : k) • (C ^ 3)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def towerLeavesOpenIPiRest12810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 4 * gamma : k) • (D * F) +
    (-3 / 4 * gamma : k) • (E ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def towerLeavesOpenIPiRest13810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 * delta : k) • (A ^ 2 * B * C) +
    (-5 / 128 * delta : k) • (A ^ 2 * F) +
    (-15 / 256 * delta : k) • (A * B ^ 3) +
    (5 / 32 * delta : k) • (A * B * E) +
    (5 / 32 * delta : k) • (A * C * D) +
    (15 / 32 * delta : k) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 3 monomials. -/
def towerLeavesOpenIPiRest14810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 32 * delta : k) • (B * C ^ 2) +
    (-5 / 8 * delta : k) • (C * F) +
    (-5 / 4 * delta : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def towerLeavesOpenIPiRest15810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * epsilon : k) • (A * B * D) +
    (1 / 2 * epsilon : k) • (B ^ 2 * C) +
    (-1 / 2 * epsilon : k) • (B * F) +
    (-1 * epsilon : k) • (C * E) +
    (-1 / 2 * epsilon : k) • (D ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def towerLeavesOpenIPiRest16810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32 * zeta : k) • (A * B * C) +
    (-3 / 8 * zeta : k) • (A * F) +
    (5 / 32 * zeta : k) • (B ^ 3) +
    (-3 / 4 * zeta : k) • (B * E) +
    (-3 / 4 * zeta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def towerLeavesOpenIPiRest17810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 16 * eta : k) • (A * B ^ 2) +
    (-1 / 2 * eta : k) • (B * D) +
    (-1 / 4 * eta : k) • (C ^ 2) +
    (2 * eta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def towerLeavesOpenIPiRest18810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 4 * theta : k) • (B * C) +
    (1 * theta : k) • (F)

set_option maxHeartbeats 64000000 in
/-- The remainder after the homogeneous face. -/
def towerLeavesOpenIPiRest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  towerLeavesOpenIPiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest13810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest14810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest15810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest16810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest17810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    towerLeavesOpenIPiRest18810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The carrier splits exactly into face and remainder. -/
theorem towerLeavesOpenIPisplit810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      towerLeavesOpenIPiFace810 A B C D E F G + towerLeavesOpenIPiRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroPiQuartic810, towerLeavesOpenIPiFace810, towerLeavesOpenIPiRest810, towerLeavesOpenIPiRest0810, towerLeavesOpenIPiRest1810, towerLeavesOpenIPiRest2810, towerLeavesOpenIPiRest3810, towerLeavesOpenIPiRest4810, towerLeavesOpenIPiRest5810, towerLeavesOpenIPiRest6810, towerLeavesOpenIPiRest7810, towerLeavesOpenIPiRest8810, towerLeavesOpenIPiRest9810, towerLeavesOpenIPiRest10810, towerLeavesOpenIPiRest11810, towerLeavesOpenIPiRest12810, towerLeavesOpenIPiRest13810, towerLeavesOpenIPiRest14810, towerLeavesOpenIPiRest15810, towerLeavesOpenIPiRest16810, towerLeavesOpenIPiRest17810, towerLeavesOpenIPiRest18810, piBaseGroupQuartic810, piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810, piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810, piThetaGroupQuartic810]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest0810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-35 / 256 : k), (25 / 128 : k), (45 / 64 : k)]
      [
      [0, 4, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest0810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-15 / 128 : k), (5 / 16 : k), (5 / 32 : k),
      (-35 / 256 : k), (25 / 128 : k), (45 / 64 : k)]
      [
      [1, 3, 0, 1, 0, 0, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest1810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-15 / 16 : k), (-5 / 8 : k)]
      [
      [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 0, 2, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest1810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 128 : k), (45 / 64 : k), (-5 / 8 : k),
      (-15 / 16 : k), (-15 / 16 : k), (-5 / 8 : k)]
      [
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0],
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest2810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
]
      [
] := by
  simp only [towerLeavesOpenIPiRest2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest2810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-5 / 8 : k)]
      [
      [0, 0, 0, 2, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest3810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 131072 * l : k), (-45 / 32768 * l : k), (-3 / 32768 * l : k),
      (9 / 4096 * l : k)]
      [
      [4, 1, 1, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0], [3, 3, 0, 0, 0, 0, 0], [3, 1, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest3810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 131072 * l : k), (-45 / 32768 * l : k), (-3 / 32768 * l : k),
      (9 / 4096 * l : k), (9 / 4096 * l : k), (-27 / 4096 * l : k)]
      [
      [4, 1, 1, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0], [3, 3, 0, 0, 0, 0, 0], [3, 1, 0, 0, 1, 0, 0],
      [3, 0, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest4810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 4096 * l : k), (-27 / 1024 * l : k), (-189 / 4096 * l : k),
      (63 / 1024 * l : k), (9 / 128 * l : k)]
      [
      [2, 1, 2, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0], [1, 3, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 1, 0],
      [1, 1, 1, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest4810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 4096 * l : k), (-27 / 1024 * l : k), (9 / 512 * l : k),
      (-189 / 4096 * l : k), (63 / 1024 * l : k), (9 / 128 * l : k)]
      [
      [2, 1, 2, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0], [1, 3, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest5810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-9 / 64 * l : k), (-63 / 4096 * l : k), (63 / 512 * l : k)]
      [
      [1, 0, 0, 0, 1, 1, 0], [0, 5, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest5810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 256 * l : k), (9 / 256 * l : k), (-9 / 64 * l : k),
      (-63 / 4096 * l : k), (63 / 512 * l : k), (189 / 512 * l : k)]
      [
      [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0], [0, 5, 0, 0, 0, 0, 0],
      [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest6810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 512 * l : k), (-9 / 32 * l : k), (-9 / 32 * l : k),
      (-27 / 128 * l : k)]
      [
      [0, 1, 3, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0]] := by
  simp only [towerLeavesOpenIPiRest6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest6810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 512 * l : k), (-9 / 32 * l : k), (-27 / 64 * l : k),
      (-9 / 32 * l : k), (-27 / 128 * l : k), (-9 / 16 * l : k)]
      [
      [0, 1, 3, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest7810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 8 * l : k)]
      [
      [0, 0, 0, 0, 0, 1, 1]] := by
  simp only [towerLeavesOpenIPiRest7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest7810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 32 * l : k), (9 / 8 * l : k)]
      [
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1]] := by
  simp only [towerLeavesOpenIPiRest7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest8810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 4096 * beta : k), (-7 / 1024 * beta : k), (7 / 4096 * beta : k),
      (7 / 512 * beta : k)]
      [
      [3, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 3, 0, 0, 0, 0, 0], [2, 1, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest8810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 4096 * beta : k), (-7 / 1024 * beta : k), (7 / 4096 * beta : k),
      (7 / 512 * beta : k), (7 / 512 * beta : k), (-21 / 256 * beta : k)]
      [
      [3, 1, 1, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 3, 0, 0, 0, 0, 0], [2, 1, 0, 0, 1, 0, 0],
      [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest9810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-7 / 256 * beta : k), (-7 / 64 * beta : k), (-63 / 512 * beta : k),
      (21 / 128 * beta : k), (7 / 16 * beta : k)]
      [
      [1, 1, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0],
      [0, 1, 1, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest9810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-7 / 256 * beta : k), (-7 / 64 * beta : k), (7 / 32 * beta : k),
      (-63 / 512 * beta : k), (21 / 128 * beta : k), (7 / 16 * beta : k)]
      [
      [1, 1, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest10810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-7 / 8 * beta : k)]
      [
      [0, 0, 0, 0, 1, 1, 0]] := by
  simp only [towerLeavesOpenIPiRest10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest10810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 32 * beta : k), (7 / 32 * beta : k), (-7 / 8 * beta : k)]
      [
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]] := by
  simp only [towerLeavesOpenIPiRest10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest11810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 32 * gamma : k), (-15 / 256 * gamma : k), (3 / 8 * gamma : k),
      (1 / 8 * gamma : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest11810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest11810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 32 * gamma : k), (3 / 16 * gamma : k), (-15 / 256 * gamma : k),
      (3 / 8 * gamma : k), (3 / 4 * gamma : k), (1 / 8 * gamma : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest11810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest12810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 4 * gamma : k)]
      [
      [0, 0, 0, 0, 2, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest12810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest12810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-3 / 4 * gamma : k), (-3 / 4 * gamma : k)]
      [
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest12810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest13810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest13810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 * delta : k), (-5 / 128 * delta : k), (-15 / 256 * delta : k),
      (5 / 32 * delta : k)]
      [
      [2, 1, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest13810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest13810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest13810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 * delta : k), (-5 / 128 * delta : k), (-15 / 256 * delta : k),
      (5 / 32 * delta : k), (5 / 32 * delta : k), (15 / 32 * delta : k)]
      [
      [2, 1, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0],
      [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest13810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest14810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest14810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 32 * delta : k), (-5 / 8 * delta : k)]
      [
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0]] := by
  simp only [towerLeavesOpenIPiRest14810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest14810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest14810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 32 * delta : k), (-5 / 8 * delta : k), (-5 / 4 * delta : k)]
      [
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest14810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest15810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest15810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 2 * epsilon : k), (-1 / 2 * epsilon : k), (-1 * epsilon : k)]
      [
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest15810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest15810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest15810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * epsilon : k), (1 / 2 * epsilon : k), (-1 / 2 * epsilon : k),
      (-1 * epsilon : k), (-1 / 2 * epsilon : k)]
      [
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest15810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest16810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest16810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 32 * zeta : k), (-3 / 8 * zeta : k), (5 / 32 * zeta : k),
      (-3 / 4 * zeta : k)]
      [
      [1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest16810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest16810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest16810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 32 * zeta : k), (-3 / 8 * zeta : k), (5 / 32 * zeta : k),
      (-3 / 4 * zeta : k), (-3 / 4 * zeta : k)]
      [
      [1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0]] := by
  simp only [towerLeavesOpenIPiRest16810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest17810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest17810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 16 * eta : k), (-1 / 4 * eta : k), (2 * eta : k)]
      [
      [1, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]] := by
  simp only [towerLeavesOpenIPiRest17810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest17810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest17810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 16 * eta : k), (-1 / 2 * eta : k), (-1 / 4 * eta : k),
      (2 * eta : k)]
      [
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]] := by
  simp only [towerLeavesOpenIPiRest17810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest18810_Dzero_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) (hDz : D = 0) :
    towerLeavesOpenIPiRest18810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-1 / 4 * theta : k), (1 * theta : k)]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [towerLeavesOpenIPiRest18810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc, hDz, zero_mul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_smul, smul_zero, zero_add]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- Reflected exponent data for a tower-leaf remainder bound. -/
private theorem astra810t_front_towerLeavesOpenIPiRest18810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    towerLeavesOpenIPiRest18810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-1 / 4 * theta : k), (1 * theta : k)]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [towerLeavesOpenIPiRest18810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right,
    Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
    Max11ReflectDeg.mono_nil_right, pow_zero, pow_one,
    mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- The strict bands put every remainder chunk below the face. -/
theorem towerLeavesOpenIPirest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (towerLeavesOpenIPiRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
  rcases hc with ⟨⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩, hCEq, hFEq, hGEq, hDbound, hEbound⟩
  have hr0 : (towerLeavesOpenIPiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIPiRest0810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIPiRest0810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr1 : (towerLeavesOpenIPiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIPiRest1810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIPiRest1810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr2 : (towerLeavesOpenIPiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIPiRest2810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIPiRest2810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr3 : (towerLeavesOpenIPiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIPiRest3810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest3810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIPiRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest3810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr4 : (towerLeavesOpenIPiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIPiRest4810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest4810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIPiRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest4810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr5 : (towerLeavesOpenIPiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIPiRest5810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest5810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIPiRest5810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest5810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr6 : (towerLeavesOpenIPiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIPiRest6810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest6810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIPiRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest6810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr7 : (towerLeavesOpenIPiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIPiRest7810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest7810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbl with hz | hb
      · simp only [towerLeavesOpenIPiRest7810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest7810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr8 : (towerLeavesOpenIPiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIPiRest8810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest8810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIPiRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest8810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr9 : (towerLeavesOpenIPiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIPiRest9810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest9810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIPiRest9810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest9810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr10 : (towerLeavesOpenIPiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIPiRest10810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest10810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbbeta with hz | hb
      · simp only [towerLeavesOpenIPiRest10810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest10810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr11 : (towerLeavesOpenIPiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIPiRest11810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIPiRest11810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr12 : (towerLeavesOpenIPiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIPiRest12810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIPiRest12810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr13 : (towerLeavesOpenIPiRest13810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbdelta with hz | hb
      · simp only [towerLeavesOpenIPiRest13810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest13810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbdelta with hz | hb
      · simp only [towerLeavesOpenIPiRest13810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest13810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr14 : (towerLeavesOpenIPiRest14810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbdelta with hz | hb
      · simp only [towerLeavesOpenIPiRest14810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest14810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbdelta with hz | hb
      · simp only [towerLeavesOpenIPiRest14810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest14810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr15 : (towerLeavesOpenIPiRest15810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIPiRest15810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIPiRest15810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr16 : (towerLeavesOpenIPiRest16810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbzeta with hz | hb
      · simp only [towerLeavesOpenIPiRest16810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest16810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbzeta with hz | hb
      · simp only [towerLeavesOpenIPiRest16810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest16810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  have hr17 : (towerLeavesOpenIPiRest17810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rw [astra810t_front_towerLeavesOpenIPiRest17810_Dzero_eq_polyOf (hDz := hDz)]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
    · rw [astra810t_front_towerLeavesOpenIPiRest17810_eq_polyOf]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add, max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hr18 : (towerLeavesOpenIPiRest18810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hDle with hDz | hDle
    · rcases hbtheta with hz | hb
      · simp only [towerLeavesOpenIPiRest18810, hDz, zero_mul, mul_zero, zero_pow, zero_smul, add_zero, zero_add, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest18810_Dzero_eq_polyOf (hDz := hDz)]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
    · rcases hbtheta with hz | hb
      · simp only [towerLeavesOpenIPiRest18810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
        omega
      · rw [astra810t_front_towerLeavesOpenIPiRest18810_eq_polyOf]
        apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
        clear * - hApos hAB hAC hAD hAE hAF hAG hCEq hFEq hGEq hDbound hEbound hEle hDle hb
        simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
          Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add, max_lt_iff]
        repeat' apply And.intro
        all_goals omega
  unfold towerLeavesOpenIPiRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10) hr11) hr12) hr13) hr14) hr15) hr16) hr17) hr18)

set_option maxHeartbeats 64000000 in
/-- Coefficient of the homogeneous face at its common degree. -/
theorem towerLeavesOpenIPiface_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    (towerLeavesOpenIPiFace810 A B C D E F G).coeff (2 * G.natDegree) =
      (5 / 4096 : k) * piQuarticOpenIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hc with ⟨⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩, hCEq, hFEq, hGEq, hDbound, hEbound⟩
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A ^ 2 * B ^ 4).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    try simp only [natDegree_pow]
    all_goals omega
  have hm0 : (A ^ 2 * B ^ 4).coeff (2 * G.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A * B ^ 2 * C ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne)]
    try simp only [natDegree_pow]
    all_goals omega
  have hm1 : (A * B ^ 2 * C ^ 2).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (A * B ^ 2 * G).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    try simp only [natDegree_pow]
    all_goals omega
  have hm2 : (A * B ^ 2 * G).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (A * B * C * F).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    try simp only [natDegree_pow]
    all_goals omega
  have hm3 : (A * B * C * F).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (A * F ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    try simp only [natDegree_pow]
    all_goals omega
  have hm4 : (A * F ^ 2).coeff (2 * G.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : (C ^ 4).natDegree = 2 * G.natDegree := by
    try simp only [natDegree_pow]
    all_goals omega
  have hm5 : (C ^ 4).coeff (2 * G.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd6 : (C ^ 2 * G).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    try simp only [natDegree_pow]
    all_goals omega
  have hm6 : (C ^ 2 * G).coeff (2 * G.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd6, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd7 : (G ^ 2).natDegree = 2 * G.natDegree := by
    try simp only [natDegree_pow]
    all_goals omega
  have hm7 : (G ^ 2).coeff (2 * G.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd7, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [towerLeavesOpenIPiFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, piQuarticOpenIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar Open-I face vanishes. -/
theorem towerLeavesOpenIPiFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    piQuarticOpenIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := towerLeavesOpenIPirest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta
  have ht := towerLeavesOpenIPiface_coeff810 A B C D E F G hc hDle hEle hBne hCne hFne hGne
  have hd : 0 < 2 * G.natDegree := by
    rcases hc with ⟨⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩, hCEq, hFEq, hGEq, hDbound, hEbound⟩
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree by omega)
  rw [towerLeavesOpenIPisplit810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)


set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestLF0_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestLF0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(93 / 8192 : k), (-115 / 1536 : k), (-225 / 1024 : k), (-125 / 2048 : k), (-265 / 2048 : k), (25 / 96 : k)]
        [[1, 5, 0, 0, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0], [1, 2, 1, 1, 0, 0, 0], [0, 4, 0, 1, 0, 0, 0], [0, 3, 2, 0, 0, 0, 0], [1, 1, 0, 1, 0, 1, 0]] := by
  simp only [bcdefg12N6RestLF0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestLF0_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestLF0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rw [astra810t_bcdefg12N6RestLF0_eq_polyOf]
  clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
  repeat' apply And.intro
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestLF1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestLF1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(25 / 384 : k), (15 / 256 : k), (85 / 256 : k), (85 / 256 : k), (45 / 128 : k), (45 / 128 : k)]
        [[1, 0, 0, 3, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 1, 0], [0, 2, 0, 1, 1, 0, 0], [0, 1, 2, 0, 1, 0, 0], [0, 1, 1, 2, 0, 0, 0]] := by
  simp only [bcdefg12N6RestLF1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestLF1_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestLF1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rw [astra810t_bcdefg12N6RestLF1_eq_polyOf]
  clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
  repeat' apply And.intro
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestLF2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestLF2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(15 / 128 : k), (-5 / 16 : k), (-5 / 16 : k), (-5 / 16 : k), (-5 / 8 : k), (-5 / 16 : k)]
        [[0, 0, 3, 1, 0, 0, 0], [0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 0, 2, 0], [0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 2, 0, 1, 0]] := by
  simp only [bcdefg12N6RestLF2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestLF2_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestLF2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rw [astra810t_bcdefg12N6RestLF2_eq_polyOf]
  clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
  repeat' apply And.intro
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestLF3_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestLF3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-5 / 16 : k)]
        [[0, 0, 0, 1, 2, 0, 0]] := by
  simp only [bcdefg12N6RestLF3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestLF3_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestLF3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rw [astra810t_bcdefg12N6RestLF3_eq_polyOf]
  clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
  repeat' apply And.intro
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestL0_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestL0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(715 / 268435456 * l : k), (105 / 1048576 * l : k), (-255 / 4194304 * l : k), (105 / 262144 * l : k), (-135 / 262144 * l : k), (585 / 524288 * l : k)]
        [[8, 0, 0, 0, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0], [4, 1, 0, 1, 0, 0, 0], [4, 0, 2, 0, 0, 0, 0]] := by
  simp only [bcdefg12N6RestL0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestL0_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbl with hz | hb
  · simp only [bcdefg12N6RestL0, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestL0_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestL1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestL1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-93 / 131072 * l : k), (1425 / 524288 * l : k), (15 / 32768 * l : k), (81 / 8192 * l : k), (-15 / 8192 * l : k), (-135 / 16384 * l : k)]
        [[3, 2, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 1], [3, 0, 1, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0]] := by
  simp only [bcdefg12N6RestL1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestL1_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbl with hz | hb
  · simp only [bcdefg12N6RestL1, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestL1_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestL2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestL2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-51 / 4096 * l : k), (11 / 8192 * l : k), (-369 / 8192 * l : k), (-765 / 16384 * l : k), (-567 / 16384 * l : k), (3 / 256 * l : k)]
        [[2, 1, 1, 1, 0, 0, 0], [2, 0, 3, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1]] := by
  simp only [bcdefg12N6RestL2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestL2_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbl with hz | hb
  · simp only [bcdefg12N6RestL2, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestL2_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestL3_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestL3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(3 / 1024 * l : k), (51 / 2048 * l : k), (27 / 1024 * l : k), (21 / 256 * l : k), (75 / 512 * l : k), (39 / 1024 * l : k)]
        [[2, 0, 0, 1, 0, 1, 0], [2, 0, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 2, 0, 1, 0, 0]] := by
  simp only [bcdefg12N6RestL3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestL3_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbl with hz | hb
  · simp only [bcdefg12N6RestL3, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestL3_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestL4_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestL4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(9 / 128 * l : k), (27 / 512 * l : k), (45 / 256 * l : k), (45 / 512 * l : k), (189 / 1024 * l : k), (63 / 4096 * l : k)]
        [[1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0]] := by
  simp only [bcdefg12N6RestL4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestL4_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbl with hz | hb
  · simp only [bcdefg12N6RestL4, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestL4_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestL5_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestL5 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(3 / 64 * l : k), (-3 / 16 * l : k), (-9 / 64 * l : k), (-9 / 32 * l : k), (-9 / 128 * l : k), (-9 / 32 * l : k)]
        [[1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0]] := by
  simp only [bcdefg12N6RestL5, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestL5_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL5 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbl with hz | hb
  · simp only [bcdefg12N6RestL5, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestL5_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestL6_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestL6 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-9 / 64 * l : k), (-9 / 64 * l : k), (9 / 16 * l : k)]
        [[0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]] := by
  simp only [bcdefg12N6RestL6, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestL6_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL6 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbl with hz | hb
  · simp only [bcdefg12N6RestL6, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestL6_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestBeta0_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestBeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(11 / 1048576 * beta : k), (35 / 98304 * beta : k), (-35 / 131072 * beta : k), (35 / 24576 * beta : k), (-35 / 12288 * beta : k), (7 / 2048 * beta : k)]
        [[7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0]] := by
  simp only [bcdefg12N6RestBeta0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestBeta0_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbbeta with hz | hb
  · simp only [bcdefg12N6RestBeta0, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestBeta0_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestBeta1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestBeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(175 / 49152 * beta : k), (91 / 8192 * beta : k), (35 / 1024 * beta : k), (-133 / 6144 * beta : k), (-49 / 768 * beta : k), (-7 / 64 * beta : k)]
        [[2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 0, 1, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0]] := by
  simp only [bcdefg12N6RestBeta1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestBeta1_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbbeta with hz | hb
  · simp only [bcdefg12N6RestBeta1, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestBeta1_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestBeta2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestBeta2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-7 / 128 * beta : k), (-91 / 1024 * beta : k), (7 / 48 * beta : k), (7 / 32 * beta : k), (7 / 32 * beta : k), (7 / 64 * beta : k)]
        [[0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 0, 2, 0, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0]] := by
  simp only [bcdefg12N6RestBeta2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestBeta2_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbbeta with hz | hb
  · simp only [bcdefg12N6RestBeta2, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestBeta2_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestBeta3_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestBeta3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(7 / 64 * beta : k), (-7 / 16 * beta : k), (-7 / 768 * beta : k), (7 / 96 * beta : k), (7 / 3072 * beta : k)]
        [[0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0], [1, 0, 3, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [2, 1, 0, 0, 0, 1, 0]] := by
  simp only [bcdefg12N6RestBeta3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestBeta3_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbbeta with hz | hb
  · simp only [bcdefg12N6RestBeta3, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestBeta3_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestGamma0_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestGamma0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(5 / 768 * gamma : k), (-15 / 128 * gamma : k), (-9 / 128 * gamma : k), (-27 / 256 * gamma : k), (-1 / 32 * gamma : k), (5 / 16 * gamma : k)]
        [[2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0]] := by
  simp only [bcdefg12N6RestGamma0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestGamma0_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestGamma0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rw [astra810t_bcdefg12N6RestGamma0_eq_polyOf]
  clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
  repeat' apply And.intro
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestGamma1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestGamma1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(9 / 64 * gamma : k), (3 / 8 * gamma : k), (3 / 16 * gamma : k), (3 / 16 * gamma : k), (-3 / 4 * gamma : k)]
        [[0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]] := by
  simp only [bcdefg12N6RestGamma1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestGamma1_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestGamma1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rw [astra810t_bcdefg12N6RestGamma1_eq_polyOf]
  clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
  repeat' apply And.intro
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestDelta0_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(21 / 524288 * delta : k), (5 / 4096 * delta : k), (-65 / 49152 * delta : k), (5 / 1024 * delta : k), (-95 / 3072 * delta : k), (65 / 6144 * delta : k)]
        [[6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]] := by
  simp only [bcdefg12N6RestDelta0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestDelta0_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbdelta with hz | hb
  · simp only [bcdefg12N6RestDelta0, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestDelta0_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestDelta1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-125 / 1024 * delta : k), (-135 / 4096 * delta : k), (35 / 192 * delta : k), (5 / 32 * delta : k), (25 / 128 * delta : k), (15 / 32 * delta : k)]
        [[1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0]] := by
  simp only [bcdefg12N6RestDelta1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestDelta1_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbdelta with hz | hb
  · simp only [bcdefg12N6RestDelta1, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestDelta1_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestDelta2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestDelta2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(5 / 64 * delta : k), (-5 / 8 * delta : k), (-5 / 16 * delta : k), (5 / 96 * delta : k), (-5 / 384 * delta : k)]
        [[0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [1, 1, 0, 0, 0, 1, 0], [2, 0, 0, 0, 0, 0, 1]] := by
  simp only [bcdefg12N6RestDelta2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestDelta2_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestDelta2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbdelta with hz | hb
  · simp only [bcdefg12N6RestDelta2, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestDelta2_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestEpsilon0_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-5 / 96 * epsilon : k), (5 / 24 * epsilon : k), (3 / 16 * epsilon : k), (7 / 32 * epsilon : k), (1 / 4 * epsilon : k), (-1 / 2 * epsilon : k)]
        [[1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0]] := by
  simp only [bcdefg12N6RestEpsilon0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestEpsilon0_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rw [astra810t_bcdefg12N6RestEpsilon0_eq_polyOf]
  clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
  repeat' apply And.intro
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestEpsilon1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestEpsilon1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-1 / 2 * epsilon : k)]
        [[0, 0, 0, 1, 1, 0, 0]] := by
  simp only [bcdefg12N6RestEpsilon1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestEpsilon1_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestEpsilon1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rw [astra810t_bcdefg12N6RestEpsilon1_eq_polyOf]
  clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
  repeat' apply And.intro
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestZeta0_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(7 / 49152 * zeta : k), (1 / 256 * zeta : k), (-11 / 1024 * zeta : k), (1 / 64 * zeta : k), (3 / 16 * zeta : k), (27 / 128 * zeta : k)]
        [[5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0]] := by
  simp only [bcdefg12N6RestZeta0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestZeta0_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbzeta with hz | hb
  · simp only [bcdefg12N6RestZeta0, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestZeta0_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestZeta1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestZeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-3 / 8 * zeta : k), (-3 / 8 * zeta : k), (-3 / 16 * zeta : k), (3 / 64 * zeta : k), (-1 / 4 * zeta : k)]
        [[0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1]] := by
  simp only [bcdefg12N6RestZeta1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestZeta1_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestZeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbzeta with hz | hb
  · simp only [bcdefg12N6RestZeta1, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestZeta1_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestEta0_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(3 / 32 * eta : k), (3 / 64 * eta : k), (-5 / 12 * eta : k), (-1 / 4 * eta : k), (-1 / 4 * eta : k)]
        [[1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]] := by
  simp only [bcdefg12N6RestEta0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestEta0_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rw [astra810t_bcdefg12N6RestEta0_eq_polyOf]
  clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
  repeat' apply And.intro
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestTheta0_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(5 / 12288 * theta : k), (1 / 96 * theta : k), (3 / 128 * theta : k), (1 / 24 * theta : k), (-1 / 8 * theta : k), (-1 / 16 * theta : k)]
        [[4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0]] := by
  simp only [bcdefg12N6RestTheta0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestTheta0_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbtheta with hz | hb
  · simp only [bcdefg12N6RestTheta0, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestTheta0_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
    · rcases hDle with hDz | hDd
      · right; left
        simp [Max11ReflectDeg.mono, hDz]
      · right; right
        simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
          Nat.add_zero, Nat.zero_add]
        omega
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_bcdefg12N6RestTheta1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    bcdefg12N6RestTheta1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(1 * theta : k)]
        [[0, 0, 0, 0, 0, 0, 1]] := by
  simp only [bcdefg12N6RestTheta1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- A tracked N6 remainder chunk lies below the common tower face. -/

theorem towerLeaves_bcdefg12N6RestTheta1_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestTheta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rcases hbtheta with hz | hb
  · simp only [bcdefg12N6RestTheta1, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  ·
    rw [astra810t_bcdefg12N6RestTheta1_eq_polyOf]
    clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle hb
    apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
    simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
    repeat' apply And.intro
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- The six monomials of the common N6 face. -/

def towerLeavesN6Face810
    (A B C D E F G : k[X]) : k[X] :=
  (145 / 12288 : k) • (A ^ 2 * B ^ 3 * C)
  + (-25 / 1536 : k) • (A ^ 2 * B ^ 2 * F)
  + (-45 / 1024 : k) • (A * B * C ^ 3)
  + (15 / 128 : k) • (A * B * C * G)
  + (-25 / 48 : k) • (A * F * G)
  + (5 / 96 : k) • (A * C ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- The three extra terms from the tracked maximal-tie N6 face. -/

def towerLeavesN6Extra810
    (A B C D E F G : k[X]) : k[X] :=
  (-25 / 768 : k) • (A ^ 2 * B * D ^ 2)
  + (25 / 192 : k) • (A * B * E ^ 2)
  + (95 / 384 : k) • (A * C * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomials for a tower-leaf remainder bound. -/
private theorem astra810t_towerLeavesN6Extra810_eq_polyOf
    (A B C D E F G : k[X]) :
    towerLeavesN6Extra810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
        [(-25 / 768 : k), (25 / 192 : k), (95 / 384 : k)]
        [[2, 1, 0, 2, 0, 0, 0], [1, 1, 0, 0, 2, 0, 0], [1, 0, 1, 1, 1, 0, 0]] := by
  simp only [towerLeavesN6Extra810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module

set_option maxHeartbeats 64000000 in
/-- The extra face terms lie strictly below the common N6 face. -/

theorem towerLeavesN6Extra_lt810
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree) :
    (towerLeavesN6Extra810 A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  rw [astra810t_towerLeavesN6Extra810_eq_polyOf]
  clear * - hApos hAB hAC hAD hAE hAF hAG hCdeg hFdeg hGdeg hDdeg hEdeg hEle hDle
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega)
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_right, and_true]
  repeat' apply And.intro
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega
  · right; right
    simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
      List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]
    omega
  · rcases hDle with hDz | hDd
    · right; left
      simp [Max11ReflectDeg.mono, hDz]
    · right; right
      simp only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
        List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, Nat.zero_add]
      omega

set_option maxHeartbeats 64000000 in
/-- The tracked maximal-tie face splits into the common face and three lower terms. -/

theorem towerLeavesN6Face_split810
    (A B C D E F G : k[X]) :
    bcdefg12N6Face A B C D E F G =
      towerLeavesN6Face810 A B C D E F G + towerLeavesN6Extra810 A B C D E F G := by
  simp only [bcdefg12N6Face, towerLeavesN6Face810, towerLeavesN6Extra810]
  module

set_option maxHeartbeats 64000000 in
/-- The tracked N6 remainder lies below the common face under the strict bands. -/

theorem towerLeavesN6Rest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6Rest l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by

  have hr0 := towerLeaves_bcdefg12N6RestLF0_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr1 := towerLeaves_bcdefg12N6RestLF1_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr2 := towerLeaves_bcdefg12N6RestLF2_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr3 := towerLeaves_bcdefg12N6RestLF3_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr4 := towerLeaves_bcdefg12N6RestL0_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr5 := towerLeaves_bcdefg12N6RestL1_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr6 := towerLeaves_bcdefg12N6RestL2_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr7 := towerLeaves_bcdefg12N6RestL3_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr8 := towerLeaves_bcdefg12N6RestL4_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr9 := towerLeaves_bcdefg12N6RestL5_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr10 := towerLeaves_bcdefg12N6RestL6_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr11 := towerLeaves_bcdefg12N6RestBeta0_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr12 := towerLeaves_bcdefg12N6RestBeta1_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr13 := towerLeaves_bcdefg12N6RestBeta2_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr14 := towerLeaves_bcdefg12N6RestBeta3_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr15 := towerLeaves_bcdefg12N6RestGamma0_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr16 := towerLeaves_bcdefg12N6RestGamma1_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr17 := towerLeaves_bcdefg12N6RestDelta0_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr18 := towerLeaves_bcdefg12N6RestDelta1_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr19 := towerLeaves_bcdefg12N6RestDelta2_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr20 := towerLeaves_bcdefg12N6RestEpsilon0_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr21 := towerLeaves_bcdefg12N6RestEpsilon1_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr22 := towerLeaves_bcdefg12N6RestZeta0_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr23 := towerLeaves_bcdefg12N6RestZeta1_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr24 := towerLeaves_bcdefg12N6RestEta0_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr25 := towerLeaves_bcdefg12N6RestTheta0_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  have hr26 := towerLeaves_bcdefg12N6RestTheta1_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta

  unfold bcdefg12N6Rest
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10) hr11) hr12) hr13) hr14) hr15) hr16) hr17) hr18) hr19) hr20) hr21) hr22) hr23) hr24) hr25) hr26)

set_option maxHeartbeats 64000000 in
/-- The common N6 coefficient is an explicit combination of the Open-I faces. -/

theorem towerLeavesN6Face_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    (towerLeavesN6Face810 A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) =
      (5 / 12288 : k) * (5 * A.leadingCoeff * n5QuarticOpenIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff - 6 * A.leadingCoeff * C.leadingCoeff * kappaQuarticOpenIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff) := by
  obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos

  have hd0 : (A ^ 2 * B ^ 3 * C).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne)) hCne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm0 : (A ^ 2 * B ^ 3 * C).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]

  have hd1 : (A ^ 2 * B ^ 2 * F).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hFne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm1 : (A ^ 2 * B ^ 2 * F).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]

  have hd2 : (A * B * C ^ 3).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 3 hCne), natDegree_mul hAne hBne, natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm2 : (A * B * C ^ 3).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]

  have hd3 : (A * B * C * G).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hGne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm3 : (A * B * C * G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]

  have hd4 : (A * F * G).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hFne) hGne, natDegree_mul hAne hFne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm4 : (A * F * G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * F.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]

  have hd5 : (A * C ^ 2 * F).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hFne, natDegree_mul hAne (pow_ne_zero 2 hCne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm5 : (A * C ^ 2 * F).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]

  simp only [towerLeavesN6Face810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, hm4, hm5, n5QuarticOpenIFace810, kappaQuarticOpenIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The N6 degree bound forces the Open-I N5 face to vanish once the kappa face vanishes. -/

theorem towerLeavesOpenIN6_to_N5_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkface : kappaQuarticOpenIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0) :
    n5QuarticOpenIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := towerLeavesN6Rest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hDle hEle hbl hbbeta hbdelta hbzeta hbtheta
  have he := towerLeavesN6Extra_lt810 A B C D E F G hc hDle hEle
  have ht := towerLeavesN6Face_coeff810 A B C D E F G hc hBne hCne hFne hGne
  have ha := hc.1.1
  have hnd := degreeZeroN6TowerQuartic810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G ha hprim homi hnu
  have hlarge : 2 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    obtain ⟨hcone, hCdeg, hFdeg, hGdeg, hDdeg, hEdeg⟩ := hc
    omega
  have hz := coeff_eq_zero_of_natDegree_lt (hnd.trans_lt hlarge)
  rw [bcdefg12N6_split, towerLeavesN6Face_split810, coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hr, coeff_eq_zero_of_natDegree_lt he, add_zero, add_zero, ht] at hz
  rw [hkface, mul_zero, sub_zero] at hz
  have hAne : A ≠ 0 := by intro h; simp [h] at ha
  have hAlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hscalar : (5 / 12288 : k) * (5 * A.leadingCoeff) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hAlc)
  exact (mul_eq_zero.mp (show ((5 / 12288 : k) * (5 * A.leadingCoeff)) * n5QuarticOpenIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 by simpa only [mul_assoc] using hz)).resolve_left hscalar


set_option maxHeartbeats 64000000 in
/-- The common degree envelope and the two refinement bounds isolate four
faces. The N6 face supplies the last equation of the tracked Open-I identity. -/
theorem quarticTowerLeaves_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hc : QuarticTowerLeavesDegrees810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (hDle : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree)
    (hEle : E.natDegree ≤ 2 * B.natDegree) : False := by
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticTowerLeaves_loadBands810 l beta gamma delta epsilon zeta eta theta A B C D E F G
      hc hprim homi hnu hkap
  have hk := towerLeavesOpenIKappaFace_zero810 l beta gamma delta epsilon zeta eta theta A B C D E F G
    hc hDle hEle hBne hCne hFne hGne hbl hbbeta hbdelta hbzeta hbtheta hkap
  have hm := towerLeavesOpenIMuFace_zero810 l beta gamma delta epsilon zeta eta theta A B C D E F G
    hc hDle hEle hBne hCne hFne hGne hbl hbbeta hbdelta hbzeta hbtheta hmu
  have hp := towerLeavesOpenIPiFace_zero810 l beta gamma delta epsilon zeta eta theta A B C D E F G
    hc hDle hEle hBne hCne hFne hGne hbl hbbeta hbdelta hbzeta hbtheta hpi
  have hn := towerLeavesOpenIN6_to_N5_zero810 l beta gamma delta epsilon zeta eta theta A B C D E F G
    hc hDle hEle hBne hCne hFne hGne hbl hbbeta hbdelta hbzeta hbtheta hprim homi hnu hk
  have hid := quarticOpenChamberI810_identity
    A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff
  rw [hk, hm, hp, hn, mul_zero, mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero] at hid
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (65536 : k) ≠ 0)
    (leadingCoeff_ne_zero.mpr hFne)) (pow_ne_zero 3 (leadingCoeff_ne_zero.mpr hGne))) hid.symm


set_option maxHeartbeats 64000000 in
/-- The refined BCDFG7 leaf 1 is impossible by the common quartic tower certificate. -/
theorem quarticUnownedLeaf_BCDFG7L1_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) = Polynomial.C (j / t))
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hc : QuarticChamberBCDFG7810 A B C D E F G)
    (h1 : A.natDegree + 2 * F.natDegree = 2 * G.natDegree)
    (h2 : 2 * F.natDegree = 2 * B.natDegree + G.natDegree)
    (h3 : F.natDegree = B.natDegree + C.natDegree)
    (h4 : A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree)
    (h5 : 2 * F.natDegree = A.natDegree + 4 * B.natDegree)
    (h6 : A.natDegree + 2 * F.natDegree = 4 * C.natDegree)
    (h7 : B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree)
    (h8 : C.natDegree + 2 * D.natDegree < 2 * F.natDegree)
    (h9 : C.natDegree + D.natDegree < A.natDegree + F.natDegree)
    (h10 : 3 * B.natDegree + D.natDegree < 2 * F.natDegree)
    (h11 : 3 * B.natDegree < A.natDegree + F.natDegree)
    (h12 : 2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree)
    (h13 : B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree)
    (h14 : A.natDegree + D.natDegree = F.natDegree)
    (h15 : A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + G.natDegree)
    (h16 : A.natDegree + D.natDegree = B.natDegree + C.natDegree)
    (h17 : D.natDegree + F.natDegree = 4 * B.natDegree)
    (h18 : A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + 2 * C.natDegree) : False := by
  have hprim := natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  rcases hc with ⟨hcellCone, hBne, hCne, hDfield, hEfield, hFne, hGne, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15⟩
  rcases hcellCone with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hEzero : E.natDegree = 0 := by simp [hEfield]
  have hdegrees : QuarticTowerLeavesDegrees810 A B C D E F G := by
    exact ⟨hcone, by omega, by omega, by omega, by omega, by omega⟩
  have hD : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree := by
    exact Or.inr (by omega)
  have hE : E.natDegree ≤ 2 * B.natDegree := by omega
  exact quarticTowerLeaves_impossible l beta gamma delta epsilon zeta eta theta A B C D E F G
    hprim hmu homi hkap hnu hpi hdegrees hBne hCne hFne hGne hD hE



set_option maxHeartbeats 64000000 in
/-- The refined BCEFG7 leaf 1 is impossible by the common quartic tower certificate. -/
theorem quarticUnownedLeaf_BCEFG7L1_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) = Polynomial.C (j / t))
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hc : QuarticChamberBCEFG7810 A B C D E F G)
    (h1 : A.natDegree + 2 * F.natDegree = 2 * G.natDegree)
    (h2 : 2 * F.natDegree = 2 * B.natDegree + G.natDegree)
    (h3 : F.natDegree = B.natDegree + C.natDegree)
    (h4 : A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree)
    (h5 : 2 * F.natDegree = A.natDegree + 4 * B.natDegree)
    (h6 : A.natDegree + 2 * F.natDegree = 4 * C.natDegree)
    (h7 : B.natDegree + E.natDegree < A.natDegree + F.natDegree)
    (h8 : C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree)
    (h9 : 3 * B.natDegree < A.natDegree + F.natDegree)
    (h10 : 2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree)
    (h11 : E.natDegree + G.natDegree = 2 * F.natDegree)
    (h12 : G.natDegree = A.natDegree + 2 * B.natDegree)
    (h13 : E.natDegree = 2 * B.natDegree)
    (h14 : E.natDegree + G.natDegree = B.natDegree + C.natDegree + F.natDegree)
    (h15 : G.natDegree = 2 * C.natDegree)
    (h16 : E.natDegree + G.natDegree = A.natDegree + 4 * B.natDegree)
    (h17 : E.natDegree + G.natDegree = 2 * B.natDegree + 2 * C.natDegree) : False := by
  have hprim := natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  rcases hc with ⟨hcellCone, hBne, hCne, hDfield, hEfield, hFne, hGne, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15⟩
  rcases hcellCone with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hDzero : D.natDegree = 0 := by simp [hDfield]
  have hdegrees : QuarticTowerLeavesDegrees810 A B C D E F G := by
    exact ⟨hcone, by omega, by omega, by omega, by omega, by omega⟩
  have hD : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree := by
    exact Or.inl hDfield
  have hE : E.natDegree ≤ 2 * B.natDegree := by omega
  exact quarticTowerLeaves_impossible l beta gamma delta epsilon zeta eta theta A B C D E F G
    hprim hmu homi hkap hnu hpi hdegrees hBne hCne hFne hGne hD hE



set_option maxHeartbeats 64000000 in
/-- The refined BCDEFG7 leaf 2 is impossible by the common quartic tower certificate. -/
theorem quarticUnownedLeaf_BCDEFG7L2_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) = Polynomial.C (j / t))
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hc : QuarticChamberBCDEFG7810 A B C D E F G)
    (h1 : A.natDegree + 2 * F.natDegree = 2 * G.natDegree)
    (h2 : 2 * F.natDegree = 2 * B.natDegree + G.natDegree)
    (h3 : F.natDegree = B.natDegree + C.natDegree)
    (h4 : A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree)
    (h5 : 2 * F.natDegree = A.natDegree + 4 * B.natDegree)
    (h6 : A.natDegree + 2 * F.natDegree = 4 * C.natDegree)
    (h7 : B.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree)
    (h8 : B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree)
    (h9 : B.natDegree + E.natDegree < A.natDegree + F.natDegree)
    (h10 : C.natDegree + 2 * D.natDegree < 2 * F.natDegree)
    (h11 : C.natDegree + D.natDegree < A.natDegree + F.natDegree)
    (h12 : C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree)
    (h13 : 2 * D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree)
    (h14 : 3 * B.natDegree + D.natDegree < 2 * F.natDegree)
    (h15 : 3 * B.natDegree < A.natDegree + F.natDegree)
    (h16 : 2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree)
    (h17 : 2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree)
    (h18 : B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree)
    (h19 : A.natDegree + D.natDegree + F.natDegree = E.natDegree + G.natDegree)
    (h20 : A.natDegree + D.natDegree = F.natDegree)
    (h21 : D.natDegree + F.natDegree = 2 * B.natDegree + E.natDegree)
    (h22 : A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + G.natDegree)
    (h23 : A.natDegree + D.natDegree = B.natDegree + C.natDegree)
    (h24 : A.natDegree + D.natDegree + F.natDegree = 2 * C.natDegree + E.natDegree)
    (h25 : D.natDegree + F.natDegree = 4 * B.natDegree)
    (h26 : A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + 2 * C.natDegree) : False := by
  have hprim := natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  rcases hc with ⟨hcellCone, hBne, hCne, hDfield, hEfield, hFne, hGne, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22⟩
  rcases hcellCone with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hdegrees : QuarticTowerLeavesDegrees810 A B C D E F G := by
    exact ⟨hcone, by omega, by omega, by omega, by omega, by omega⟩
  have hD : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree := by
    exact Or.inr (by omega)
  have hE : E.natDegree ≤ 2 * B.natDegree := by omega
  exact quarticTowerLeaves_impossible l beta gamma delta epsilon zeta eta theta A B C D E F G
    hprim hmu homi hkap hnu hpi hdegrees hBne hCne hFne hGne hD hE



set_option maxHeartbeats 64000000 in
/-- The refined BCDEFG7 leaf 3 is impossible by the common quartic tower certificate. -/
theorem quarticUnownedLeaf_BCDEFG7L3_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) = Polynomial.C (j / t))
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hc : QuarticChamberBCDEFG7810 A B C D E F G)
    (h1 : A.natDegree + 2 * F.natDegree = 2 * G.natDegree)
    (h2 : 2 * F.natDegree = 2 * B.natDegree + G.natDegree)
    (h3 : F.natDegree = B.natDegree + C.natDegree)
    (h4 : A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree)
    (h5 : 2 * F.natDegree = A.natDegree + 4 * B.natDegree)
    (h6 : A.natDegree + 2 * F.natDegree = 4 * C.natDegree)
    (h7 : B.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree)
    (h8 : B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree)
    (h9 : B.natDegree + E.natDegree < A.natDegree + F.natDegree)
    (h10 : C.natDegree + 2 * D.natDegree < 2 * F.natDegree)
    (h11 : C.natDegree + D.natDegree < A.natDegree + F.natDegree)
    (h12 : C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree)
    (h13 : 2 * D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree)
    (h14 : 3 * B.natDegree + D.natDegree < 2 * F.natDegree)
    (h15 : 3 * B.natDegree < A.natDegree + F.natDegree)
    (h16 : 2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree)
    (h17 : 2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree)
    (h18 : B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree)
    (h19 : A.natDegree + D.natDegree = F.natDegree)
    (h20 : A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + G.natDegree)
    (h21 : A.natDegree + D.natDegree = B.natDegree + C.natDegree)
    (h22 : D.natDegree + F.natDegree = 4 * B.natDegree)
    (h23 : A.natDegree + D.natDegree + F.natDegree = 2 * B.natDegree + 2 * C.natDegree)
    (h24 : E.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree)
    (h25 : 2 * B.natDegree + E.natDegree < D.natDegree + F.natDegree)
    (h26 : 2 * C.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) : False := by
  have hprim := natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  rcases hc with ⟨hcellCone, hBne, hCne, hDfield, hEfield, hFne, hGne, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22⟩
  rcases hcellCone with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hdegrees : QuarticTowerLeavesDegrees810 A B C D E F G := by
    exact ⟨hcone, by omega, by omega, by omega, by omega, by omega⟩
  have hD : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree := by
    exact Or.inr (by omega)
  have hE : E.natDegree ≤ 2 * B.natDegree := by omega
  exact quarticTowerLeaves_impossible l beta gamma delta epsilon zeta eta theta A B C D E F G
    hprim hmu homi hkap hnu hpi hdegrees hBne hCne hFne hGne hD hE



set_option maxHeartbeats 64000000 in
/-- The refined BCDEFG7 leaf 5 is impossible by the common quartic tower certificate. -/
theorem quarticUnownedLeaf_BCDEFG7L5_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) = Polynomial.C (j / t))
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hc : QuarticChamberBCDEFG7810 A B C D E F G)
    (h1 : A.natDegree + 2 * F.natDegree = 2 * G.natDegree)
    (h2 : 2 * F.natDegree = 2 * B.natDegree + G.natDegree)
    (h3 : F.natDegree = B.natDegree + C.natDegree)
    (h4 : A.natDegree + 2 * F.natDegree = 2 * C.natDegree + G.natDegree)
    (h5 : 2 * F.natDegree = A.natDegree + 4 * B.natDegree)
    (h6 : A.natDegree + 2 * F.natDegree = 4 * C.natDegree)
    (h7 : B.natDegree + D.natDegree + E.natDegree < 2 * F.natDegree)
    (h8 : B.natDegree + D.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree)
    (h9 : B.natDegree + E.natDegree < A.natDegree + F.natDegree)
    (h10 : C.natDegree + 2 * D.natDegree < 2 * F.natDegree)
    (h11 : C.natDegree + D.natDegree < A.natDegree + F.natDegree)
    (h12 : C.natDegree + 2 * E.natDegree < A.natDegree + 2 * F.natDegree)
    (h13 : 2 * D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree)
    (h14 : 3 * B.natDegree + D.natDegree < 2 * F.natDegree)
    (h15 : 3 * B.natDegree < A.natDegree + F.natDegree)
    (h16 : 2 * B.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree)
    (h17 : 2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree)
    (h18 : B.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree)
    (h19 : E.natDegree + G.natDegree = 2 * F.natDegree)
    (h20 : G.natDegree = A.natDegree + 2 * B.natDegree)
    (h21 : E.natDegree = 2 * B.natDegree)
    (h22 : E.natDegree + G.natDegree = B.natDegree + C.natDegree + F.natDegree)
    (h23 : G.natDegree = 2 * C.natDegree)
    (h24 : E.natDegree + G.natDegree = A.natDegree + 4 * B.natDegree)
    (h25 : E.natDegree + G.natDegree = 2 * B.natDegree + 2 * C.natDegree)
    (h26 : A.natDegree + D.natDegree + F.natDegree < E.natDegree + G.natDegree)
    (h27 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree)
    (h28 : B.natDegree + D.natDegree < G.natDegree)
    (h29 : C.natDegree + 2 * D.natDegree < E.natDegree + G.natDegree)
    (h30 : 3 * B.natDegree + D.natDegree < E.natDegree + G.natDegree) : False := by
  have hprim := natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  rcases hc with ⟨hcellCone, hBne, hCne, hDfield, hEfield, hFne, hGne, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22⟩
  rcases hcellCone with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  have hdegrees : QuarticTowerLeavesDegrees810 A B C D E F G := by
    exact ⟨hcone, by omega, by omega, by omega, by omega, by omega⟩
  have hD : D = 0 ∨ A.natDegree + D.natDegree ≤ F.natDegree := by
    exact Or.inr (by omega)
  have hE : E.natDegree ≤ 2 * B.natDegree := by omega
  exact quarticTowerLeaves_impossible l beta gamma delta epsilon zeta eta theta A B C D E F G
    hprim hmu homi hkap hnu hpi hdegrees hBne hCne hFne hGne hD hE


end Max11DegreeRoutes

#print axioms Max11DegreeRoutes.quarticUnownedLeaf_BCDFG7L1_impossible
#print axioms Max11DegreeRoutes.quarticUnownedLeaf_BCEFG7L1_impossible
#print axioms Max11DegreeRoutes.quarticUnownedLeaf_BCDEFG7L2_impossible
#print axioms Max11DegreeRoutes.quarticUnownedLeaf_BCDEFG7L3_impossible
#print axioms Max11DegreeRoutes.quarticUnownedLeaf_BCDEFG7L5_impossible
