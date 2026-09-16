import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Astra810ScaleZeroQuarticChamberBCDEFG12Part101Scratch
import Max11SpeedReflectDegLibScratch

/-! # BCDEFG12 chamber, part 3

One piece of the `Astra810ScaleZeroQuarticChamberBCDEFG12Scratch` module, split out so each
compilation unit stays inside the runner memory budget.  Public statements
are byte-identical to the single-module version.
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
/-- Reflected monomial data for `bandAuxBCDEFG12RestTheta1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestTheta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestTheta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 32 * theta : k), (-(1 / 64 * theta) : k), (1 / 4 * theta : k),
      (-(1 / 8 * theta) : k), (-(1 / 16 * theta) : k), (1 / 1 * theta : k)
      ]
      [
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [bandAuxBCDEFG12RestTheta1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestEta1810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestEta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestEta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 64 * eta : k), (-(1 / 4 * eta) : k), (-(1 / 4 * eta) : k)
      ]
      [
      [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestEta1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestZeta2810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestZeta2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestZeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 8 * zeta) : k), (-(3 / 16 * zeta) : k), (3 / 128 * zeta : k),
      (3 / 8 * zeta : k)
      ]
      [
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [bandAuxBCDEFG12RestZeta2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestZeta1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestZeta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestZeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 * zeta : k), (-(3 / 512 * zeta) : k), (3 / 32 * zeta : k),
      (-(3 / 64 * zeta) : k), (27 / 128 * zeta : k), (-(3 / 8 * zeta) : k)
      ]
      [
      [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestZeta1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestEpsilon1810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestEpsilon1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestEpsilon1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 32 * epsilon : k), (1 / 4 * epsilon : k), (-(1 / 2 * epsilon) : k),
      (-(1 / 2 * epsilon) : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestEpsilon1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestDelta3810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestDelta3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestDelta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 8 * delta) : k), (-(5 / 16 * delta) : k), (-(5 / 64 * delta) : k),
      (15 / 128 * delta : k)
      ]
      [
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [1, 1, 0, 0, 0, 1, 0], [2, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [bandAuxBCDEFG12RestDelta3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestDelta2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestDelta2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestDelta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 64 * delta : k), (-(5 / 128 * delta) : k), (-(135 / 4096 * delta) : k),
      (25 / 128 * delta : k), (15 / 32 * delta : k), (5 / 64 * delta : k)
      ]
      [
      [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestDelta2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestDelta1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestDelta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestDelta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 4096 * delta : k), (-(15 / 8192 * delta) : k), (15 / 512 * delta : k),
      (-(15 / 1024 * delta) : k), (45 / 2048 * delta : k), (-(5 / 1024 * delta) : k)
      ]
      [
      [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0],
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestDelta1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestGamma1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestGamma1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestGamma1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(27 / 256 * gamma) : k), (9 / 64 * gamma : k), (3 / 8 * gamma : k),
      (3 / 16 * gamma : k), (3 / 16 * gamma : k), (-(3 / 4 * gamma) : k)
      ]
      [
      [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestGamma1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestBeta4810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestBeta4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestBeta4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 64 * beta) : k), (-(21 / 1024 * beta) : k), (35 / 1024 * beta : k),
      (7 / 32 * beta : k)
      ]
      [
      [1, 0, 0, 1, 0, 1, 0], [2, 1, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 1], [1, 0, 1, 0, 0, 0, 1]
      ] := by
  simp only [bandAuxBCDEFG12RestBeta4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestBeta3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestBeta3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestBeta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(91 / 1024 * beta) : k), (7 / 32 * beta : k), (7 / 32 * beta : k),
      (7 / 64 * beta : k), (7 / 64 * beta : k), (-(7 / 16 * beta) : k)
      ]
      [
      [0, 2, 2, 0, 0, 0, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestBeta3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestBeta2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestBeta2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestBeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 1024 * beta : k), (-(21 / 2048 * beta) : k), (49 / 32768 * beta : k),
      (-(7 / 1024 * beta) : k), (7 / 128 * beta : k), (-(7 / 128 * beta) : k)
      ]
      [
      [2, 0, 1, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0],
      [1, 0, 0, 0, 2, 0, 0], [0, 3, 0, 1, 0, 0, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestBeta2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestBeta1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestBeta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestBeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (315 / 131072 * beta : k), (-(35 / 65536 * beta) : k), (35 / 4096 * beta : k),
      (-(35 / 8192 * beta) : k), (175 / 16384 * beta : k), (-(7 / 16384 * beta) : k)
      ]
      [
      [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0],
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestBeta1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestL6810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 128 * l) : k), (-(9 / 32 * l) : k), (-(9 / 64 * l) : k),
      (-(9 / 64 * l) : k), (9 / 16 * l : k)
      ]
      [
      [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0],
      [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [bandAuxBCDEFG12RestL6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestL5810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 256 * l : k), (45 / 512 * l : k), (189 / 1024 * l : k),
      (-(9 / 64 * l) : k), (-(9 / 32 * l) : k), (63 / 4096 * l : k)
      ]
      [
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1],
      [0, 1, 0, 0, 1, 1, 0], [0, 0, 4, 0, 0, 0, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestL5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestL4810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 2048 * l) : k), (-(9 / 512 * l) : k), (9 / 32 * l : k),
      (-(9 / 128 * l) : k), (-(567 / 16384 * l) : k), (27 / 512 * l : k)
      ]
      [
      [1, 2, 2, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 0, 0, 2, 0],
      [0, 4, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestL4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestL3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 4096 * l) : k), (9 / 8192 * l : k), (27 / 256 * l : k),
      (-(27 / 1024 * l) : k), (81 / 2048 * l : k), (-(27 / 4096 * l) : k)
      ]
      [
      [2, 1, 1, 1, 0, 0, 0], [2, 0, 3, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0],
      [2, 0, 0, 0, 2, 0, 0], [1, 3, 0, 1, 0, 0, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestL3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestL2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(81 / 131072 * l) : k), (-(45 / 8192 * l) : k), (225 / 8192 * l : k),
      (-(45 / 16384 * l) : k), (-(45 / 524288 * l) : k), (-(45 / 16384 * l) : k)
      ]
      [
      [3, 2, 1, 0, 0, 0, 0], [3, 1, 0, 0, 0, 1, 0], [3, 0, 1, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0],
      [2, 4, 0, 0, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestL2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestL1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (693 / 1048576 * l : k), (-(315 / 2097152 * l) : k), (315 / 131072 * l : k),
      (-(315 / 262144 * l) : k), (2205 / 524288 * l : k), (315 / 32768 * l : k)
      ]
      [
      [6, 0, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0], [4, 1, 0, 1, 0, 0, 0],
      [4, 0, 2, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [bandAuxBCDEFG12RestL1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestFree3810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestFree3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestFree3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(5 / 8) : k), (-(5 / 16) : k),
      (-(5 / 16) : k), (-(15 / 512) : k)
      ]
      [
      [0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0],
      [1, 2, 1, 1, 0, 0, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestFree3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestFree2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestFree2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestFree2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (85 / 256 : k), (45 / 128 : k), (45 / 128 : k),
      (-(5 / 16) : k), (-(5 / 16) : k), (15 / 128 : k)
      ]
      [
      [0, 2, 0, 1, 1, 0, 0], [0, 1, 2, 0, 1, 0, 0], [0, 1, 1, 2, 0, 0, 0], [0, 1, 0, 0, 1, 0, 1],
      [0, 1, 0, 0, 0, 2, 0], [0, 0, 3, 1, 0, 0, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestFree2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `bandAuxBCDEFG12RestFree1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestFree1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    bandAuxBCDEFG12RestFree1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (23 / 8192 : k), (-(5 / 512) : k), (-(125 / 2048) : k),
      (-(265 / 2048) : k), (15 / 256 : k), (85 / 256 : k)
      ]
      [
      [1, 5, 0, 0, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0], [0, 4, 0, 1, 0, 0, 0], [0, 3, 2, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 1, 0]
      ] := by
  simp only [bandAuxBCDEFG12RestFree1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, neg_smul, add_assoc]
  all_goals rfl


set_option maxHeartbeats 64000000 in
/-- Every non-pure auxiliary monomial is strictly below the candidate pure load degree, including equality at the old tower face. -/
theorem bandAuxBCDEFG12Rest810_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hd : 5 * A.natDegree + 8 * B.natDegree ≤ 2 * d)
    (hl : l = 0 ∨ 8 * A.natDegree ≤ d)
    (hbeta : beta = 0 ∨ 7 * A.natDegree ≤ d)
    (hdelta : delta = 0 ∨ 6 * A.natDegree ≤ d)
    (hzeta : zeta = 0 ∨ 5 * A.natDegree ≤ d)
    (htheta : theta = 0 ∨ 4 * A.natDegree ≤ d)
    : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  simp only [QuarticChamberBCDEFG12810, QuarticRatioConeA810] at hc
  rcases hc with ⟨⟨ha, hab, hac, had, hae, haf, hag⟩, hB, hC, hD, hE, hF, hG,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22⟩
  have hc0 : (bandAuxBCDEFG12RestFree1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestFree1810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc1 : (bandAuxBCDEFG12RestFree2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestFree2810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc2 : (bandAuxBCDEFG12RestFree3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestFree3810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc3 : (bandAuxBCDEFG12RestL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestL1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL1810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc4 : (bandAuxBCDEFG12RestL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestL2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL2810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc5 : (bandAuxBCDEFG12RestL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestL3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL3810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc6 : (bandAuxBCDEFG12RestL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestL4810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL4810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc7 : (bandAuxBCDEFG12RestL5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestL5810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL5810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc8 : (bandAuxBCDEFG12RestL6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestL6810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestL6810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc9 : (bandAuxBCDEFG12RestBeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestBeta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestBeta1810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc10 : (bandAuxBCDEFG12RestBeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestBeta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestBeta2810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc11 : (bandAuxBCDEFG12RestBeta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestBeta3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestBeta3810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc12 : (bandAuxBCDEFG12RestBeta4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestBeta4810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestBeta4810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc13 : (bandAuxBCDEFG12RestGamma1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestGamma1810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc14 : (bandAuxBCDEFG12RestDelta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestDelta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestDelta1810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc15 : (bandAuxBCDEFG12RestDelta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestDelta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestDelta2810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc16 : (bandAuxBCDEFG12RestDelta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestDelta3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestDelta3810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc17 : (bandAuxBCDEFG12RestEpsilon1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestEpsilon1810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc18 : (bandAuxBCDEFG12RestZeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hzeta with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestZeta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestZeta1810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc19 : (bandAuxBCDEFG12RestZeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hzeta with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestZeta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestZeta2810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  have hc20 : (bandAuxBCDEFG12RestEta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestEta1810]
    apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
      max_lt_iff]
    repeat' apply And.intro
    all_goals omega
  have hc21 : (bandAuxBCDEFG12RestTheta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases htheta with hz | hdload
    ·
      simp only [bandAuxBCDEFG12RestTheta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    ·
      rw [astra4kRefl_ChamberBCDEFG12Part03_bandAuxBCDEFG12RestTheta1810]
      apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        max_lt_iff]
      repeat' apply And.intro
      all_goals omega
  simp only [bandAuxBCDEFG12Rest810]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc0 hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9) hc10) hc11) hc12) hc13) hc14) hc15) hc16) hc17) hc18) hc19) hc20) hc21)

end Max11DegreeRoutes
