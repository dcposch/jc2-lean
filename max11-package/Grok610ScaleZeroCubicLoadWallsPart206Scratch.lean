import Grok610ScaleZeroCubicLoadWallsPart205Scratch

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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicCDWallZetaRest610` (15 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicCDWallZetaRest610_eq_polyOf
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicCDWallZetaRest610 alpha epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (20 / 243 : k), (-(10 / 27) : k),
      (-(5 / 27) : k), (4 / 243 * alpha : k), (-(4 / 27 * alpha) : k),
      (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (-(2 / 9 * epsilon) : k),
      (1 / 12 * zeta : k), (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 24 * theta : k), (1 / 6 * theta : k)]
      [
      [1, 2, 0, 1, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [0, 1, 1, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]] := by
  simp only [degreeZeroN1CubicCDWallZetaRest610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicCDWallThetaRest610` (11 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicCDWallThetaRest610_eq_polyOf
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicCDWallThetaRest610 alpha epsilon eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (20 / 243 : k), (-(10 / 27) : k),
      (-(5 / 27) : k), (4 / 243 * alpha : k), (-(4 / 27 * alpha) : k),
      (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (-(2 / 9 * epsilon) : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 2, 0, 1, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [0, 1, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0]] := by
  simp only [degreeZeroN1CubicCDWallThetaRest610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN2CubicCDWallBetaRest610 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallBetaRest610_chunk3 alpha beta delta epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicCDWallBetaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicCDWallBetaRest610_chunk0_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 81) : k), (-(25 / 243) : k), (-(4 / 243) : k),
      (10 / 27 : k), (5 / 27 : k), (10 / 81 : k),
      (5 / 9 : k), (5 / 27 : k), (-(10 / 9) : k),
      (-(10 / 27) : k), (-(4 / 243 * alpha) : k), (4 / 27 * alpha : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k)]
      [
      [2, 2, 0, 1, 0], [1, 3, 1, 0, 0], [0, 5, 0, 0, 0], [1, 1, 1, 0, 1],
      [1, 1, 0, 2, 0], [0, 3, 0, 0, 1], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
      [0, 0, 1, 1, 1], [0, 0, 0, 3, 0], [2, 3, 0, 0, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1]] := by
  simp only [degreeZeroN2CubicCDWallBetaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicCDWallBetaRest610_chunk1` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicCDWallBetaRest610_chunk1_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (35 / 2592 * beta : k),
      (-(7 / 1296 * beta) : k), (7 / 216 * beta : k), (-(7 / 432 * beta) : k),
      (49 / 864 * beta : k), (35 / 432 * beta : k), (35 / 1728 * beta : k),
      (7 / 36 * beta : k), (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k),
      (-(7 / 18 * beta) : k), (-(7 / 108 * beta) : k), (7 / 12 * beta : k),
      (7 / 2592 * delta : k)]
      [
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0],
      [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0],
      [0, 4, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [5, 0, 0, 0, 0]] := by
  simp only [degreeZeroN2CubicCDWallBetaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicCDWallBetaRest610_chunk2` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicCDWallBetaRest610_chunk2_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicCDWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 144 * delta : k), (-(25 / 864 * delta) : k), (5 / 72 * delta : k),
      (5 / 36 * delta : k), (5 / 36 * delta : k), (-(5 / 12 * delta) : k),
      (2 / 9 * epsilon : k), (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k),
      (5 / 576 * zeta : k), (1 / 12 * zeta : k), (1 / 12 * zeta : k),
      (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k), (-(1 / 3 * eta) : k),
      (-(1 / 3 * eta) : k)]
      [
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
      [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
      [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0]] := by
  simp only [degreeZeroN2CubicCDWallBetaRest610_chunk2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicCDWallBetaRest610_chunk3` (4 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicCDWallBetaRest610_chunk3_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicCDWallBetaRest610_chunk3 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (1 / 36 * theta : k), (1 / 6 * theta : k), (-(1 / 12 * theta) : k),
      (1 * theta : k)]
      [
      [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] := by
  simp only [degreeZeroN2CubicCDWallBetaRest610_chunk3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN2CubicCDWallDeltaRest610 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallDeltaRest610_chunk2 alpha delta epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicCDWallDeltaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicCDWallDeltaRest610_chunk0_eq_polyOf
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 81) : k), (-(25 / 243) : k), (-(4 / 243) : k),
      (10 / 27 : k), (5 / 27 : k), (10 / 81 : k),
      (5 / 9 : k), (5 / 27 : k), (-(10 / 9) : k),
      (-(10 / 27) : k), (-(4 / 243 * alpha) : k), (4 / 27 * alpha : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k)]
      [
      [2, 2, 0, 1, 0], [1, 3, 1, 0, 0], [0, 5, 0, 0, 0], [1, 1, 1, 0, 1],
      [1, 1, 0, 2, 0], [0, 3, 0, 0, 1], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
      [0, 0, 1, 1, 1], [0, 0, 0, 3, 0], [2, 3, 0, 0, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1]] := by
  simp only [degreeZeroN2CubicCDWallDeltaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicCDWallDeltaRest610_chunk1` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicCDWallDeltaRest610_chunk1_eq_polyOf
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (5 / 144 * delta : k),
      (-(25 / 864 * delta) : k), (5 / 72 * delta : k), (5 / 36 * delta : k),
      (5 / 36 * delta : k), (-(5 / 12 * delta) : k), (2 / 9 * epsilon : k),
      (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k), (5 / 576 * zeta : k),
      (1 / 12 * zeta : k), (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k),
      (-(1 / 4 * zeta) : k)]
      [
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
      [2, 0, 0, 0, 1], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 0, 2, 0],
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0]] := by
  simp only [degreeZeroN2CubicCDWallDeltaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicCDWallDeltaRest610_chunk2` (6 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicCDWallDeltaRest610_chunk2_eq_polyOf
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicCDWallDeltaRest610_chunk2 alpha delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k), (1 / 36 * theta : k),
      (1 / 6 * theta : k), (-(1 / 12 * theta) : k), (1 * theta : k)]
      [
      [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] := by
  simp only [degreeZeroN2CubicCDWallDeltaRest610_chunk2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN2CubicCDWallZetaRest610 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicCDWallZetaRest610_chunk0 alpha epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicCDWallZetaRest610_chunk1 alpha epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicCDWallZetaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicCDWallZetaRest610_chunk0_eq_polyOf
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicCDWallZetaRest610_chunk0 alpha epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 81) : k), (-(25 / 243) : k), (-(4 / 243) : k),
      (10 / 27 : k), (5 / 27 : k), (10 / 81 : k),
      (5 / 9 : k), (5 / 27 : k), (-(10 / 9) : k),
      (-(10 / 27) : k), (-(4 / 243 * alpha) : k), (4 / 27 * alpha : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k)]
      [
      [2, 2, 0, 1, 0], [1, 3, 1, 0, 0], [0, 5, 0, 0, 0], [1, 1, 1, 0, 1],
      [1, 1, 0, 2, 0], [0, 3, 0, 0, 1], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
      [0, 0, 1, 1, 1], [0, 0, 0, 3, 0], [2, 3, 0, 0, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1]] := by
  simp only [degreeZeroN2CubicCDWallZetaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicCDWallZetaRest610_chunk1` (15 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicCDWallZetaRest610_chunk1_eq_polyOf
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicCDWallZetaRest610_chunk1 alpha epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (2 / 9 * epsilon : k),
      (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k), (1 / 12 * zeta : k),
      (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k),
      (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k), (1 / 36 * theta : k),
      (1 / 6 * theta : k), (-(1 / 12 * theta) : k), (1 * theta : k)]
      [
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
      [0, 0, 1, 1, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0],
      [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] := by
  simp only [degreeZeroN2CubicCDWallZetaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN2CubicCDWallThetaRest610 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicCDWallThetaRest610_chunk0 alpha epsilon eta theta A B C D E) +
  (degreeZeroN2CubicCDWallThetaRest610_chunk1 alpha epsilon eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicCDWallThetaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicCDWallThetaRest610_chunk0_eq_polyOf
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicCDWallThetaRest610_chunk0 alpha epsilon eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 81) : k), (-(25 / 243) : k), (-(4 / 243) : k),
      (10 / 27 : k), (5 / 27 : k), (10 / 81 : k),
      (5 / 9 : k), (5 / 27 : k), (-(10 / 9) : k),
      (-(10 / 27) : k), (-(4 / 243 * alpha) : k), (4 / 27 * alpha : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k)]
      [
      [2, 2, 0, 1, 0], [1, 3, 1, 0, 0], [0, 5, 0, 0, 0], [1, 1, 1, 0, 1],
      [1, 1, 0, 2, 0], [0, 3, 0, 0, 1], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
      [0, 0, 1, 1, 1], [0, 0, 0, 3, 0], [2, 3, 0, 0, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1]] := by
  simp only [degreeZeroN2CubicCDWallThetaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicCDWallThetaRest610_chunk1` (10 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicCDWallThetaRest610_chunk1_eq_polyOf
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicCDWallThetaRest610_chunk1 alpha epsilon eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (2 / 9 * epsilon : k),
      (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k), (-(1 / 3 * eta) : k),
      (-(1 / 3 * eta) : k), (1 / 6 * theta : k), (-(1 / 12 * theta) : k),
      (1 * theta : k)]
      [
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
      [0, 0, 1, 1, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [1, 0, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] := by
  simp only [degreeZeroN2CubicCDWallThetaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN1CubicBCDEWallBetaRest610 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN1CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN1CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicBCDEWallBetaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicBCDEWallBetaRest610_chunk0_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (20 / 243 : k), (-(5 / 27) : k), (4 / 243 * alpha : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (35 / 2592 * beta : k), (-(7 / 5184 * beta) : k), (7 / 144 * beta : k),
      (-(7 / 216 * beta) : k), (7 / 432 * beta : k), (-(35 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 72 * beta : k), (35 / 10368 * delta : k),
      (5 / 144 * delta : k)]
      [
      [0, 3, 1, 0, 0], [0, 1, 0, 2, 0], [1, 3, 0, 0, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
      [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0]] := by
  simp only [degreeZeroN1CubicBCDEWallBetaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicBCDEWallBetaRest610_chunk1` (12 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicBCDEWallBetaRest610_chunk1_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 36 * delta) : k),
      (-(5 / 72 * delta) : k), (-(2 / 9 * epsilon) : k), (5 / 432 * zeta : k),
      (1 / 12 * zeta : k), (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 24 * theta : k), (1 / 6 * theta : k)]
      [
      [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
      [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]] := by
  simp only [degreeZeroN1CubicBCDEWallBetaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN1CubicBCDEWallDeltaRest610 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN1CubicBCDEWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN1CubicBCDEWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicBCDEWallDeltaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicBCDEWallDeltaRest610_chunk0_eq_polyOf
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicBCDEWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (20 / 243 : k), (-(5 / 27) : k), (4 / 243 * alpha : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (5 / 144 * delta : k), (5 / 432 * delta : k), (5 / 36 * delta : k),
      (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k), (-(2 / 9 * epsilon) : k),
      (5 / 432 * zeta : k), (1 / 12 * zeta : k), (-(1 / 8 * zeta) : k),
      (1 / 2 * zeta : k)]
      [
      [0, 3, 1, 0, 0], [0, 1, 0, 2, 0], [1, 3, 0, 0, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
      [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [0, 1, 1, 0, 0],
      [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] := by
  simp only [degreeZeroN1CubicBCDEWallDeltaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicBCDEWallDeltaRest610_chunk1` (3 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicBCDEWallDeltaRest610_chunk1_eq_polyOf
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicBCDEWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (1 / 3 * eta : k), (1 / 24 * theta : k), (1 / 6 * theta : k)]
      [
      [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]] := by
  simp only [degreeZeroN1CubicBCDEWallDeltaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicBCDEWallZetaRest610` (13 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicBCDEWallZetaRest610_eq_polyOf
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicBCDEWallZetaRest610 alpha epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (20 / 243 : k), (-(5 / 27) : k), (4 / 243 * alpha : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (-(2 / 9 * epsilon) : k), (1 / 12 * zeta : k), (-(1 / 8 * zeta) : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 24 * theta : k),
      (1 / 6 * theta : k)]
      [
      [0, 3, 1, 0, 0], [0, 1, 0, 2, 0], [1, 3, 0, 0, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [0, 1, 1, 0, 0], [1, 0, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0]] := by
  simp only [degreeZeroN1CubicBCDEWallZetaRest610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicBCDEWallThetaRest610` (9 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicBCDEWallThetaRest610_eq_polyOf
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicBCDEWallThetaRest610 alpha epsilon eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (20 / 243 : k), (-(5 / 27) : k), (4 / 243 * alpha : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (-(2 / 9 * epsilon) : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [0, 3, 1, 0, 0], [0, 1, 0, 2, 0], [1, 3, 0, 0, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [0, 1, 1, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0]] := by
  simp only [degreeZeroN1CubicBCDEWallThetaRest610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN2CubicBCDEWallBetaRest610 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallBetaRest610_chunk3 alpha beta delta epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicBCDEWallBetaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicBCDEWallBetaRest610_chunk0_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicBCDEWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(25 / 243) : k), (-(4 / 243) : k), (5 / 27 : k),
      (10 / 81 : k), (5 / 9 : k), (5 / 27 : k),
      (-(10 / 9) : k), (-(10 / 27) : k), (-(4 / 243 * alpha) : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k)]
      [
      [1, 3, 1, 0, 0], [0, 5, 0, 0, 0], [1, 1, 0, 2, 0], [0, 3, 0, 0, 1],
      [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0],
      [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
      [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0]] := by
  simp only [degreeZeroN2CubicBCDEWallBetaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicBCDEWallBetaRest610_chunk1` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicBCDEWallBetaRest610_chunk1_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicBCDEWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (35 / 2592 * beta : k), (-(7 / 1296 * beta) : k), (7 / 216 * beta : k),
      (-(7 / 432 * beta) : k), (49 / 864 * beta : k), (35 / 432 * beta : k),
      (35 / 1728 * beta : k), (7 / 36 * beta : k), (-(7 / 36 * beta) : k),
      (-(7 / 72 * beta) : k), (-(7 / 18 * beta) : k), (-(7 / 108 * beta) : k),
      (7 / 12 * beta : k), (7 / 2592 * delta : k), (5 / 144 * delta : k),
      (-(25 / 864 * delta) : k)]
      [
      [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
      [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1],
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0]] := by
  simp only [degreeZeroN2CubicBCDEWallBetaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicBCDEWallBetaRest610_chunk2` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicBCDEWallBetaRest610_chunk2_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicBCDEWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 72 * delta : k), (5 / 36 * delta : k), (5 / 36 * delta : k),
      (-(5 / 12 * delta) : k), (2 / 9 * epsilon : k), (2 / 27 * epsilon : k),
      (-(2 / 3 * epsilon) : k), (5 / 576 * zeta : k), (1 / 12 * zeta : k),
      (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k),
      (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k), (1 / 36 * theta : k),
      (1 / 6 * theta : k)]
      [
      [2, 0, 0, 0, 1], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 0, 2, 0],
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
      [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0]] := by
  simp only [degreeZeroN2CubicBCDEWallBetaRest610_chunk2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicBCDEWallBetaRest610_chunk3` (2 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicBCDEWallBetaRest610_chunk3_eq_polyOf
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicBCDEWallBetaRest610_chunk3 alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(1 / 12 * theta) : k), (1 * theta : k)]
      [
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] := by
  simp only [degreeZeroN2CubicBCDEWallBetaRest610_chunk3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN2CubicBCDEWallDeltaRest610 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicBCDEWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallDeltaRest610_chunk2 alpha delta epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicBCDEWallDeltaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicBCDEWallDeltaRest610_chunk0_eq_polyOf
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicBCDEWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(25 / 243) : k), (-(4 / 243) : k), (5 / 27 : k),
      (10 / 81 : k), (5 / 9 : k), (5 / 27 : k),
      (-(10 / 9) : k), (-(10 / 27) : k), (-(4 / 243 * alpha) : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k)]
      [
      [1, 3, 1, 0, 0], [0, 5, 0, 0, 0], [1, 1, 0, 2, 0], [0, 3, 0, 0, 1],
      [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0],
      [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
      [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0]] := by
  simp only [degreeZeroN2CubicBCDEWallDeltaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicBCDEWallDeltaRest610_chunk1` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicBCDEWallDeltaRest610_chunk1_eq_polyOf
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicBCDEWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 144 * delta : k), (-(25 / 864 * delta) : k), (5 / 72 * delta : k),
      (5 / 36 * delta : k), (5 / 36 * delta : k), (-(5 / 12 * delta) : k),
      (2 / 9 * epsilon : k), (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k),
      (5 / 576 * zeta : k), (1 / 12 * zeta : k), (1 / 12 * zeta : k),
      (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k), (-(1 / 3 * eta) : k),
      (-(1 / 3 * eta) : k)]
      [
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0],
      [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
      [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0]] := by
  simp only [degreeZeroN2CubicBCDEWallDeltaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicBCDEWallDeltaRest610_chunk2` (4 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicBCDEWallDeltaRest610_chunk2_eq_polyOf
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicBCDEWallDeltaRest610_chunk2 alpha delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (1 / 36 * theta : k), (1 / 6 * theta : k), (-(1 / 12 * theta) : k),
      (1 * theta : k)]
      [
      [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] := by
  simp only [degreeZeroN2CubicBCDEWallDeltaRest610_chunk2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN2CubicBCDEWallZetaRest610 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicBCDEWallZetaRest610_chunk0 alpha epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallZetaRest610_chunk1 alpha epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicBCDEWallZetaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicBCDEWallZetaRest610_chunk0_eq_polyOf
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicBCDEWallZetaRest610_chunk0 alpha epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(25 / 243) : k), (-(4 / 243) : k), (5 / 27 : k),
      (10 / 81 : k), (5 / 9 : k), (5 / 27 : k),
      (-(10 / 9) : k), (-(10 / 27) : k), (-(4 / 243 * alpha) : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k)]
      [
      [1, 3, 1, 0, 0], [0, 5, 0, 0, 0], [1, 1, 0, 2, 0], [0, 3, 0, 0, 1],
      [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0],
      [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
      [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0]] := by
  simp only [degreeZeroN2CubicBCDEWallZetaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicBCDEWallZetaRest610_chunk1` (13 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicBCDEWallZetaRest610_chunk1_eq_polyOf
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicBCDEWallZetaRest610_chunk1 alpha epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (2 / 9 * epsilon : k), (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k),
      (1 / 12 * zeta : k), (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k),
      (-(1 / 4 * zeta) : k), (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k),
      (1 / 36 * theta : k), (1 / 6 * theta : k), (-(1 / 12 * theta) : k),
      (1 * theta : k)]
      [
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1]] := by
  simp only [degreeZeroN2CubicBCDEWallZetaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN2CubicBCDEWallThetaRest610 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicBCDEWallThetaRest610_chunk0 alpha epsilon eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallThetaRest610_chunk1 alpha epsilon eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicBCDEWallThetaRest610_chunk0` (16 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicBCDEWallThetaRest610_chunk0_eq_polyOf
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicBCDEWallThetaRest610_chunk0 alpha epsilon eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(25 / 243) : k), (-(4 / 243) : k), (5 / 27 : k),
      (10 / 81 : k), (5 / 9 : k), (5 / 27 : k),
      (-(10 / 9) : k), (-(10 / 27) : k), (-(4 / 243 * alpha) : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k)]
      [
      [1, 3, 1, 0, 0], [0, 5, 0, 0, 0], [1, 1, 0, 2, 0], [0, 3, 0, 0, 1],
      [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 3, 0],
      [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
      [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0]] := by
  simp only [degreeZeroN2CubicBCDEWallThetaRest610_chunk0, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN2CubicBCDEWallThetaRest610_chunk1` (8 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN2CubicBCDEWallThetaRest610_chunk1_eq_polyOf
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2CubicBCDEWallThetaRest610_chunk1 alpha epsilon eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (2 / 9 * epsilon : k), (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k),
      (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k), (1 / 6 * theta : k),
      (-(1 / 12 * theta) : k), (1 * theta : k)]
      [
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] := by
  simp only [degreeZeroN2CubicBCDEWallThetaRest610_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallSplits610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_CD_zetaWall
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 0 epsilon zeta eta theta A B C D E =
      n1CubicSigmaFaceCD610 A B C D E +
        n1CubicZetaFace610 zeta A +
          degreeZeroN1CubicCDWallZetaRest610 alpha epsilon zeta eta theta
            A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceCD610, n1CubicZetaFace610,
    degreeZeroN1CubicCDWallZetaRest610, zero_mul, mul_zero, zero_smul]
  all_goals module

end CubicLoadWallSplits610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallSplits610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_CD_thetaWall
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 0 epsilon 0 eta theta A B C D E =
      n1CubicSigmaFaceCD610 A B C D E +
        n1CubicThetaFace610 theta A +
          degreeZeroN1CubicCDWallThetaRest610 alpha epsilon eta theta
            A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceCD610, n1CubicThetaFace610,
    degreeZeroN1CubicCDWallThetaRest610, zero_mul, mul_zero, zero_smul]
  all_goals module

end CubicLoadWallSplits610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallSplits610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_BCDE_zetaWall
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 0 epsilon zeta eta theta A B C D E =
      n1CubicSigmaFaceBCDE610 A B C D E +
        n1CubicZetaFace610 zeta A +
          degreeZeroN1CubicBCDEWallZetaRest610 alpha epsilon zeta eta theta
            A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceBCDE610, n1CubicZetaFace610,
    degreeZeroN1CubicBCDEWallZetaRest610, zero_mul, mul_zero, zero_smul]
  all_goals module

end CubicLoadWallSplits610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallSplits610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_BCDE_thetaWall
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 0 epsilon 0 eta theta A B C D E =
      n1CubicSigmaFaceBCDE610 A B C D E +
        n1CubicThetaFace610 theta A +
          degreeZeroN1CubicBCDEWallThetaRest610 alpha epsilon eta theta
            A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceBCDE610, n1CubicThetaFace610,
    degreeZeroN1CubicBCDEWallThetaRest610, zero_mul, mul_zero, zero_smul]
  all_goals module

end CubicLoadWallSplits610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem degreeZeroKappaCubic610_eq_chamber
    (alpha epsilon eta : k) (A C D E : k[X]) :
    degreeZeroKappaCubic610 0 alpha 0 0 epsilon 0 eta 0 A 0 C D E =
      kappaChamberCD610 alpha epsilon C D E := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  simp only [degreeZeroKappaCubic610, kappaChamberCD610, hpow2, hpow3,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    neg_zero]
  all_goals module

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem degreeZeroOmicronCubic610_eq_chamber
    (alpha epsilon eta : k) (A C D E : k[X]) :
    degreeZeroOmicronCubic610 0 alpha 0 0 epsilon 0 eta 0 A 0 C D E =
      omicronChamberCD610 alpha epsilon eta A C D E := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  simp only [degreeZeroOmicronCubic610, omicronChamberCD610, hpow2, hpow3,
    hpow4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    sub_zero, neg_zero]
  all_goals module

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem omicronCubicSigmaFaceCD610_coeff_top
    (A B C D E : k[X]) (hC : C ≠ 0) (hD : D ≠ 0) :
    (omicronCubicSigmaFaceCD610 A B C D E).coeff
        (C.natDegree + 2 * D.natDegree) =
      (-(5 / 27 : k)) * C.leadingCoeff * D.leadingCoeff ^ 2 := by
  simp only [omicronCubicSigmaFaceCD610, coeff_smul, smul_eq_mul]
  have hdeg : (C * D ^ 2).natDegree = C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hC (pow_ne_zero 2 hD), natDegree_pow]
  rw [← hdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  ring

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem kappaChamberCD610_of_E_eq_zero (alpha epsilon : k) (C D : k[X]) :
    kappaChamberCD610 alpha epsilon C D 0 =
      (4 / 9 * alpha : k) • (C * D) + (2 / 3 * epsilon : k) • D := by
  simp only [kappaChamberCD610, mul_zero, smul_zero, add_zero, zero_add]

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem kappaChamberCD610_of_alpha_eq_zero (epsilon : k) (C D E : k[X]) :
    kappaChamberCD610 0 epsilon C D E =
      (10 / 9 : k) • (D * E) + (2 / 3 * epsilon : k) • D := by
  unfold kappaChamberCD610
  have hCD : ((4 / 9 * (0 : k) : k)) • (C * D) = 0 := by
    have hz : (4 / 9 * (0 : k) : k) = 0 := by ring
    rw [hz, zero_smul]
  rw [hCD, add_zero]

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem omicronChamberCD610_of_alpha_eq_zero
    (epsilon eta : k) (A C D E : k[X]) :
    omicronChamberCD610 0 epsilon eta A C D E =
      (-(5 / 27 : k)) • (C ^ 2 * E) +
        (-(5 / 27 : k)) • (C * D ^ 2) +
        (-(1 / 9 * epsilon : k)) • C ^ 2 +
        (1 / 3 * eta : k) • E := by
  unfold omicronChamberCD610
  have hAD2 : (-(2 / 27 * (0 : k) : k)) • (A * D ^ 2) = 0 := by
    have hz : (2 / 27 * (0 : k) : k) = 0 := by ring
    rw [hz, neg_zero, zero_smul]
  have hC3 : (-(4 / 81 * (0 : k) : k)) • C ^ 3 = 0 := by
    have hz : (4 / 81 * (0 : k) : k) = 0 := by ring
    rw [hz, neg_zero, zero_smul]
  have hE2 : ((2 / 9 * (0 : k) : k)) • E ^ 2 = 0 := by
    have hz : (2 / 9 * (0 : k) : k) = 0 := by ring
    rw [hz, zero_smul]
  rw [hAD2, hC3, hE2]
  abel

end CubicLoadCDChamber610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallBetaRest610_chunk0_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 7 * C.natDegree = 11 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 5 * A.natDegree := by omega
  rw [speedRefl_degreeZeroN1CubicCDWallBetaRest610_chunk0_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
      (simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
                  Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
                  Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
                  List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
                  Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                  mul_one, one_mul, and_true, true_and, natDegree_zero];
       repeat' apply And.intro) <;>
        first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallBetaRest610_chunk1_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 5 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 7 * C.natDegree = 11 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 5 * A.natDegree := by omega
  rw [speedRefl_degreeZeroN1CubicCDWallBetaRest610_chunk1_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
      (simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
                  Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
                  Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
                  List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
                  Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                  mul_one, one_mul, and_true, true_and, natDegree_zero];
       repeat' apply And.intro) <;>
        first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallDeltaRest610_chunk0_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallDeltaRest610_chunk0 alpha delta epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 7 * C.natDegree = 9 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 4 * A.natDegree := by omega
  rw [speedRefl_degreeZeroN1CubicCDWallDeltaRest610_chunk0_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
      (simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
                  Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
                  Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
                  List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
                  Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                  mul_one, one_mul, and_true, true_and, natDegree_zero];
       repeat' apply And.intro) <;>
        first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallDeltaRest610_chunk1_natDegree_lt
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallDeltaRest610_chunk1 alpha delta epsilon zeta eta theta A B C D E).natDegree < 4 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 7 * C.natDegree = 9 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 4 * A.natDegree := by omega
  rw [speedRefl_degreeZeroN1CubicCDWallDeltaRest610_chunk1_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
      (simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
                  Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
                  Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
                  List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
                  Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                  mul_one, one_mul, and_true, true_and, natDegree_zero];
       repeat' apply And.intro) <;>
        first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallZetaRest610_natDegree_lt
    (alpha epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 12 * A.natDegree = 6 * A.natDegree + 6 * C.natDegree) :
    (degreeZeroN1CubicCDWallZetaRest610 alpha epsilon zeta eta theta A B C D E).natDegree < 3 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : C.natDegree = A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 3 * A.natDegree := by omega
  rw [speedRefl_degreeZeroN1CubicCDWallZetaRest610_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
      (simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
                  Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
                  Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
                  List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
                  Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                  mul_one, one_mul, and_true, true_and, natDegree_zero];
       repeat' apply And.intro) <;>
        first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial

end CubicLoadWallRests610

end Max11DegreeRoutes
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
set_option maxRecDepth 100000000

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicCDWallThetaRest610_natDegree_lt
    (alpha epsilon eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 54 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicCDWallThetaRest610 alpha epsilon eta theta A B C D E).natDegree < 2 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hwall' : 7 * C.natDegree = 5 * A.natDegree := by omega
  have hface : 2 * C.natDegree + D.natDegree = 2 * A.natDegree := by omega
  rw [speedRefl_degreeZeroN1CubicCDWallThetaRest610_eq_polyOf]
  first
    | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
    | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
      (simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
                  Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
                  Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
                  List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
                  Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                  mul_one, one_mul, and_true, true_and, natDegree_zero];
       repeat' apply And.intro) <;>
        first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial

end CubicLoadWallRests610

end Max11DegreeRoutes
