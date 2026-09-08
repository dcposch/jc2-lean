import Grok610ScaleZeroCubicLoadWallsPart39Scratch

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
