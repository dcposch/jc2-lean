import Grok610ScaleZeroCubicLoadWallsPart87Scratch

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
