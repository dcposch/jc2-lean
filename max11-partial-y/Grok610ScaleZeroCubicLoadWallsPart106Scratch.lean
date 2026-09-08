import Grok610ScaleZeroCubicLoadWallsPart101Scratch

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
