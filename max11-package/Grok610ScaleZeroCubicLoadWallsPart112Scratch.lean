import Grok610ScaleZeroCubicLoadWallsPart104Scratch

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
