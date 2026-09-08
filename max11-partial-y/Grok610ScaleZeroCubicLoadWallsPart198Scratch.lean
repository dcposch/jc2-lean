import Grok610ScaleZeroCubicLoadMultiScratch
import Max11SpeedReflectDegLibScratch

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

set_option maxHeartbeats 400000000 in
/-- Reflected form of `lambdaChamberRestCD610` (5 monomials, 4 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_lambdaChamberRestCD610_eq_polyOf_dupfix
    (alpha epsilon eta : k) (A C D E : k[X]) :
    lambdaChamberRestCD610 alpha epsilon eta A C D E =
      Max11ReflectDeg.polyOf [A, C, D, E]
      [
      (5 / 9 : k), (4 / 9 * alpha : k), (2 / 9 * alpha : k),
      (2 / 3 * epsilon : k), (1 / 3 * eta : k)]
      [
      [0, 0, 0, 2], [0, 1, 0, 1], [0, 0, 2, 0], [0, 0, 0, 1],
      [0, 1, 0, 0]] := by
  simp only [lambdaChamberRestCD610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  try module

end CubicLoadCDChamber610

end Max11DegreeRoutes
