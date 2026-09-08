import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart15aScratch

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

section CubicKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuCubicNoABCDE610` (40 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuCubicNoABCDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroMuCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (35 / 248832 * l : k), (5 / 2304 * l : k), (1 / 144 * l : k),
      (1 / 96 * l : k), (1 / 192 * l : k), (1 / 16 * l : k),
      (3 / 128 * l : k), (-(1 / 8 * l) : k), (-(3 / 16 * l) : k),
      (-(3 / 8 * l) : k), (-(1 / 16 * l) : k), (3 / 8 * l : k),
      (2 / 81 * alpha : k), (-(2 / 27 * alpha) : k), (-(2 / 27 * alpha) : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (7 / 15552 * beta : k), (7 / 1296 * beta : k), (7 / 5184 * beta : k),
      (7 / 432 * beta : k), (-(7 / 108 * beta) : k), (-(35 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 72 * beta : k), (5 / 3456 * delta : k),
      (5 / 432 * delta : k), (5 / 216 * delta : k), (-(5 / 36 * delta) : k),
      (-(5 / 72 * delta) : k), (-(1 / 9 * epsilon) : k), (-(2 / 9 * epsilon) : k),
      (1 / 216 * zeta : k), (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k),
      (-(1 / 18 * eta) : k), (1 / 3 * eta : k), (1 / 72 * theta : k),
      (1 / 6 * theta : k)]
      [
      [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
      [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0],
      [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
      [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]] :=
  rfl

end CubicKills610

end Max11DegreeRoutes

end
