import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart15iScratch

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
/-- Reflected form of `degreeZeroPrimitiveCubicNoABCDE610` (63 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPrimitiveCubicNoABCDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroPrimitiveCubicNoABCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 27648 * l : k), (25 / 6912 * l : k), (-(17 / 13824 * l) : k),
      (1 / 128 * l : k), (1 / 288 * l : k), (13 / 576 * l : k),
      (-(5 / 192 * l) : k), (-(1 / 32 * l) : k), (1 / 16 * l : k),
      (1 / 8 * l : k), (3 / 8 * l : k), (1 / 16 * l : k),
      (3 / 16 * l : k), (9 / 32 * l : k), (-(3 / 4 * l) : k),
      (-(3 / 8 * l) : k), (-(3 / 4 * l) : k), (-(1 / 81 * alpha) : k),
      (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k), (4 / 27 * alpha : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
      (35 / 62208 * beta : k), (49 / 5184 * beta : k), (-(7 / 1728 * beta) : k),
      (7 / 432 * beta : k), (-(7 / 216 * beta) : k), (7 / 144 * beta : k),
      (35 / 432 * beta : k), (35 / 1728 * beta : k), (7 / 36 * beta : k),
      (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k), (-(7 / 18 * beta) : k),
      (-(7 / 108 * beta) : k), (7 / 12 * beta : k), (1 / 576 * delta : k),
      (5 / 216 * delta : k), (-(5 / 216 * delta) : k), (5 / 36 * delta : k),
      (5 / 36 * delta : k), (-(5 / 12 * delta) : k), (-(1 / 18 * epsilon) : k),
      (2 / 9 * epsilon : k), (2 / 27 * epsilon : k), (-(2 / 3 * epsilon) : k),
      (1 / 192 * zeta : k), (1 / 24 * zeta : k), (1 / 12 * zeta : k),
      (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k), (-(1 / 36 * eta) : k),
      (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k), (1 / 72 * theta : k),
      (1 / 6 * theta : k), (-(1 / 12 * theta) : k), (1 * theta : k)]
      [
      [7, 0, 0, 0, 0], [5, 0, 1, 0, 0], [4, 2, 0, 0, 0], [4, 0, 0, 0, 1],
      [3, 1, 0, 1, 0], [3, 0, 2, 0, 0], [2, 2, 1, 0, 0], [1, 4, 0, 0, 0],
      [2, 0, 1, 0, 1], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 0, 3, 0, 0],
      [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1],
      [0, 0, 1, 2, 0], [2, 3, 0, 0, 0], [2, 1, 0, 0, 1], [2, 0, 1, 1, 0],
      [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1],
      [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0],
      [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
      [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1],
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [2, 0, 0, 1, 0],
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
      [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0],
      [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] :=
  rfl

end CubicKills610

end Max11DegreeRoutes

end
