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

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

def degreeZeroN1CubicBCDEWallBetaRest610_chunk0 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  + (-(7 / 5184 * beta : k)) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  + (-(7 / 216 * beta : k)) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  + (-(35 / 432 * beta : k)) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)

end CubicLoadWallRests610

end Max11DegreeRoutes
