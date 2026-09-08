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

def degreeZeroN2CubicBCDEWallBetaRest610_chunk1 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (35 / 2592 * beta : k) • (A ^ 4 * C)
  + (-(7 / 1296 * beta : k)) • (A ^ 3 * B ^ 2)
  + (7 / 216 * beta : k) • (A ^ 3 * E)
  + (-(7 / 432 * beta : k)) • (A ^ 2 * B * D)
  + (49 / 864 * beta : k) • (A ^ 2 * C ^ 2)
  + (35 / 432 * beta : k) • (A * B ^ 2 * C)
  + (35 / 1728 * beta : k) • B ^ 4
  + (7 / 36 * beta : k) • (A * C * E)
  + (-(7 / 36 * beta : k)) • (A * D ^ 2)
  + (-(7 / 72 * beta : k)) • (B ^ 2 * E)
  + (-(7 / 18 * beta : k)) • (B * C * D)
  + (-(7 / 108 * beta : k)) • C ^ 3
  + (7 / 12 * beta : k) • E ^ 2
  + (7 / 2592 * delta : k) • A ^ 5
  + (5 / 144 * delta : k) • (A ^ 3 * C)
  + (-(25 / 864 * delta : k)) • (A ^ 2 * B ^ 2)

end CubicLoadWallRests610

end Max11DegreeRoutes
