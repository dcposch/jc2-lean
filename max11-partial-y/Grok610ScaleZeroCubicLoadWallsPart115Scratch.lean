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

def degreeZeroN2CubicBCDEWallDeltaRest610_chunk0 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(25 / 243 : k)) • (A * B ^ 3 * C)
  + (-(4 / 243 : k)) • B ^ 5
  + (5 / 27 : k) • (A * B * D ^ 2)
  + (10 / 81 : k) • (B ^ 3 * E)
  + (5 / 9 : k) • (B ^ 2 * C * D)
  + (5 / 27 : k) • (B * C ^ 3)
  + (-(10 / 9 : k)) • (C * D * E)
  + (-(10 / 27 : k)) • D ^ 3
  + (-(4 / 243 * alpha : k)) • (A ^ 2 * B ^ 3)
  + (4 / 27 * alpha : k) • (A * B ^ 2 * D)
  + (4 / 27 * alpha : k) • (A * B * C ^ 2)
  + (4 / 27 * alpha : k) • (B ^ 3 * C)
  + (-(4 / 9 * alpha : k)) • (A * D * E)
  + (-(4 / 9 * alpha : k)) • (B * C * E)
  + (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)

end CubicLoadWallRests610

end Max11DegreeRoutes
