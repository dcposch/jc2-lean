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

def degreeZeroN2CubicBCDEWallBetaRest610_chunk2 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 72 * delta : k) • (A ^ 2 * E)
  + (5 / 36 * delta : k) • (A * C ^ 2)
  + (5 / 36 * delta : k) • (B ^ 2 * C)
  + (-(5 / 12 * delta : k)) • D ^ 2
  + (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (5 / 576 * zeta : k) • A ^ 4
  + (1 / 12 * zeta : k) • (A ^ 2 * C)
  + (1 / 12 * zeta : k) • (A * B ^ 2)
  + (-(1 / 2 * zeta : k)) • (B * D)
  + (-(1 / 4 * zeta : k)) • C ^ 2
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 36 * theta : k) • A ^ 3
  + (1 / 6 * theta : k) • (A * C)

end CubicLoadWallRests610

end Max11DegreeRoutes
