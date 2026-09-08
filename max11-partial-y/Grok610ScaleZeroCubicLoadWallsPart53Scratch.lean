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

def degreeZeroN2CubicCDWallDeltaRest610_chunk1 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (-(4 / 9 * alpha : k)) • (B * D ^ 2)
  + (-(4 / 9 * alpha : k)) • (C ^ 2 * D)
  + (5 / 144 * delta : k) • (A ^ 3 * C)
  + (-(25 / 864 * delta : k)) • (A ^ 2 * B ^ 2)
  + (5 / 72 * delta : k) • (A ^ 2 * E)
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

end CubicLoadWallRests610

end Max11DegreeRoutes
