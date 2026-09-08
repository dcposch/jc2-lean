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

def degreeZeroN2CubicBCDEWallThetaRest610_chunk1 (alpha epsilon eta theta : k) (A B C D E : k[X]) : k[X] :=
  (2 / 9 * epsilon : k) • (A * B * C)
  + (2 / 27 * epsilon : k) • B ^ 3
  + (-(2 / 3 * epsilon : k)) • (C * D)
  + (-(1 / 3 * eta : k)) • (A * D)
  + (-(1 / 3 * eta : k)) • (B * C)
  + (1 / 6 * theta : k) • (A * C)
  + (-(1 / 12 * theta : k)) • B ^ 2
  + (1 * theta : k) • E

end CubicLoadWallRests610

end Max11DegreeRoutes
