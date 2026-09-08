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

def degreeZeroN1CubicCDWallDeltaRest610_chunk0 (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (5 / 81 : k) • (A * B ^ 2 * D)
  + (20 / 243 : k) • (B ^ 3 * C)
  + (-(10 / 27 : k)) • (B * C * E)
  + (-(5 / 27 : k)) • (B * D ^ 2)
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  + (-(4 / 27 * alpha : k)) • (B ^ 2 * D)
  + (-(4 / 27 * alpha : k)) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  + (-(5 / 36 * delta : k)) • (B * D)
  + (-(5 / 72 * delta : k)) • C ^ 2
  + (-(2 / 9 * epsilon : k)) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)

end CubicLoadWallRests610

end Max11DegreeRoutes
