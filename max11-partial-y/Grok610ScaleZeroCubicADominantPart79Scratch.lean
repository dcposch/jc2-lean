import Grok610ScaleZeroCubicConesScratch
import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronCubicNoSigmaBCD610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 486 : k)) • (A * B ^ 4)
  + (5 / 81 : k) • (A * B ^ 2 * E)
  + (25 / 486 : k) • (B ^ 3 * D)
  + (5 / 54 : k) • (B ^ 2 * C ^ 2)
  - (5 / 27 : k) • (B * D * E)
  - (5 / 27 : k) • (C ^ 2 * E)
  - (5 / 27 : k) • (C * D ^ 2)
  - (5 / 6912 * l : k) • (A ^ 4 * D)
  + (1 / 864 * l : k) • (A ^ 3 * B * C)
  - (1 / 288 * l : k) • (A ^ 2 * B ^ 3)
  - (1 / 96 * l : k) • (A ^ 2 * C * D)
  + (7 / 96 * l : k) • (A * B ^ 2 * D)
  + (1 / 24 * l : k) • (A * B * C ^ 2)
  + (1 / 16 * l : k) • (B ^ 3 * C)
  - (1 / 8 * l : k) • (A * D * E)
  - (1 / 4 * l : k) • (B * C * E)
  - (1 / 8 * l : k) • (B * D ^ 2)
  - (3 / 16 * l : k) • (C ^ 2 * D)
  + (4 / 81 * alpha : k) • (A * B ^ 2 * C)
  + (1 / 81 * alpha : k) • B ^ 4
  - (2 / 27 * alpha : k) • (A * D ^ 2)
  - (2 / 27 * alpha : k) • (B ^ 2 * E)
  - (2 / 9 * alpha : k) • (B * C * D)
  - (4 / 81 * alpha : k) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * D)
  + (7 / 1296 * beta : k) • (A ^ 2 * B * C)
  + (7 / 648 * beta : k) • (A * B ^ 3)
  - (7 / 216 * beta : k) • (A * C * D)
  - (7 / 144 * beta : k) • (B ^ 2 * D)
  - (7 / 108 * beta : k) • (B * C ^ 2)
  + (7 / 36 * beta : k) • (D * E)
  - (5 / 432 * delta : k) • (A ^ 2 * D)
  + (5 / 108 * delta : k) • (A * B * C)
  + (5 / 324 * delta : k) • B ^ 3
  - (5 / 36 * delta : k) • (C * D)
  + (1 / 27 * epsilon : k) • (A * B ^ 2)
  - (1 / 9 * epsilon : k) • (B * D)
  - (1 / 9 * epsilon : k) • C ^ 2
  - (1 / 12 * zeta : k) • (A * D)
  - (1 / 6 * zeta : k) • (B * C)
  - (1 / 18 * eta : k) • B ^ 2
  + (1 / 3 * eta : k) • E
  + (1 / 6 * theta : k) • D

end CubicSigmaKills610

end Max11DegreeRoutes
