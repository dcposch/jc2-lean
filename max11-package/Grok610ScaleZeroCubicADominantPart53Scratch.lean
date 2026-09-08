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

set_option maxHeartbeats 16000000 in
def degreeZeroLambdaCubicNoSigmaBC610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • B ^ 4
  - (5 / 27 : k) • (A * D ^ 2)
  - (5 / 27 : k) • (B ^ 2 * E)
  - (10 / 27 : k) • (B * C * D)
  + (5 / 9 : k) • E ^ 2
  - (5 / 6912 * l : k) • (A ^ 4 * B)
  - (1 / 288 * l : k) • (A ^ 3 * D)
  - (1 / 96 * l : k) • (A ^ 2 * B * C)
  + (1 / 32 * l : k) • (A * B ^ 3)
  - (1 / 8 * l : k) • (A * B * E)
  - (1 / 8 * l : k) • (A * C * D)
  - (3 / 16 * l : k) • (B ^ 2 * D)
  - (3 / 16 * l : k) • (B * C ^ 2)
  + (3 / 4 * l : k) • (D * E)
  - (4 / 27 * alpha : k) • (A * B * D)
  - (4 / 27 * alpha : k) • (B ^ 2 * C)
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  - (7 / 2592 * beta : k) • (A ^ 3 * B)
  - (7 / 432 * beta : k) • (A ^ 2 * D)
  - (7 / 216 * beta : k) • (A * B * C)
  - (35 / 1296 * beta : k) • B ^ 3
  + (7 / 36 * beta : k) • (B * E)
  + (7 / 36 * beta : k) • (C * D)
  - (5 / 432 * delta : k) • (A ^ 2 * B)
  - (5 / 36 * delta : k) • (A * D)
  - (5 / 36 * delta : k) • (B * C)
  - (1 / 9 * epsilon : k) • B ^ 2
  + (2 / 3 * epsilon : k) • E
  - (1 / 12 * zeta : k) • (A * B)
  + (1 / 2 * zeta : k) • D
  + (1 / 3 * eta : k) • C
  + (1 / 6 * theta : k) • B

end CubicSigmaKills610

end Max11DegreeRoutes
