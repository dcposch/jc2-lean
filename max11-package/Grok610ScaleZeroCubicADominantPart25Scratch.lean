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
def degreeZeroKappaCubicNoSigmaB610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (B ^ 2 * D)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)
  + (7 / 6912 * l : k) • A ^ 5
  + (5 / 288 * l : k) • (A ^ 3 * C)
  - (1 / 192 * l : k) • (A ^ 2 * B ^ 2)
  + (1 / 16 * l : k) • (A ^ 2 * E)
  - (1 / 8 * l : k) • (A * B * D)
  + (1 / 16 * l : k) • (A * C ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * C)
  + (3 / 4 * l : k) • (C * E)
  + (3 / 8 * l : k) • D ^ 2
  - (4 / 81 * alpha : k) • B ^ 3
  + (4 / 9 * alpha : k) • (B * E)
  + (4 / 9 * alpha : k) • (C * D)
  + (35 / 10368 * beta : k) • A ^ 4
  + (7 / 144 * beta : k) • (A ^ 2 * C)
  - (7 / 432 * beta : k) • (A * B ^ 2)
  + (7 / 36 * beta : k) • (A * E)
  + (7 / 36 * beta : k) • (B * D)
  + (7 / 72 * beta : k) • C ^ 2
  + (5 / 432 * delta : k) • A ^ 3
  + (5 / 36 * delta : k) • (A * C)
  - (5 / 72 * delta : k) • B ^ 2
  + (5 / 6 * delta : k) • E
  + (2 / 3 * epsilon : k) • D
  + (1 / 24 * zeta : k) • A ^ 2
  + (1 / 2 * zeta : k) • C
  + (1 / 3 * eta : k) • B
  + (1 / 6 * theta : k) • A

end CubicSigmaKills610

end Max11DegreeRoutes
