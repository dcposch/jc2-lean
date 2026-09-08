import Grok610ScaleZeroCubicConesScratch
import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
def degreeZeroN1CubicNoSigmaBCDE610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) : k[X] :=
  (20 / 243 : k) • (B ^ 3 * C)
  - (5 / 27 : k) • (B * D ^ 2)
  + (77 / 248832 * l : k) • A ^ 6
  + (35 / 6912 * l : k) • (A ^ 4 * C)
  - (1 / 1152 * l : k) • (A ^ 3 * B ^ 2)
  + (5 / 288 * l : k) • (A ^ 3 * E)
  - (1 / 96 * l : k) • (A ^ 2 * B * D)
  + (1 / 64 * l : k) • (A ^ 2 * C ^ 2)
  + (1 / 32 * l : k) • (A * B ^ 2 * C)
  + (3 / 128 * l : k) • B ^ 4
  + (1 / 8 * l : k) • (A * C * E)
  - (1 / 16 * l : k) • (A * D ^ 2)
  - (3 / 16 * l : k) • (B ^ 2 * E)
  - (3 / 8 * l : k) • (B * C * D)
  - (1 / 16 * l : k) • C ^ 3
  + (3 / 8 * l : k) • E ^ 2
  + (4 / 243 * alpha : k) • (A * B ^ 3)
  - (4 / 27 * alpha : k) • (B ^ 2 * D)
  - (4 / 27 * alpha : k) • (B * C ^ 2)
  + (4 / 9 * alpha : k) • (D * E)
  + (7 / 6912 * beta : k) • A ^ 5
  + (35 / 2592 * beta : k) • (A ^ 3 * C)
  - (7 / 5184 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 144 * beta : k) • (A ^ 2 * E)
  - (7 / 216 * beta : k) • (A * B * D)
  + (7 / 432 * beta : k) • (A * C ^ 2)
  - (35 / 432 * beta : k) • (B ^ 2 * C)
  + (7 / 36 * beta : k) • (C * E)
  + (7 / 72 * beta : k) • D ^ 2
  + (35 / 10368 * delta : k) • A ^ 4
  + (5 / 144 * delta : k) • (A ^ 2 * C)
  + (5 / 432 * delta : k) • (A * B ^ 2)
  + (5 / 36 * delta : k) • (A * E)
  - (5 / 36 * delta : k) • (B * D)
  - (5 / 72 * delta : k) • C ^ 2
  - (2 / 9 * epsilon : k) • (B * C)
  + (5 / 432 * zeta : k) • A ^ 3
  + (1 / 12 * zeta : k) • (A * C)
  - (1 / 8 * zeta : k) • B ^ 2
  + (1 / 2 * zeta : k) • E
  + (1 / 3 * eta : k) • D
  + (1 / 24 * theta : k) • A ^ 2
  + (1 / 6 * theta : k) • C

end CubicBalanced610

end Max11DegreeRoutes
