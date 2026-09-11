import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 39 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

section QuarticN2_810


set_option maxHeartbeats 64000000 in
def degreeZeroN2QuarticNoL2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(63 / 1024 * l : k)) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2
  + (63 / 262144 * beta : k) • A ^ 5
  + (35 / 8192 * beta : k) • (A ^ 3 * C)
  + (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (21 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 512 * beta : k) • (A * B * D)
  - (7 / 1024 * beta : k) • (A * C ^ 2)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)
  + (7 / 64 * beta : k) • (A * G)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 16 * gamma : k) • (B * E)


set_option maxHeartbeats 64000000 in
def degreeZeroN2QuarticNoL3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * gamma : k)) • (C * D)
  + (35 / 32768 * delta : k) • A ^ 4
  + (15 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 1024 * delta : k) • (A * B ^ 2)
  + (5 / 64 * delta : k) • (A * E)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F
  + (5 / 1024 * zeta : k) • A ^ 3
  + (3 / 64 * zeta : k) • (A * C)
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  + (1 / 4 * eta : k) • D
  + (3 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C


end QuarticN2_810
end Max11DegreeRoutes
end
