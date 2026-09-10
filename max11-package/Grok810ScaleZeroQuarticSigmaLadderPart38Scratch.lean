import Grok810ScaleZeroQuarticSigmaLadderPart37Scratch

/-! Part 38 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


def n2QuarticThetaFace810 (theta : k) (A : k[X]) : k[X] :=
  (3 / 128 * theta : k) • A ^ 2


set_option maxHeartbeats 64000000 in
def degreeZeroN2QuarticNoL1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)
  + (315 / 262144 * l : k) • (A ^ 4 * C)
  - (9 / 131072 * l : k) • (A ^ 3 * B ^ 2)
  + (45 / 8192 * l : k) • (A ^ 3 * E)
  - (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 8192 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (27 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 512 * l : k) • (A * B * F)
  + (9 / 512 * l : k) • (A * C * E)
  - (9 / 1024 * l : k) • (A * D ^ 2)


end QuarticN2_810
end Max11DegreeRoutes
end
