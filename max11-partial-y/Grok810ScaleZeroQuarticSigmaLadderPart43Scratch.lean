import Grok810ScaleZeroQuarticSigmaLadderPart42Scratch

/-! Part 43 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticKappaLadder810


set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoL1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)


set_option maxHeartbeats 64000000 in
def degreeZeroKappaQuarticNoL2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 512 * l : k)) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)


end QuarticKappaLadder810
end Max11DegreeRoutes
end
