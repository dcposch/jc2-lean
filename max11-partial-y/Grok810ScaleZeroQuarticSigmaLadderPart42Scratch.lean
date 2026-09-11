import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 42 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


def kappaQuarticDeltaFace810 (delta : k) (A : k[X]) : k[X] :=
  (5 / 1024 * delta : k) • A ^ 3

def kappaQuarticZetaFace810 (zeta : k) (A : k[X]) : k[X] :=
  (3 / 128 * zeta : k) • A ^ 2


end QuarticKappaLadder810
end Max11DegreeRoutes
end
