import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 37 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


def n2QuarticDeltaFace810 (delta : k) (A : k[X]) : k[X] :=
  (35 / 32768 * delta : k) • A ^ 4

def n2QuarticZetaFace810 (zeta : k) (A : k[X]) : k[X] :=
  (5 / 1024 * zeta : k) • A ^ 3

end QuarticN2_810
end Max11DegreeRoutes
end
