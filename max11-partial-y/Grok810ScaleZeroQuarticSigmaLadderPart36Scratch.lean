import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 36 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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


def n2QuarticLFace810 (l : k) (A : k[X]) : k[X] :=
  (231 / 4194304 * l : k) • A ^ 6

def n2QuarticBetaFace810 (beta : k) (A : k[X]) : k[X] :=
  (63 / 262144 * beta : k) • A ^ 5

end QuarticN2_810
end Max11DegreeRoutes
end
