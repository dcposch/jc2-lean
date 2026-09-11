import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 73 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]


def kappaQuarticInnerABFG810 (a b f g : k) : k :=
  5 * a * b ^ 3 + 160 * b * g


def muQuarticInnerABFG810 (a b f g : k) : k :=
  (-160 : k) * a * b * f + 35 * b ^ 4


def nuQuarticInnerABFG810 (a b f g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + (-160 : k) * a * b * g + (-480 : k) * b ^ 2 * f


end QuarticKills810
end Max11DegreeRoutes
end
