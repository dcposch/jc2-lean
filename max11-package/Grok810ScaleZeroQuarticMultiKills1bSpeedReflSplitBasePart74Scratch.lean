import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 74 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def xiQuarticInnerABFG810 (a b f g : k) : k :=
  (-15 : k) * a * b ^ 4 + (-160 : k) * b ^ 2 * g + 320 * f ^ 2


def omicronQuarticInnerABFG810 (a b f g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-160 : k) * a ^ 2 * b * g + 1600 * a * b ^ 2 * f + (-336 : k) * b ^ 5 + 20480 * f * g


def piQuarticInnerABFG810 (a b f g : k) : k :=
  15 * a ^ 2 * b ^ 4 + 320 * a * b ^ 2 * g + (-1280 : k) * a * f ^ 2 + 800 * b ^ 3 * f + 5120 * g ^ 2


end QuarticKills810
end Max11DegreeRoutes
end
