import Grok810ScaleZeroQuarticMultiKillsScratch
import Max11SpeedReflectDegLibScratch

/-! Part 1 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def kappaQuarticInnerABCD810 (a b c d : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + (-60 : k) * b * c ^ 2


def muQuarticInnerABCD810 (a b c d : k) : k :=
  60 * a * b ^ 2 * c + (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + (-480 : k) * b * c * d + (-80 : k) * c ^ 3


def nuQuarticInnerABCD810 (a b c d : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + 60 * a * b * c ^ 2 + 280 * b ^ 3 * c + (-480 : k) * b * d ^ 2 + (-480 : k) * c ^ 2 * d


end QuarticKills810
end Max11DegreeRoutes
end
