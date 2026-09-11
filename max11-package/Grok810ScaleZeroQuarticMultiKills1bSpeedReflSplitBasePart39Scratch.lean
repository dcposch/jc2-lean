import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 39 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def nuQuarticInnerABDE810 (a b d e : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + (-160 : k) * a * d * e + (-480 : k) * b * d ^ 2


def xiQuarticInnerABDE810 (a b d e : k) : k :=
  (-15 : k) * a * b ^ 4 + 60 * a * b ^ 2 * e + 110 * b ^ 3 * d + (-400 : k) * b * d * e


def omicronQuarticInnerABDE810 (a b d e : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + (-160 : k) * a ^ 2 * d * e + 2240 * a * b * d ^ 2 + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + (-5120 : k) * b * e ^ 2 + (-2560 : k) * d ^ 3


end QuarticKills810
end Max11DegreeRoutes
end
