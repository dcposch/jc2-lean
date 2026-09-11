import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 49 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def omicronQuarticInnerABDF810 (a b d f : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + 1600 * a * b ^ 2 * f + 2240 * a * b * d ^ 2 + (-336 : k) * b ^ 5 + (-10240 : k) * b * d * f + (-2560 : k) * d ^ 3


def piQuarticInnerABDF810 (a b d f : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + (-1280 : k) * a * f ^ 2 + 800 * b ^ 3 * f + 1440 * b ^ 2 * d ^ 2


def primitiveQuarticInnerABDF810 (a b d f : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + (-160 : k) * a ^ 2 * b ^ 2 * f + (-800 : k) * a ^ 2 * b * d ^ 2 + 520 * a * b ^ 5 + 10240 * a * b * d * f + 2560 * a * d ^ 3 + (-4000 : k) * b ^ 4 * d + (-20480 : k) * b * f ^ 2 + (-20480 : k) * d ^ 2 * f


end QuarticKills810
end Max11DegreeRoutes
end
