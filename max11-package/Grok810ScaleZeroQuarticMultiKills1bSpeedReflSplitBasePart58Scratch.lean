import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart57Scratch

/-! Part 58 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def xiQuarticInnerABDG810 (a b d g : k) : k :=
  (-15 : k) * a * b ^ 4 + 110 * b ^ 3 * d + (-160 : k) * b ^ 2 * g


def omicronQuarticInnerABDG810 (a b d g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + (-160 : k) * a ^ 2 * b * g + 2240 * a * b * d ^ 2 + (-2560 : k) * a * d * g + (-336 : k) * b ^ 5 + (-2560 : k) * d ^ 3


def piQuarticInnerABDG810 (a b d g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + 320 * a * b ^ 2 * g + 1440 * b ^ 2 * d ^ 2 + (-2560 : k) * b * d * g + 5120 * g ^ 2


end QuarticKills810
end Max11DegreeRoutes
end
