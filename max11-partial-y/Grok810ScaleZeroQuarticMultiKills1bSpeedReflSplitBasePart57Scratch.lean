import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart56Scratch

/-! Part 57 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def kappaQuarticInnerABDG810 (a b d g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + 160 * b * g


def muQuarticInnerABDG810 (a b d g : k) : k :=
  (-80 : k) * a * d ^ 2 + 35 * b ^ 4


def nuQuarticInnerABDG810 (a b d g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + (-160 : k) * a * b * g + (-480 : k) * b * d ^ 2 + 1280 * d * g


end QuarticKills810
end Max11DegreeRoutes
end
