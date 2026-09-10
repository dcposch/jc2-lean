import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart28Scratch

/-! Part 29 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def kappaQuarticInnerABCG810 (a b c g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b * c ^ 2 + 160 * b * g


def muQuarticInnerABCG810 (a b c g : k) : k :=
  60 * a * b ^ 2 * c + 35 * b ^ 4 + (-80 : k) * c ^ 3 + 640 * c * g


def nuQuarticInnerABCG810 (a b c g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 60 * a * b * c ^ 2 + (-160 : k) * a * b * g + 280 * b ^ 3 * c


end QuarticKills810
end Max11DegreeRoutes
end
