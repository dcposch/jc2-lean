import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart29Scratch

/-! Part 30 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def xiQuarticInnerABCG810 (a b c g : k) : k :=
  (-15 : k) * a * b ^ 4 + 180 * b ^ 2 * c ^ 2 + (-160 : k) * b ^ 2 * g


def omicronQuarticInnerABCG810 (a b c g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * b * g + (-1120 : k) * a * b ^ 3 * c + (-336 : k) * b ^ 5 + 2880 * b * c ^ 3 + (-7680 : k) * b * c * g


def piQuarticInnerABCG810 (a b c g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-360 : k) * a * b ^ 2 * c ^ 2 + 320 * a * b ^ 2 * g + (-560 : k) * b ^ 4 * c + 240 * c ^ 4 + (-1280 : k) * c ^ 2 * g + 5120 * g ^ 2


end QuarticKills810
end Max11DegreeRoutes
end
