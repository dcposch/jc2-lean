import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart01Scratch

/-! Part 2 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def xiQuarticInnerABCD810 (a b c d : k) : k :=
  (-15 : k) * a * b ^ 4 + 120 * a * b * c * d + 110 * b ^ 3 * d + 180 * b ^ 2 * c ^ 2 + (-240 : k) * c * d ^ 2


def omicronQuarticInnerABCD810 (a b c d : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + 60 * a ^ 2 * b * c ^ 2 + (-1120 : k) * a * b ^ 3 * c + 2240 * a * b * d ^ 2 + 960 * a * c ^ 2 * d + (-336 : k) * b ^ 5 + 8640 * b ^ 2 * c * d + 2880 * b * c ^ 3 + (-2560 : k) * d ^ 3


def piQuarticInnerABCD810 (a b c d : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + (-360 : k) * a * b ^ 2 * c ^ 2 + 640 * a * c * d ^ 2 + (-560 : k) * b ^ 4 * c + 1440 * b ^ 2 * d ^ 2 + 2880 * b * c ^ 2 * d + 240 * c ^ 4


end QuarticKills810
end Max11DegreeRoutes
end
