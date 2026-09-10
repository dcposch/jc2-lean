import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart47Scratch

/-! Part 48 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def muQuarticInnerABDF810 (a b d f : k) : k :=
  (-160 : k) * a * b * f + (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + 640 * d * f


def nuQuarticInnerABDF810 (a b d f : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + (-480 : k) * b ^ 2 * f + (-480 : k) * b * d ^ 2


def xiQuarticInnerABDF810 (a b d f : k) : k :=
  (-15 : k) * a * b ^ 4 + (-160 : k) * a * d * f + 110 * b ^ 3 * d + 320 * f ^ 2


end QuarticKills810
end Max11DegreeRoutes
end
