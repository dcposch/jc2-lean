import Grok810ScaleZeroQuarticMultiKillsPart27Scratch

/-! Part 28 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


def kappaQuarticInnerBCD810 (b c d : k) : k :=
  (-15 : k) * b ^ 2 * d + (-15 : k) * b * c ^ 2


def muQuarticInnerBCD810 (b c d : k) : k :=
  35 * b ^ 4 + (-480 : k) * b * c * d + (-80 : k) * c ^ 3


def nuQuarticInnerBCD810 (b c d : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b * d ^ 2 + (-60 : k) * c ^ 2 * d


def xiQuarticInnerBCD810 (b c d : k) : k :=
  55 * b ^ 3 * d + 90 * b ^ 2 * c ^ 2 + (-120 : k) * c * d ^ 2


end QuarticKills810
end Max11DegreeRoutes
end
