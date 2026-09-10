import Grok810ScaleZeroQuarticMultiKillsPart34Scratch

/-! Part 35 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


def muQuarticInnerBCF810 (b c f : k) : k :=
  35 * b ^ 4 + (-80 : k) * c ^ 3


def nuQuarticInnerBCF810 (b c f : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b ^ 2 * f


def xiQuarticInnerBCF810 (b c f : k) : k :=
  45 * b ^ 2 * c ^ 2 + (-100 : k) * b * c * f + 80 * f ^ 2


def omicronQuarticInnerBCF810 (b c f : k) : k :=
  (-21 : k) * b ^ 5 + 180 * b * c ^ 3 + (-320 : k) * c ^ 2 * f


end QuarticKills810
end Max11DegreeRoutes
end
