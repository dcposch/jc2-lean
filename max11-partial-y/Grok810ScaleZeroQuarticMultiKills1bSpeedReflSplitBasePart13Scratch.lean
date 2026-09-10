import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart12Scratch

/-! Part 13 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def omicronQuarticInnerABCE810 (a b c e : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + 60 * a ^ 2 * b * c ^ 2 + (-1120 : k) * a * b ^ 3 * c + 1920 * a * b * c * e + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + 2880 * b * c ^ 3 + (-5120 : k) * b * e ^ 2


def piQuarticInnerABCE810 (a b c e : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-360 : k) * a * b ^ 2 * c ^ 2 + (-560 : k) * b ^ 4 * c + 2880 * b ^ 2 * c * e + 240 * c ^ 4 + (-2560 : k) * c * e ^ 2


def primitiveQuarticInnerABCE810 (a b c e : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + 60 * a ^ 3 * b * c ^ 2 + 120 * a ^ 2 * b ^ 3 * c + 960 * a ^ 2 * b * c * e + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + (-960 : k) * a * b * c ^ 3 + 5120 * a * b * e ^ 2 + (-8480 : k) * b ^ 3 * c ^ 2 + 23040 * b * c ^ 2 * e


end QuarticKills810
end Max11DegreeRoutes
end
