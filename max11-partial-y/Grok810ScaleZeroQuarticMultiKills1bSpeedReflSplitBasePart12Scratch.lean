import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 12 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def muQuarticInnerABCE810 (a b c e : k) : k :=
  60 * a * b ^ 2 * c + 35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-80 : k) * c ^ 3 + 320 * e ^ 2


def nuQuarticInnerABCE810 (a b c e : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 60 * a * b * c ^ 2 + 280 * b ^ 3 * c + (-960 : k) * b * c * e


def xiQuarticInnerABCE810 (a b c e : k) : k :=
  (-15 : k) * a * b ^ 4 + 60 * a * b ^ 2 * e + 180 * b ^ 2 * c ^ 2 + (-240 : k) * c ^ 2 * e


end QuarticKills810
end Max11DegreeRoutes
end
