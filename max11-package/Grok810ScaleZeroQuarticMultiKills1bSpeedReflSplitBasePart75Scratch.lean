import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart73Scratch
import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart74Scratch

/-! Part 75 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def primitiveQuarticInnerABFG810 (a b f g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-160 : k) * a ^ 3 * b * g + (-160 : k) * a ^ 2 * b ^ 2 * f + 520 * a * b ^ 5 + (-20480 : k) * a * f * g + 3840 * b ^ 3 * g + (-20480 : k) * b * f ^ 2


set_option maxHeartbeats 32000000 in
theorem quarticInner_ABFG_identity
    (a b f g : k) :
    ((1 / 480 : k) * a * g + (3 / 320 : k) * b * f) * kappaQuarticInnerABFG810 a b f g +
      ((1 / 480 : k) * g) * nuQuarticInnerABFG810 a b f g +
      ((1 / 320 : k) * f) * xiQuarticInnerABFG810 a b f g =
      f ^ 3 := by
  simp only [kappaQuarticInnerABFG810, muQuarticInnerABFG810, nuQuarticInnerABFG810, xiQuarticInnerABFG810, omicronQuarticInnerABFG810, piQuarticInnerABFG810, primitiveQuarticInnerABFG810]
  ring


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (B * G)


end QuarticKills810
end Max11DegreeRoutes
end
