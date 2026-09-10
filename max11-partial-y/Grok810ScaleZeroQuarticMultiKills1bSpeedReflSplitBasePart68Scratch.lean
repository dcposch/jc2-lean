import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart67Scratch

/-! Part 68 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def piQuarticInnerABEG810 (a b e g : k) : k :=
  15 * a ^ 2 * b ^ 4 + 320 * a * b ^ 2 * g + 5120 * g ^ 2


def primitiveQuarticInnerABEG810 (a b e g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-160 : k) * a ^ 3 * b * g + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + 5120 * a * b * e ^ 2 + 3840 * b ^ 3 * g + (-20480 : k) * b * e * g


set_option maxHeartbeats 32000000 in
theorem quarticInner_ABEG_identity
    (a b e g : k) :
    ((-23 / 448 : k) * a ^ 2 * b ^ 2 + (5 / 56 : k) * a ^ 2 * e) * kappaQuarticInnerABEG810 a b e g +
      ((-13 / 28 : k) * b ^ 3 + (10 / 7 : k) * b * e) * muQuarticInnerABEG810 a b e g +
      ((-23 / 448 : k) * b ^ 2 + (5 / 56 : k) * e) * omicronQuarticInnerABEG810 a b e g =
      b ^ 7 := by
  simp only [kappaQuarticInnerABEG810, muQuarticInnerABEG810, nuQuarticInnerABEG810, xiQuarticInnerABEG810, omicronQuarticInnerABEG810, piQuarticInnerABEG810, primitiveQuarticInnerABEG810]
  ring


end QuarticKills810
end Max11DegreeRoutes
end
