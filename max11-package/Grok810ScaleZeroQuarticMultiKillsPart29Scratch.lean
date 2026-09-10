import Grok810ScaleZeroQuarticMultiKillsPart28Scratch

/-! Part 29 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


def omicronQuarticInnerBCD810 (b c d : k) : k :=
  (-21 : k) * b ^ 5 + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-160 : k) * d ^ 3


def piQuarticInnerBCD810 (b c d : k) : k :=
  (-35 : k) * b ^ 4 * c + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + 15 * c ^ 4


def primitiveQuarticInnerBCD810 (b c d : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 720 * b * c * d ^ 2 + 240 * c ^ 3 * d


set_option maxHeartbeats 32000000 in
theorem quarticInner_BCD_identity
    (b c d : k) :
    ((-16 / 105 : k) * b ^ 2 * c + (-64 / 49 : k) * d ^ 2) * kappaQuarticInnerBCD810 b c d +
      ((1 / 35 : k) * b ^ 3) * muQuarticInnerBCD810 b c d +
      ((16 / 49 : k) * b * d) * nuQuarticInnerBCD810 b c d =
      b ^ 7 := by
  simp only [kappaQuarticInnerBCD810, muQuarticInnerBCD810, nuQuarticInnerBCD810, xiQuarticInnerBCD810, omicronQuarticInnerBCD810, piQuarticInnerBCD810, primitiveQuarticInnerBCD810]
  ring


end QuarticKills810
end Max11DegreeRoutes
end
