import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart01Scratch
import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart02Scratch

/-! Part 3 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def primitiveQuarticInnerABCD810 (a b c d : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + 60 * a ^ 3 * b * c ^ 2 + 120 * a ^ 2 * b ^ 3 * c + (-800 : k) * a ^ 2 * b * d ^ 2 + 480 * a ^ 2 * c ^ 2 * d + 520 * a * b ^ 5 + (-8640 : k) * a * b ^ 2 * c * d + (-960 : k) * a * b * c ^ 3 + 2560 * a * d ^ 3 + (-4000 : k) * b ^ 4 * d + (-8480 : k) * b ^ 3 * c ^ 2 + 23040 * b * c * d ^ 2 + 7680 * c ^ 3 * d


set_option maxHeartbeats 32000000 in
theorem quarticInner_ABCD_identity
    (a b c d : k) :
    ((-1319 / 727680 : k) * a ^ 3 * b + (4229 / 363840 : k) * a ^ 2 * d + (-83147 / 1819200 : k) * a * b * c + (2737 / 242560 : k) * b ^ 3 + (9107 / 37900 : k) * c * d) * kappaQuarticInnerABCD810 a b c d +
      ((-47 / 48512 : k) * a * b ^ 2 + (-1401 / 60640 : k) * b * d + (2153 / 303200 : k) * c ^ 2) * muQuarticInnerABCD810 a b c d +
      ((-929 / 727680 : k) * a ^ 2 * b + (2441 / 363840 : k) * a * d + (3587 / 606400 : k) * b * c) * nuQuarticInnerABCD810 a b c d +
      ((149 / 90960 : k) * a * c + (819 / 60640 : k) * b ^ 2) * xiQuarticInnerABCD810 a b c d +
      ((-13 / 24256 : k) * a * b) * omicronQuarticInnerABCD810 a b c d +
      ((1981 / 303200 : k) * c) * piQuarticInnerABCD810 a b c d =
      c ^ 5 := by
  simp only [kappaQuarticInnerABCD810, muQuarticInnerABCD810, nuQuarticInnerABCD810, xiQuarticInnerABCD810, omicronQuarticInnerABCD810, piQuarticInnerABCD810, primitiveQuarticInnerABCD810]
  ring


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABCD810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)


end QuarticKills810
end Max11DegreeRoutes
end
