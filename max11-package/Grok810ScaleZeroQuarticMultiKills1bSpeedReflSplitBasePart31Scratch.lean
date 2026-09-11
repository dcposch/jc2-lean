import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart29Scratch
import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart30Scratch

/-! Part 31 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def primitiveQuarticInnerABCG810 (a b c g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * b * g + 120 * a ^ 2 * b ^ 3 * c + 520 * a * b ^ 5 + (-960 : k) * a * b * c ^ 3 + 2560 * a * b * c * g + (-8480 : k) * b ^ 3 * c ^ 2 + 3840 * b ^ 3 * g


set_option maxHeartbeats 32000000 in
theorem quarticInner_ABCG_identity
    (a b c g : k) :
    ((-11 / 4480 : k) * a ^ 3 * b + (-19 / 320 : k) * a * b * c + (21 / 320 : k) * b ^ 3) * kappaQuarticInnerABCG810 a b c g +
      ((9 / 640 : k) * a * b ^ 2 + (1 / 160 : k) * c ^ 2 + (-1 / 20 : k) * g) * muQuarticInnerABCG810 a b c g +
      ((-11 / 4480 : k) * a ^ 2 * b + (-3 / 320 : k) * b * c) * nuQuarticInnerABCG810 a b c g +
      ((7 / 128 : k) * b ^ 2) * xiQuarticInnerABCG810 a b c g +
      ((1 / 160 : k) * c) * piQuarticInnerABCG810 a b c g =
      c ^ 5 := by
  simp only [kappaQuarticInnerABCG810, muQuarticInnerABCG810, nuQuarticInnerABCG810, xiQuarticInnerABCG810, omicronQuarticInnerABCG810, piQuarticInnerABCG810, primitiveQuarticInnerABCG810]
  ring


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABCG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)


end QuarticKills810
end Max11DegreeRoutes
end
