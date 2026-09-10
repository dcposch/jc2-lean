import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart58Scratch

/-! Part 59 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def primitiveQuarticInnerABDG810 (a b d g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + (-160 : k) * a ^ 3 * b * g + (-800 : k) * a ^ 2 * b * d ^ 2 + (-1280 : k) * a ^ 2 * d * g + 520 * a * b ^ 5 + 2560 * a * d ^ 3 + (-4000 : k) * b ^ 4 * d + 3840 * b ^ 3 * g


set_option maxHeartbeats 32000000 in
theorem quarticInner_ABDG_identity
    (a b d g : k) :
    ((-43 / 64000 : k) * a ^ 2 * d) * kappaQuarticInnerABDG810 a b d g +
      ((3 / 4000 : k) * a * b ^ 2 + (-37 / 4000 : k) * b * d + (1 / 125 : k) * g) * muQuarticInnerABDG810 a b d g +
      ((-9 / 32000 : k) * a * d) * nuQuarticInnerABDG810 a b d g +
      ((7 / 4000 : k) * b ^ 2) * xiQuarticInnerABDG810 a b d g +
      ((-1 / 2560 : k) * d) * omicronQuarticInnerABDG810 a b d g =
      d ^ 4 := by
  simp only [kappaQuarticInnerABDG810, muQuarticInnerABDG810, nuQuarticInnerABDG810, xiQuarticInnerABDG810, omicronQuarticInnerABDG810, piQuarticInnerABDG810, primitiveQuarticInnerABDG810]
  ring


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABDG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)


end QuarticKills810
end Max11DegreeRoutes
end
