import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart39Scratch

/-! Part 40 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def piQuarticInnerABDE810 (a b d e : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + 1280 * a * b * d * e + 1440 * b ^ 2 * d ^ 2 + (-2560 : k) * d ^ 2 * e


def primitiveQuarticInnerABDE810 (a b d e : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + (-160 : k) * a ^ 3 * d * e + (-800 : k) * a ^ 2 * b * d ^ 2 + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + 5120 * a * b * e ^ 2 + 2560 * a * d ^ 3 + (-4000 : k) * b ^ 4 * d + 21760 * b ^ 2 * d * e + (-20480 : k) * d * e ^ 2


set_option maxHeartbeats 32000000 in
theorem quarticInner_ABDE_identity
    (a b d e : k) :
    ((1 / 1024 : k) * a ^ 3 * b + (-23 / 12800 : k) * a ^ 2 * d + (-11 / 9600 : k) * b ^ 3 + (31 / 1200 : k) * b * e) * kappaQuarticInnerABDE810 a b d e +
      ((41 / 9600 : k) * a * b ^ 2 + (-31 / 2400 : k) * b * d) * muQuarticInnerABDE810 a b d e +
      ((1 / 1536 : k) * a ^ 2 * b + (-9 / 6400 : k) * a * d) * nuQuarticInnerABDE810 a b d e +
      ((11 / 4800 : k) * b ^ 2 + (1 / 200 : k) * e) * xiQuarticInnerABDE810 a b d e +
      ((1 / 3072 : k) * a * b + (-1 / 2560 : k) * d) * omicronQuarticInnerABDE810 a b d e =
      d ^ 4 := by
  simp only [kappaQuarticInnerABDE810, muQuarticInnerABDE810, nuQuarticInnerABDE810, xiQuarticInnerABDE810, omicronQuarticInnerABDE810, piQuarticInnerABDE810, primitiveQuarticInnerABDE810]
  ring


end QuarticKills810
end Max11DegreeRoutes
end
