import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart22Scratch

/-! Part 23 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def primitiveQuarticInnerABCF810 (a b c f : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * c * f + 120 * a ^ 2 * b ^ 3 * c + (-160 : k) * a ^ 2 * b ^ 2 * f + 520 * a * b ^ 5 + (-960 : k) * a * b * c ^ 3 + (-8480 : k) * b ^ 3 * c ^ 2 + 21760 * b ^ 2 * c * f + (-20480 : k) * b * f ^ 2


set_option maxHeartbeats 32000000 in
theorem quarticInner_ABCF_identity
    (a b c f : k) :
    ((1 / 2080 : k) * a ^ 3 * b + (-761 / 66560 : k) * a * b * c + (567 / 166400 : k) * a * f + (3933 / 332800 : k) * b ^ 3) * kappaQuarticInnerABCF810 a b c f +
      ((-9 / 6656 : k) * a * b ^ 2 + (-1 / 80 : k) * c ^ 2) * muQuarticInnerABCF810 a b c f +
      ((1 / 2080 : k) * a ^ 2 * b + (239 / 66560 : k) * b * c + (87 / 166400 : k) * f) * nuQuarticInnerABCF810 a b c f +
      ((-3 / 2080 : k) * a * c + (261 / 332800 : k) * b ^ 2) * xiQuarticInnerABCF810 a b c f =
      c ^ 5 := by
  simp only [kappaQuarticInnerABCF810, muQuarticInnerABCF810, nuQuarticInnerABCF810, xiQuarticInnerABCF810, omicronQuarticInnerABCF810, piQuarticInnerABCF810, primitiveQuarticInnerABCF810]
  ring


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABCF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)


end QuarticKills810
end Max11DegreeRoutes
end
