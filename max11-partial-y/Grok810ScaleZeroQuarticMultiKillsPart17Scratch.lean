import Grok810ScaleZeroQuarticMultiKillsPart15Scratch
import Grok810ScaleZeroQuarticMultiKillsPart16Scratch

/-! Part 17 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


def piQuarticInnerABD810 (a b d : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + 1440 * b ^ 2 * d ^ 2


def primitiveQuarticInnerABD810 (a b d : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + (-800 : k) * a ^ 2 * b * d ^ 2 + 520 * a * b ^ 5 + 2560 * a * d ^ 3 + (-4000 : k) * b ^ 4 * d


set_option maxHeartbeats 32000000 in
theorem quarticInner_ABD_identity
    (a b d : k) :
    ((-37 / 38400 : k) * a ^ 2 * d + (-7 / 3200 : k) * b ^ 3) * kappaQuarticInnerABD810 a b d +
      ((1 / 3200 : k) * a * b ^ 2 + (-3 / 400 : k) * b * d) * muQuarticInnerABD810 a b d +
      ((-11 / 19200 : k) * a * d) * nuQuarticInnerABD810 a b d +
      ((-1 / 2560 : k) * d) * omicronQuarticInnerABD810 a b d =
      d ^ 4 := by
  simp only [kappaQuarticInnerABD810, muQuarticInnerABD810, nuQuarticInnerABD810, xiQuarticInnerABD810, omicronQuarticInnerABD810, piQuarticInnerABD810, primitiveQuarticInnerABD810]
  ring


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABD810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)


end QuarticKills810
end Max11DegreeRoutes
end
