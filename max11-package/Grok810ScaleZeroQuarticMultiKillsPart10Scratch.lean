import Grok810ScaleZeroQuarticMultiKillsPart09Scratch

/-! Part 10 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


def omicronQuarticInnerABC810 (a b c : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + 60 * a ^ 2 * b * c ^ 2 + (-1120 : k) * a * b ^ 3 * c + (-336 : k) * b ^ 5 + 2880 * b * c ^ 3


def piQuarticInnerABC810 (a b c : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-360 : k) * a * b ^ 2 * c ^ 2 + (-560 : k) * b ^ 4 * c + 240 * c ^ 4


def primitiveQuarticInnerABC810 (a b c : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + 60 * a ^ 3 * b * c ^ 2 + 120 * a ^ 2 * b ^ 3 * c + 520 * a * b ^ 5 + (-960 : k) * a * b * c ^ 3 + (-8480 : k) * b ^ 3 * c ^ 2


set_option maxHeartbeats 32000000 in
theorem quarticInner_ABC_identity
    (a b c : k) :
    ((-73 / 5120 : k) * a * b * c + (-21 / 2560 : k) * b ^ 3) * kappaQuarticInnerABC810 a b c +
      ((3 / 2560 : k) * a * b ^ 2 + (-1 / 80 : k) * c ^ 2) * muQuarticInnerABC810 a b c +
      ((-1 / 5120 : k) * b * c) * nuQuarticInnerABC810 a b c =
      c ^ 5 := by
  simp only [kappaQuarticInnerABC810, muQuarticInnerABC810, nuQuarticInnerABC810, xiQuarticInnerABC810, omicronQuarticInnerABC810, piQuarticInnerABC810, primitiveQuarticInnerABC810]
  ring


end QuarticKills810
end Max11DegreeRoutes
end
