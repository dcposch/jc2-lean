import Grok810ScaleZeroQuarticMultiKillsPart23Scratch

/-! Part 24 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


def muQuarticInnerACG810 (a c g : k) : k :=
  (-5 : k) * c ^ 3 + 40 * c * g


def piQuarticInnerACG810 (a c g : k) : k :=
  15 * c ^ 4 + (-80 : k) * c ^ 2 * g + 320 * g ^ 2


set_option maxHeartbeats 32000000 in
theorem quarticInner_ACG_identity
    (a c g : k) :
    ((1 / 10 : k) * c ^ 2 + (-4 / 5 : k) * g) * muQuarticInnerACG810 a c g +
      ((1 / 10 : k) * c) * piQuarticInnerACG810 a c g =
      c ^ 5 := by
  simp only [muQuarticInnerACG810, piQuarticInnerACG810]
  ring


set_option maxHeartbeats 16000000 in
def muQuarticFaceACG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  + (5 / 16 : k) • (C * G)


end QuarticKills810
end Max11DegreeRoutes
end
