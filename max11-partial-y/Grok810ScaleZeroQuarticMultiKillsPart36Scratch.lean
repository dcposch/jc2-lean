import Grok810ScaleZeroQuarticMultiKillsPart35Scratch

/-! Part 36 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


def piQuarticInnerBCF810 (b c f : k) : k :=
  (-35 : k) * b ^ 4 * c + 50 * b ^ 3 * f + 15 * c ^ 4


def primitiveQuarticInnerBCF810 (b c f : k) : k :=
  (-265 : k) * b ^ 3 * c ^ 2 + 680 * b ^ 2 * c * f + (-640 : k) * b * f ^ 2


set_option maxHeartbeats 32000000 in
theorem quarticInner_BCF_identity
    (b c f : k) :
    ((32 / 21 : k) * c) * kappaQuarticInnerBCF810 b c f +
      ((1 / 7 : k) * b) * muQuarticInnerBCF810 b c f +
      ((4 / 21 : k)) * omicronQuarticInnerBCF810 b c f =
      b ^ 5 := by
  simp only [kappaQuarticInnerBCF810, muQuarticInnerBCF810, nuQuarticInnerBCF810, xiQuarticInnerBCF810, omicronQuarticInnerBCF810, piQuarticInnerBCF810, primitiveQuarticInnerBCF810]
  ring


set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBCF810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)


end QuarticKills810
end Max11DegreeRoutes
end
