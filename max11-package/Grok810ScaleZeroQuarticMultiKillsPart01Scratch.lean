import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! Part 1 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


def muQuarticInnerBE810 (b e : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + 320 * e ^ 2


def omicronQuarticInnerBE810 (b e : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + (-320 : k) * b * e ^ 2


theorem quarticInner_BE_identity
    (b e : k) :
    ((-13 / 28 : k) * b ^ 3 + (10 / 7 : k) * b * e) * muQuarticInnerBE810 b e +
      ((-23 / 28 : k) * b ^ 2 + (10 / 7 : k) * e) * omicronQuarticInnerBE810 b e =
      b ^ 7 := by
  simp only [muQuarticInnerBE810, omicronQuarticInnerBE810]
  ring


set_option maxHeartbeats 16000000 in
def muQuarticFaceBE810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  + (5 / 32 : k) • E ^ 2


end QuarticKills810
end Max11DegreeRoutes
end
