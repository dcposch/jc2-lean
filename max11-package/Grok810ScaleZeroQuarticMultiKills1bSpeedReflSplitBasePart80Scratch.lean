import Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBasePart79Scratch

/-! Part 80 of 84 of `Grok810ScaleZeroQuarticMultiKills1bSpeedReflSplitBaseScratch`, split so that no single module elaborates them all
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


def xiQuarticInnerACEG810 (a c e g : k) : k :=
  (-15 : k) * c ^ 2 * e + 40 * e * g


def piQuarticInnerACEG810 (a c e g : k) : k :=
  15 * c ^ 4 + (-80 : k) * c ^ 2 * g + (-160 : k) * c * e ^ 2 + 320 * g ^ 2


set_option maxHeartbeats 32000000 in
theorem quarticInner_ACEG_identity
    (a c e g : k) :
    ((-3 / 5120 : k) * c ^ 3 * g + (63 / 56320 : k) * c ^ 2 * e ^ 2 + (1 / 128 : k) * c * g ^ 2 + (7 / 1408 : k) * e ^ 2 * g) * muQuarticInnerACEG810 a c e g +
      ((9 / 14080 : k) * c * e * g + (-7 / 2816 : k) * e ^ 3) * xiQuarticInnerACEG810 a c e g +
      ((-1 / 5120 : k) * c ^ 2 * g + (21 / 56320 : k) * c * e ^ 2 + (1 / 320 : k) * g ^ 2) * piQuarticInnerACEG810 a c e g =
      g ^ 4 := by
  simp only [muQuarticInnerACEG810, xiQuarticInnerACEG810, piQuarticInnerACEG810]
  ring


end QuarticKills810
end Max11DegreeRoutes
end
