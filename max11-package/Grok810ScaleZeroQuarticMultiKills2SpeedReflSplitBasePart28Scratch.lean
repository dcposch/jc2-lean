import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 28 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`; statements are byte-identical.
-/

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

def kappaQuarticInnerBDFG810 (b d f g : k) : k :=
  (-15 : k) * b ^ 2 * d + 40 * b * g

def muQuarticInnerBDFG810 (b d f g : k) : k :=
  35 * b ^ 4 + 640 * d * f

def nuQuarticInnerBDFG810 (b d f g : k) : k :=
  (-15 : k) * b ^ 2 * f + (-15 : k) * b * d ^ 2 + 40 * d * g

def xiQuarticInnerBDFG810 (b d f g : k) : k :=
  55 * b ^ 3 * d + (-80 : k) * b ^ 2 * g + 160 * f ^ 2

def omicronQuarticInnerBDFG810 (b d f g : k) : k :=
  (-21 : k) * b ^ 5 + (-640 : k) * b * d * f + (-160 : k) * d ^ 3 + 1280 * f * g

def piQuarticInnerBDFG810 (b d f g : k) : k :=
  25 * b ^ 3 * f + 45 * b ^ 2 * d ^ 2 + (-80 : k) * b * d * g + 160 * g ^ 2

def primitiveQuarticInnerBDFG810 (b d f g : k) : k :=
  (-125 : k) * b ^ 4 * d + 120 * b ^ 3 * g + (-640 : k) * b * f ^ 2 + (-640 : k) * d ^ 2 * f

set_option maxHeartbeats 32000000 in
theorem quarticInner_BDFG_identity
    (b d f g : k) :
    ((-128 / 105 : k) * d ^ 2) * kappaQuarticInnerBDFG810 b d f g +
      ((1 / 35 : k) * b ^ 3) * muQuarticInnerBDFG810 b d f g +
      ((128 / 105 : k) * b * d) * nuQuarticInnerBDFG810 b d f g =
      b ^ 7 := by
  simp only [kappaQuarticInnerBDFG810, muQuarticInnerBDFG810, nuQuarticInnerBDFG810, xiQuarticInnerBDFG810, omicronQuarticInnerBDFG810, piQuarticInnerBDFG810, primitiveQuarticInnerBDFG810]
  ring

end QuarticKills810

end Max11DegreeRoutes
