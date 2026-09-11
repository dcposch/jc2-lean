import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 18 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerBCFG810 (b c f g : k) : k :=
  (-15 : k) * b * c ^ 2 + 40 * b * g + 40 * c * f

def muQuarticInnerBCFG810 (b c f g : k) : k :=
  35 * b ^ 4 + (-80 : k) * c ^ 3 + 640 * c * g

def nuQuarticInnerBCFG810 (b c f g : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b ^ 2 * f

def xiQuarticInnerBCFG810 (b c f g : k) : k :=
  45 * b ^ 2 * c ^ 2 + (-40 : k) * b ^ 2 * g + (-100 : k) * b * c * f + 80 * f ^ 2

def omicronQuarticInnerBCFG810 (b c f g : k) : k :=
  (-21 : k) * b ^ 5 + 180 * b * c ^ 3 + (-480 : k) * b * c * g + (-320 : k) * c ^ 2 * f + 1280 * f * g

def piQuarticInnerBCFG810 (b c f g : k) : k :=
  (-35 : k) * b ^ 4 * c + 50 * b ^ 3 * f + 15 * c ^ 4 + (-80 : k) * c ^ 2 * g + 320 * g ^ 2

def primitiveQuarticInnerBCFG810 (b c f g : k) : k :=
  (-265 : k) * b ^ 3 * c ^ 2 + 120 * b ^ 3 * g + 680 * b ^ 2 * c * f + (-640 : k) * b * f ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCFG_identity
    (b c f g : k) :
    ((24 / 175 : k) * b ^ 2 * c + (-96 / 175 : k) * b * f) * kappaQuarticInnerBCFG810 b c f g +
      ((1 / 35 : k) * b ^ 3) * muQuarticInnerBCFG810 b c f g +
      ((-8 / 35 : k) * c ^ 2 + (-64 / 175 : k) * g) * nuQuarticInnerBCFG810 b c f g +
      ((48 / 175 : k) * b * c) * xiQuarticInnerBCFG810 b c f g =
      b ^ 7 := by
  simp only [kappaQuarticInnerBCFG810, muQuarticInnerBCFG810, nuQuarticInnerBCFG810, xiQuarticInnerBCFG810, omicronQuarticInnerBCFG810, piQuarticInnerBCFG810, primitiveQuarticInnerBCFG810]
  ring

end QuarticKills810

end Max11DegreeRoutes
