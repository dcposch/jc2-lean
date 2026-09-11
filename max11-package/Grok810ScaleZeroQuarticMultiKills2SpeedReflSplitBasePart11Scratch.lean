import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 11 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerBCEF810 (b c e f : k) : k :=
  (-15 : k) * b * c ^ 2 + 40 * c * f

def muQuarticInnerBCEF810 (b c e f : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-80 : k) * c ^ 3 + 320 * e ^ 2

def nuQuarticInnerBCEF810 (b c e f : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b ^ 2 * f + (-120 : k) * b * c * e + 160 * e * f

def xiQuarticInnerBCEF810 (b c e f : k) : k :=
  45 * b ^ 2 * c ^ 2 + (-100 : k) * b * c * f + (-60 : k) * c ^ 2 * e + 80 * f ^ 2

def omicronQuarticInnerBCEF810 (b c e f : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + 180 * b * c ^ 3 + (-320 : k) * b * e ^ 2 + (-320 : k) * c ^ 2 * f

def piQuarticInnerBCEF810 (b c e f : k) : k :=
  (-35 : k) * b ^ 4 * c + 50 * b ^ 3 * f + 180 * b ^ 2 * c * e + (-240 : k) * b * e * f + 15 * c ^ 4 + (-160 : k) * c * e ^ 2

def primitiveQuarticInnerBCEF810 (b c e f : k) : k :=
  (-265 : k) * b ^ 3 * c ^ 2 + 680 * b ^ 2 * c * f + 720 * b * c ^ 2 * e + (-640 : k) * b * f ^ 2 + (-1280 : k) * c * e * f

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCEF_identity
    (b c e f : k) :
    ((-16 / 105 : k) * b ^ 6 * c + (-128 / 315 : k) * b ^ 5 * f + (-256 / 245 : k) * b ^ 4 * c * e + (-1441792 / 11025 : k) * b ^ 3 * e * f + (-12073984 / 91875 : k) * b ^ 2 * c ^ 4 + (8623168 / 128625 : k) * b ^ 2 * c * e ^ 2 + (-48295936 / 385875 : k) * b * c ^ 3 * f + (1025990656 / 1929375 : k) * b * e ^ 2 * f + (96591872 / 214375 : k) * c ^ 4 * e + (129744896 / 214375 : k) * c ^ 2 * f ^ 2 + (-81880576 / 128625 : k) * c * e ^ 3) * kappaQuarticInnerBCEF810 b c e f +
      ((1 / 35 : k) * b ^ 7 + (48 / 245 : k) * b ^ 5 * e + (-4016 / 343 : k) * b ^ 3 * e ^ 2 + (-48526336 / 275625 : k) * b * c * f ^ 2 + (13184 / 343 : k) * b * e ^ 3 + (24147968 / 214375 : k) * c ^ 2 * e * f + (64872448 / 214375 : k) * f ^ 3) * muQuarticInnerBCEF810 b c e f +
      ((16218112 / 91875 : k) * b ^ 2 * f ^ 2 + (-15388672 / 91875 : k) * b * c * e * f + (-12073984 / 214375 : k) * c ^ 5 + (4785024 / 42875 : k) * c ^ 2 * e ^ 2 + (-1427193856 / 1929375 : k) * e * f ^ 2) * nuQuarticInnerBCEF810 b c e f +
      ((518979584 / 1929375 : k) * e ^ 2 * f) * xiQuarticInnerBCEF810 b c e f +
      ((-7312 / 343 : k) * b ^ 2 * e ^ 2 + (13184 / 343 : k) * e ^ 3) * omicronQuarticInnerBCEF810 b c e f =
      b ^ 11 := by
  simp only [kappaQuarticInnerBCEF810, muQuarticInnerBCEF810, nuQuarticInnerBCEF810, xiQuarticInnerBCEF810, omicronQuarticInnerBCEF810, piQuarticInnerBCEF810, primitiveQuarticInnerBCEF810]
  ring

end QuarticKills810

end Max11DegreeRoutes
