import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 21 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerBDEF810 (b d e f : k) : k :=
  (-15 : k) * b ^ 2 * d + 40 * d * e

def muQuarticInnerBDEF810 (b d e f : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + 640 * d * f + 320 * e ^ 2

def nuQuarticInnerBDEF810 (b d e f : k) : k :=
  (-15 : k) * b ^ 2 * f + (-15 : k) * b * d ^ 2 + 40 * e * f

def xiQuarticInnerBDEF810 (b d e f : k) : k :=
  55 * b ^ 3 * d + (-200 : k) * b * d * e + 160 * f ^ 2

def omicronQuarticInnerBDEF810 (b d e f : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + (-640 : k) * b * d * f + (-320 : k) * b * e ^ 2 + (-160 : k) * d ^ 3

def piQuarticInnerBDEF810 (b d e f : k) : k :=
  25 * b ^ 3 * f + 45 * b ^ 2 * d ^ 2 + (-120 : k) * b * e * f + (-80 : k) * d ^ 2 * e

def primitiveQuarticInnerBDEF810 (b d e f : k) : k :=
  (-125 : k) * b ^ 4 * d + 680 * b ^ 2 * d * e + (-640 : k) * b * f ^ 2 + (-640 : k) * d ^ 2 * f + (-640 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_BDEF_identity
    (b d e f : k) :
    ((480 / 7 : k) * b ^ 2 * f + (-6856 / 21 : k) * b * d ^ 2 + (-32512 / 63 : k) * e * f) * kappaQuarticInnerBDEF810 b d e f +
      ((-13 / 28 : k) * b ^ 4 + (10 / 7 : k) * b ^ 2 * e + (160 / 7 : k) * d * f) * muQuarticInnerBDEF810 b d e f +
      ((20992 / 63 : k) * d * e) * nuQuarticInnerBDEF810 b d e f +
      ((-640 / 7 : k) * d ^ 2) * xiQuarticInnerBDEF810 b d e f +
      ((-23 / 28 : k) * b ^ 3 + (10 / 7 : k) * b * e) * omicronQuarticInnerBDEF810 b d e f =
      b ^ 8 := by
  simp only [kappaQuarticInnerBDEF810, muQuarticInnerBDEF810, nuQuarticInnerBDEF810, xiQuarticInnerBDEF810, omicronQuarticInnerBDEF810, piQuarticInnerBDEF810, primitiveQuarticInnerBDEF810]
  ring

end QuarticKills810

end Max11DegreeRoutes
