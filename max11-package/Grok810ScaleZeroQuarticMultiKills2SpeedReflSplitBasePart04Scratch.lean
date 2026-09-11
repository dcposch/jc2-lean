import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 4 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerBCDF810 (b c d f : k) : k :=
  (-15 : k) * b ^ 2 * d + (-15 : k) * b * c ^ 2 + 40 * c * f

def muQuarticInnerBCDF810 (b c d f : k) : k :=
  35 * b ^ 4 + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * d * f

def nuQuarticInnerBCDF810 (b c d f : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b ^ 2 * f + (-60 : k) * b * d ^ 2 + (-60 : k) * c ^ 2 * d

def xiQuarticInnerBCDF810 (b c d f : k) : k :=
  55 * b ^ 3 * d + 90 * b ^ 2 * c ^ 2 + (-200 : k) * b * c * f + (-120 : k) * c * d ^ 2 + 160 * f ^ 2

def omicronQuarticInnerBCDF810 (b c d f : k) : k :=
  (-21 : k) * b ^ 5 + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-640 : k) * b * d * f + (-320 : k) * c ^ 2 * f + (-160 : k) * d ^ 3

def piQuarticInnerBCDF810 (b c d f : k) : k :=
  (-35 : k) * b ^ 4 * c + 50 * b ^ 3 * f + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + 15 * c ^ 4 + (-240 : k) * c * d * f

def primitiveQuarticInnerBCDF810 (b c d f : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 680 * b ^ 2 * c * f + 720 * b * c * d ^ 2 + (-640 : k) * b * f ^ 2 + 240 * c ^ 3 * d + (-640 : k) * d ^ 2 * f

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCDF_identity
    (b c d f : k) :
    ((-67 / 12000 : k) * b ^ 3 + (-23 / 50 : k) * c * d) * kappaQuarticInnerBCDF810 b c d f +
      ((-69 / 8000 : k) * b * d + (-9 / 320 : k) * c ^ 2) * muQuarticInnerBCDF810 b c d f +
      ((-547 / 4000 : k) * b * c + (2 / 75 : k) * f) * nuQuarticInnerBCDF810 b c d f +
      ((-19 / 2000 : k) * b ^ 2) * xiQuarticInnerBCDF810 b c d f +
      ((-1 / 160 : k) * d) * omicronQuarticInnerBCDF810 b c d f +
      ((-3 / 20 : k) * c) * piQuarticInnerBCDF810 b c d f +
      ((-39 / 8000 : k) * b) * primitiveQuarticInnerBCDF810 b c d f =
      d ^ 4 := by
  simp only [kappaQuarticInnerBCDF810, muQuarticInnerBCDF810, nuQuarticInnerBCDF810, xiQuarticInnerBCDF810, omicronQuarticInnerBCDF810, piQuarticInnerBCDF810, primitiveQuarticInnerBCDF810]
  ring

end QuarticKills810

end Max11DegreeRoutes
