import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 0 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`; statements are byte-identical.
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

def kappaQuarticInnerACDEF810 (a c d e f : k) : k :=
  5 * c * f + 5 * d * e

def muQuarticInnerACDEF810 (a c d e f : k) : k :=
  (-5 : k) * a * d ^ 2 + (-5 : k) * c ^ 3 + 40 * d * f + 20 * e ^ 2

def nuQuarticInnerACDEF810 (a c d e f : k) : k :=
  (-5 : k) * a * c * f + (-5 : k) * a * d * e + (-15 : k) * c ^ 2 * d + 40 * e * f

def xiQuarticInnerACDEF810 (a c d e f : k) : k :=
  (-10 : k) * a * d * f + (-15 : k) * c ^ 2 * e + (-15 : k) * c * d ^ 2 + 20 * f ^ 2

def omicronQuarticInnerACDEF810 (a c d e f : k) : k :=
  (-5 : k) * a ^ 2 * c * f + (-5 : k) * a ^ 2 * d * e + 30 * a * c ^ 2 * d + (-80 : k) * a * e * f + (-160 : k) * c ^ 2 * f + (-400 : k) * c * d * e + (-80 : k) * d ^ 3

def piQuarticInnerACDEF810 (a c d e f : k) : k :=
  40 * a * c * d ^ 2 + (-80 : k) * a * f ^ 2 + 15 * c ^ 4 + (-240 : k) * c * d * f + (-160 : k) * c * e ^ 2 + (-160 : k) * d ^ 2 * e

def primitiveQuarticInnerACDEF810 (a c d e f : k) : k :=
  (-5 : k) * a ^ 3 * c * f + (-5 : k) * a ^ 3 * d * e + 15 * a ^ 2 * c ^ 2 * d + (-40 : k) * a ^ 2 * e * f + 240 * a * c * d * e + 80 * a * d ^ 3 + 240 * c ^ 3 * d + (-1280 : k) * c * e * f + (-640 : k) * d ^ 2 * f + (-640 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_ACDEF_identity
    (a c d e f : k) :
    ((2097 / 99520 : k) * a ^ 3 * f + (7771 / 149280 : k) * a ^ 2 * c * d + (199 / 622 : k) * a * c * f + (-175 / 3732 : k) * a * d * e + (3917 / 6220 : k) * c ^ 2 * d + (1051 / 4665 : k) * e * f) * kappaQuarticInnerACDEF810 a c d e f +
      ((111 / 6220 : k) * c ^ 3 + (233 / 6220 : k) * d * f + (1 / 20 : k) * e ^ 2) * muQuarticInnerACDEF810 a c d e f +
      ((699 / 49760 : k) * a ^ 2 * f + (2837 / 74640 : k) * a * c * d + (-452 / 4665 : k) * d * e) * nuQuarticInnerACDEF810 a c d e f +
      ((-1051 / 18660 : k) * c * e + (-233 / 3110 : k) * d ^ 2) * xiQuarticInnerACDEF810 a c d e f +
      ((699 / 99520 : k) * a * f + (699 / 49760 : k) * c * d) * omicronQuarticInnerACDEF810 a c d e f +
      ((37 / 6220 : k) * c ^ 2) * piQuarticInnerACDEF810 a c d e f =
      e ^ 4 := by
  simp only [kappaQuarticInnerACDEF810, muQuarticInnerACDEF810, nuQuarticInnerACDEF810, xiQuarticInnerACDEF810, omicronQuarticInnerACDEF810, piQuarticInnerACDEF810, primitiveQuarticInnerACDEF810]
  ring

end QuarticKills810

end Max11DegreeRoutes
