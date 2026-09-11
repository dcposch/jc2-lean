import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 17 of `Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitBaseScratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitBaseScratch`; statements are byte-identical.
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

def kappaQuarticInnerABCEG810 (a b c e g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b * c ^ 2 + 160 * b * g

def muQuarticInnerABCEG810 (a b c e g : k) : k :=
  60 * a * b ^ 2 * c + 35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-80 : k) * c ^ 3 + 640 * c * g + 320 * e ^ 2

def nuQuarticInnerABCEG810 (a b c e g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 60 * a * b * c ^ 2 + (-160 : k) * a * b * g + 280 * b ^ 3 * c + (-960 : k) * b * c * e

def xiQuarticInnerABCEG810 (a b c e g : k) : k :=
  (-15 : k) * a * b ^ 4 + 60 * a * b ^ 2 * e + 180 * b ^ 2 * c ^ 2 + (-160 : k) * b ^ 2 * g + (-240 : k) * c ^ 2 * e + 640 * e * g

def omicronQuarticInnerABCEG810 (a b c e g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * b * g + (-1120 : k) * a * b ^ 3 * c + 1920 * a * b * c * e + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + 2880 * b * c ^ 3 + (-7680 : k) * b * c * g + (-5120 : k) * b * e ^ 2

def piQuarticInnerABCEG810 (a b c e g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-360 : k) * a * b ^ 2 * c ^ 2 + 320 * a * b ^ 2 * g + (-560 : k) * b ^ 4 * c + 2880 * b ^ 2 * c * e + 240 * c ^ 4 + (-1280 : k) * c ^ 2 * g + (-2560 : k) * c * e ^ 2 + 5120 * g ^ 2

def primitiveQuarticInnerABCEG810 (a b c e g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * b * g + 120 * a ^ 2 * b ^ 3 * c + 960 * a ^ 2 * b * c * e + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + (-960 : k) * a * b * c ^ 3 + 2560 * a * b * c * g + 5120 * a * b * e ^ 2 + (-8480 : k) * b ^ 3 * c ^ 2 + 3840 * b ^ 3 * g + 23040 * b * c ^ 2 * e + (-20480 : k) * b * e * g

set_option maxHeartbeats 32000000 in
theorem quarticInner_ABCEG_identity
    (a b c e g : k) :
    ((-17877 / 978560 : k) * a ^ 3 * b * c ^ 2 + (3199 / 122320 : k) * a ^ 3 * b * g + (113053289 / 242682880 : k) * a ^ 2 * b * c * e + (-6738891 / 30335360 : k) * a * b ^ 3 * e + (-845777 / 1957120 : k) * a * b * c ^ 3 + (14611451 / 7583840 : k) * a * b * c * g + (1015793 / 1516768 : k) * a * b * e ^ 2 + (271761 / 1378880 : k) * b ^ 3 * c ^ 2 + (-93779 / 122320 : k) * b ^ 3 * g + (13047479 / 15167680 : k) * b * c ^ 2 * e + (41677 / 15290 : k) * b * e * g) * kappaQuarticInnerABCEG810 a b c e g +
      ((-17877 / 489280 : k) * a ^ 2 * b ^ 2 * e + (95001 / 978560 : k) * a * b ^ 2 * c ^ 2 + (-40213 / 122320 : k) * a * b ^ 2 * g + (17877 / 122320 : k) * a * c ^ 2 * e + (-5959 / 15290 : k) * a * e * g + (17469 / 3033536 : k) * b ^ 2 * c * e + (-1 / 80 : k) * c ^ 4 + (1 / 20 : k) * c ^ 2 * g + (16 / 55 : k) * c * e ^ 2 + (-2 / 5 : k) * g ^ 2) * muQuarticInnerABCEG810 a b c e g +
      ((-17877 / 978560 : k) * a ^ 2 * b * c ^ 2 + (4119 / 122320 : k) * a ^ 2 * b * g + (708611 / 24268288 : k) * a * b * c * e + (-17469 / 6067072 : k) * b ^ 3 * e + (-56389 / 391424 : k) * b * c ^ 3 + (4041691 / 7583840 : k) * b * c * g + (33011 / 689440 : k) * b * e ^ 2) * nuQuarticInnerABCEG810 a b c e g +
      ((-38737 / 244640 : k) * a * b ^ 2 * e + (-5959 / 122320 : k) * a * c ^ 3 + (5959 / 15290 : k) * a * c * g + (5959 / 30580 : k) * a * e ^ 2 + (8864653 / 30335360 : k) * b ^ 2 * c ^ 2 + (-52241 / 61160 : k) * b ^ 2 * g + (-17 / 220 : k) * c ^ 2 * e + (-1 / 11 : k) * e * g) * xiQuarticInnerABCEG810 a b c e g +
      ((-23 / 3058 : k) * a * b * g + (-87345 / 48536576 : k) * b * c * e) * omicronQuarticInnerABCEG810 a b c e g +
      ((1 / 20 : k) * c * g + (2 / 55 : k) * e ^ 2) * piQuarticInnerABCEG810 a b c e g =
      c ^ 7 := by
  simp only [kappaQuarticInnerABCEG810, muQuarticInnerABCEG810, nuQuarticInnerABCEG810, xiQuarticInnerABCEG810, omicronQuarticInnerABCEG810, piQuarticInnerABCEG810, primitiveQuarticInnerABCEG810]
  ring

end QuarticKills810

end Max11DegreeRoutes
