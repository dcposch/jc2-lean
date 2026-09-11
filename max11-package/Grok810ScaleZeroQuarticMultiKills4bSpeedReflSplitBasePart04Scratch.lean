import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 4 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerBCDEF810 (b c d e f : k) : k :=
  (-15 : k) * b ^ 2 * d + (-15 : k) * b * c ^ 2 + 40 * c * f + 40 * d * e

def muQuarticInnerBCDEF810 (b c d e f : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * d * f + 320 * e ^ 2

def nuQuarticInnerBCDEF810 (b c d e f : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b ^ 2 * f + (-120 : k) * b * c * e + (-60 : k) * b * d ^ 2 + (-60 : k) * c ^ 2 * d + 160 * e * f

def xiQuarticInnerBCDEF810 (b c d e f : k) : k :=
  55 * b ^ 3 * d + 90 * b ^ 2 * c ^ 2 + (-200 : k) * b * c * f + (-200 : k) * b * d * e + (-120 : k) * c ^ 2 * e + (-120 : k) * c * d ^ 2 + 160 * f ^ 2

def omicronQuarticInnerBCDEF810 (b c d e f : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-640 : k) * b * d * f + (-320 : k) * b * e ^ 2 + (-320 : k) * c ^ 2 * f + (-800 : k) * c * d * e + (-160 : k) * d ^ 3

def piQuarticInnerBCDEF810 (b c d e f : k) : k :=
  (-35 : k) * b ^ 4 * c + 50 * b ^ 3 * f + 180 * b ^ 2 * c * e + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + (-240 : k) * b * e * f + 15 * c ^ 4 + (-240 : k) * c * d * f + (-160 : k) * c * e ^ 2 + (-160 : k) * d ^ 2 * e

def primitiveQuarticInnerBCDEF810 (b c d e f : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 680 * b ^ 2 * c * f + 680 * b ^ 2 * d * e + 720 * b * c ^ 2 * e + 720 * b * c * d ^ 2 + (-640 : k) * b * f ^ 2 + 240 * c ^ 3 * d + (-1280 : k) * c * e * f + (-640 : k) * d ^ 2 * f + (-640 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCDEF_identity
    (b c d e f : k) :
    ((5856019861 / 12769491545600 : k) * b ^ 4 * d + (-54944173451 / 12097413043200 : k) * b ^ 3 * c ^ 2 + (4117052321 / 2094994706700 : k) * b ^ 2 * c * f + (-153008969 / 167599576536 : k) * b ^ 2 * d * e + (670351762721 / 67039830614400 : k) * b * c ^ 2 * e + (3117429893 / 1596186443200 : k) * b * c * d ^ 2 + (66994308781 / 2394279664800 : k) * b * f ^ 2 + (-38833312739 / 3351991530720 : k) * c ^ 3 * d + (622239207463 / 12569968240200 : k) * c * e * f + (-87284367397 / 2793326275600 : k) * d ^ 2 * f + (-27178691719 / 4189989413400 : k) * d * e ^ 2) * kappaQuarticInnerBCDEF810 b c d e f +
      ((-887750649 / 5586652551200 : k) * b ^ 3 * f + (149192413 / 558665255120 : k) * b ^ 2 * c * e + (-6520437989 / 17877288163840 : k) * b * c ^ 2 * d + (13439415371 / 5586652551200 : k) * b * e * f + (-29381166921 / 178772881638400 : k) * c ^ 4 + (-16804476719 / 4788559329600 : k) * c * d * f + (-5679925609 / 2793326275600 : k) * c * e ^ 2 + (-40980415589 / 33519915307200 : k) * d ^ 2 * e) * muQuarticInnerBCDEF810 b c d e f +
      ((-1995531 / 14701717240 : k) * b ^ 3 * e + (-10344927983 / 8379978826800 : k) * b * c ^ 3 + (-79495316587 / 5586652551200 : k) * b * d * f + (-2079564153 / 2793326275600 : k) * b * e ^ 2 + (1618396469 / 1795709748600 : k) * c ^ 2 * f + (42759268939 / 6284984120100 : k) * c * d * e + (5856019861 / 6703983061440 : k) * d ^ 3) * nuQuarticInnerBCDEF810 b c d e f +
      ((-8486878607 / 15323389854720 : k) * b ^ 2 * c ^ 2 + (978366343 / 1197139832400 : k) * b * c * f + (933757931 / 2394279664800 : k) * b * d * e + (10603295 / 6720785024 : k) * c ^ 2 * e + (2237965889 / 1915423731840 : k) * c * d ^ 2 + (1 / 160 : k) * f ^ 2) * xiQuarticInnerBCDEF810 b c d e f +
      ((-295916883 / 1117330510240 : k) * b ^ 2 * f + (-225022591 / 558665255120 : k) * b * c * e + (-5856019861 / 17877288163840 : k) * b * d ^ 2 + (-5380445271 / 4469322040960 : k) * c ^ 2 * d + (5679925609 / 1117330510240 : k) * e * f) * omicronQuarticInnerBCDEF810 b c d e f +
      ((260469737 / 698331568900 : k) * b ^ 2 * e + (3455893409 / 2793326275600 : k) * b * c * d + (-9793722307 / 11173305102400 : k) * c ^ 3 + (-332683353 / 19671311800 : k) * d * f + (-5679925609 / 1396663137800 : k) * e ^ 2) * piQuarticInnerBCDEF810 b c d e f =
      f ^ 4 := by
  simp only [kappaQuarticInnerBCDEF810, muQuarticInnerBCDEF810, nuQuarticInnerBCDEF810, xiQuarticInnerBCDEF810, omicronQuarticInnerBCDEF810, piQuarticInnerBCDEF810, primitiveQuarticInnerBCDEF810]
  ring

end QuarticKills810

end Max11DegreeRoutes
