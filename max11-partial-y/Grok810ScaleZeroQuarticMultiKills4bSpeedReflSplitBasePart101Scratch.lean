import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch
import Grok810ScaleZeroQuarticDefsScratch

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
/-! # Part 8 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerBCDEG810 (b c d e g : k) : k :=
  (-15 : k) * b ^ 2 * d + (-15 : k) * b * c ^ 2 + 40 * b * g + 40 * d * e

def muQuarticInnerBCDEG810 (b c d e g : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * c * g + 320 * e ^ 2

def nuQuarticInnerBCDEG810 (b c d e g : k) : k :=
  35 * b ^ 3 * c + (-120 : k) * b * c * e + (-60 : k) * b * d ^ 2 + (-60 : k) * c ^ 2 * d + 160 * d * g

def xiQuarticInnerBCDEG810 (b c d e g : k) : k :=
  55 * b ^ 3 * d + 90 * b ^ 2 * c ^ 2 + (-80 : k) * b ^ 2 * g + (-200 : k) * b * d * e + (-120 : k) * c ^ 2 * e + (-120 : k) * c * d ^ 2 + 320 * e * g

def omicronQuarticInnerBCDEG810 (b c d e g : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-480 : k) * b * c * g + (-320 : k) * b * e ^ 2 + (-800 : k) * c * d * e + (-160 : k) * d ^ 3

def piQuarticInnerBCDEG810 (b c d e g : k) : k :=
  (-35 : k) * b ^ 4 * c + 180 * b ^ 2 * c * e + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + (-160 : k) * b * d * g + 15 * c ^ 4 + (-80 : k) * c ^ 2 * g + (-160 : k) * c * e ^ 2 + (-160 : k) * d ^ 2 * e + 320 * g ^ 2

def primitiveQuarticInnerBCDEG810 (b c d e g : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 120 * b ^ 3 * g + 680 * b ^ 2 * d * e + 720 * b * c ^ 2 * e + 720 * b * c * d ^ 2 + (-640 : k) * b * e * g + 240 * c ^ 3 * d + (-640 : k) * c * d * g + (-640 : k) * d * e ^ 2

set_option maxHeartbeats 64000000 in
theorem quarticInner_BCDEG_identity
    (b c d e g : k) :
    ((-25686694503478743 / 14916339186188222464 : k) * b ^ 4 * c * d + (-1958592148964633 / 3925352417417953280 : k) * b ^ 3 * c ^ 3 + (212962847516251 / 73600357826586624 : k) * b ^ 3 * c * g + (-19379141224833 / 196267620870897664 : k) * b ^ 3 * e ^ 2 + (11537019432645313 / 932271199136763904 : k) * b ^ 2 * c * d * e + (-616420093976163 / 3729084796547055616 : k) * b ^ 2 * d ^ 3 + (939317705213721 / 490669052177244160 : k) * b * c ^ 3 * e + (1681843467312838013 / 37290847965470556160 : k) * b * c ^ 2 * d ^ 2 + (-1720412315508397 / 122667263044311040 : k) * b * c * e * g + (-8751490750323411 / 2330677997841909760 : k) * b * d ^ 2 * g + (29483730440343 / 122667263044311040 : k) * b * e ^ 3 + (472532382559468199 / 74581695930941112320 : k) * c ^ 4 * d + (-642037454305765443 / 9322711991367639040 : k) * c ^ 2 * d * g + (-40249488613413473 / 4661355995683819520 : k) * c * d * e ^ 2 + (7772100477067313 / 9322711991367639040 : k) * d ^ 3 * e + (289364722125257 / 18400089456646656 : k) * d * g ^ 2) * kappaQuarticInnerBCDEG810 b c d e g +
      ((-34761552192303 / 245334526088622080 : k) * b ^ 2 * e * g + (-14513265344315031 / 15701409669671813120 : k) * b * c ^ 3 * d + (4262752319251469 / 1962676208708976640 : k) * b * c * d * g + (-29483730440343 / 981338104354488320 : k) * b * d * e ^ 2 + (-3 / 81920 : k) * c ^ 3 * g + (18647753130261 / 981338104354488320 : k) * c ^ 2 * e ^ 2 + (27513490006482343 / 18645423982735278080 : k) * c * d ^ 2 * e + (1 / 2048 : k) * c * g ^ 2 + (-1118892612660777 / 3925352417417953280 : k) * d ^ 4 + (54769227269329 / 122667263044311040 : k) * e ^ 2 * g) * muQuarticInnerBCDEG810 b c d e g +
      ((-839396635270557 / 3925352417417953280 : k) * b * c ^ 4 + (354282485933507 / 196267620870897664 : k) * b * c ^ 2 * g + (2828799918687 / 49066905217724416 : k) * b * c * e ^ 2 + (-173021323491619 / 291334749730238720 : k) * b * d ^ 2 * e + (-296818019585869 / 368001789132933120 : k) * b * g ^ 2 + (-2118226446433937 / 18645423982735278080 : k) * c ^ 2 * d * e + (-2497257460630121 / 1962676208708976640 : k) * c * d ^ 3 + (13187229835760279 / 6992033993525729280 : k) * d * e * g) * nuQuarticInnerBCDEG810 b c d e g +
      ((-5857212642225 / 98133810435448832 : k) * b ^ 2 * c * g + (19379141224833 / 196267620870897664 : k) * b ^ 2 * e ^ 2 + (78833174276629 / 981338104354488320 : k) * b * c * d * e + (10166137440483051 / 74581695930941112320 : k) * b * d ^ 3 + (8326755828597 / 245334526088622080 : k) * c ^ 3 * e + (28528663003045603 / 37290847965470556160 : k) * c ^ 2 * d ^ 2 + (-23505839299839 / 122667263044311040 : k) * c * e * g + (-657792838576287 / 932271199136763904 : k) * d ^ 2 * g + (-54769227269329 / 122667263044311040 : k) * e ^ 3) * xiQuarticInnerBCDEG810 b c d e g +
      ((18347638931056245 / 14916339186188222464 : k) * b * c * d ^ 2 + (-11587184064101 / 49066905217724416 : k) * b * e * g + (2737923303750561 / 59665356744752889856 : k) * c ^ 3 * d + (-14046405175158643 / 7458169593094111232 : k) * c * d * g + (54769227269329 / 196267620870897664 : k) * d * e ^ 2) * omicronQuarticInnerBCDEG810 b c d e g +
      ((-1 / 5120 : k) * c ^ 2 * g + (21 / 56320 : k) * c * e ^ 2 + (-597325308616499 / 932271199136763904 : k) * d ^ 2 * e + (1 / 320 : k) * g ^ 2) * piQuarticInnerBCDEG810 b c d e g =
      g ^ 4 := by
  simp only [kappaQuarticInnerBCDEG810, muQuarticInnerBCDEG810, nuQuarticInnerBCDEG810, xiQuarticInnerBCDEG810, omicronQuarticInnerBCDEG810, piQuarticInnerBCDEG810, primitiveQuarticInnerBCDEG810]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 12 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-15 : k) * b ^ 2 * d + (-15 : k) * b * c ^ 2 + 40 * b * g + 40 * c * f

def muQuarticInnerBCDFG810 (b c d f g : k) : k :=
  35 * b ^ 4 + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * c * g + 640 * d * f

def nuQuarticInnerBCDFG810 (b c d f g : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b ^ 2 * f + (-60 : k) * b * d ^ 2 + (-60 : k) * c ^ 2 * d + 160 * d * g

def xiQuarticInnerBCDFG810 (b c d f g : k) : k :=
  55 * b ^ 3 * d + 90 * b ^ 2 * c ^ 2 + (-80 : k) * b ^ 2 * g + (-200 : k) * b * c * f + (-120 : k) * c * d ^ 2 + 160 * f ^ 2

def omicronQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-21 : k) * b ^ 5 + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-480 : k) * b * c * g + (-640 : k) * b * d * f + (-320 : k) * c ^ 2 * f + (-160 : k) * d ^ 3 + 1280 * f * g

def piQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-35 : k) * b ^ 4 * c + 50 * b ^ 3 * f + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + (-160 : k) * b * d * g + 15 * c ^ 4 + (-80 : k) * c ^ 2 * g + (-240 : k) * c * d * f + 320 * g ^ 2

def primitiveQuarticInnerBCDFG810 (b c d f g : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 120 * b ^ 3 * g + 680 * b ^ 2 * c * f + 720 * b * c * d ^ 2 + (-640 : k) * b * f ^ 2 + 240 * c ^ 3 * d + (-640 : k) * c * d * g + (-640 : k) * d ^ 2 * f

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCDFG_identity
    (b c d f g : k) :
    ((49721439699 / 92489280634880 : k) * b ^ 4 * d + (-1412223896701 / 55493568380928 : k) * b ^ 3 * c ^ 2 + (-433327923123 / 11561160079360 : k) * b ^ 3 * g + (718669049307 / 16185624111104 : k) * b ^ 2 * c * f + (338005186913 / 5780580039680 : k) * b * c * d ^ 2 + (181171989941 / 5780580039680 : k) * b * f ^ 2 + (600807275947 / 10116015069440 : k) * c ^ 3 * d + (-13099546853549 / 60696090416640 : k) * c * d * g + (-1897249609669 / 40464060277760 : k) * d ^ 2 * f) * kappaQuarticInnerBCDFG810 b c d f g +
      ((69797673027 / 129484992888832 : k) * b ^ 3 * f + (1038672910209 / 258969985777664 : k) * b * c ^ 2 * d + (765235362377 / 161856241111040 : k) * b * d * g + (191100579987 / 323712482222080 : k) * c ^ 4 + (-63700193329 / 20232030138880 : k) * c ^ 2 * g + (-128691860909 / 23122320158720 : k) * c * d * f + (63700193329 / 5058007534720 : k) * g ^ 2) * muQuarticInnerBCDFG810 b c d f g +
      ((-1213263453279 / 161856241111040 : k) * b * c ^ 3 + (1471610468093 / 60696090416640 : k) * b * c * g + (-934271627935 / 32371248222208 : k) * b * d * f + (221467542707 / 8670870059520 : k) * c ^ 2 * f + (16573813233 / 16185624111104 : k) * d ^ 3 + (-7193167623 / 2023203013888 : k) * f * g) * nuQuarticInnerBCDFG810 b c d f g +
      ((-12263569863 / 36995712253952 : k) * b ^ 2 * c ^ 2 + (-61185507293 / 4624464031744 : k) * b ^ 2 * g + (-528863701 / 23122320158720 : k) * b * c * f + (-11963841453 / 4624464031744 : k) * c * d ^ 2 + (1 / 160 : k) * f ^ 2) * xiQuarticInnerBCDFG810 b c d f g +
      ((116329455045 / 129484992888832 : k) * b ^ 2 * f + (-49721439699 / 129484992888832 : k) * b * d ^ 2 + (5303137653 / 3407499812864 : k) * c ^ 2 * d + (16573813233 / 16185624111104 : k) * d * g) * omicronQuarticInnerBCDFG810 b c d f g +
      ((133856743379 / 10116015069440 : k) * b * c * d + (63700193329 / 20232030138880 : k) * c ^ 3 + (-63700193329 / 2529003767360 : k) * c * g + (-278252387341 / 10116015069440 : k) * d * f) * piQuarticInnerBCDFG810 b c d f g =
      f ^ 4 := by
  simp only [kappaQuarticInnerBCDFG810, muQuarticInnerBCDFG810, nuQuarticInnerBCDFG810, xiQuarticInnerBCDFG810, omicronQuarticInnerBCDFG810, piQuarticInnerBCDFG810, primitiveQuarticInnerBCDFG810]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 16 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerBCEFG810 (b c e f g : k) : k :=
  (-15 : k) * b * c ^ 2 + 40 * b * g + 40 * c * f

def muQuarticInnerBCEFG810 (b c e f g : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-80 : k) * c ^ 3 + 640 * c * g + 320 * e ^ 2

def nuQuarticInnerBCEFG810 (b c e f g : k) : k :=
  35 * b ^ 3 * c + (-60 : k) * b ^ 2 * f + (-120 : k) * b * c * e + 160 * e * f

def xiQuarticInnerBCEFG810 (b c e f g : k) : k :=
  45 * b ^ 2 * c ^ 2 + (-40 : k) * b ^ 2 * g + (-100 : k) * b * c * f + (-60 : k) * c ^ 2 * e + 160 * e * g + 80 * f ^ 2

def omicronQuarticInnerBCEFG810 (b c e f g : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + 180 * b * c ^ 3 + (-480 : k) * b * c * g + (-320 : k) * b * e ^ 2 + (-320 : k) * c ^ 2 * f + 1280 * f * g

def piQuarticInnerBCEFG810 (b c e f g : k) : k :=
  (-35 : k) * b ^ 4 * c + 50 * b ^ 3 * f + 180 * b ^ 2 * c * e + (-240 : k) * b * e * f + 15 * c ^ 4 + (-80 : k) * c ^ 2 * g + (-160 : k) * c * e ^ 2 + 320 * g ^ 2

def primitiveQuarticInnerBCEFG810 (b c e f g : k) : k :=
  (-265 : k) * b ^ 3 * c ^ 2 + 120 * b ^ 3 * g + 680 * b ^ 2 * c * f + 720 * b * c ^ 2 * e + (-640 : k) * b * e * g + (-640 : k) * b * f ^ 2 + (-1280 : k) * c * e * f

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCEFG_identity
    (b c e f g : k) :
    ((-1752793 / 122880 : k) * b ^ 3 * c * g + (20099 / 3604480 : k) * b ^ 3 * e ^ 2 + (-7602413 / 21626880 : k) * b ^ 2 * c ^ 2 * f + (663151 / 811008 : k) * b ^ 2 * f * g + (-2298357 / 901120 : k) * b * c ^ 3 * e + (8263249 / 122880 : k) * b * c * e * g + (113241803 / 16220160 : k) * b * c * f ^ 2 + (205249 / 40960 : k) * b * e ^ 3 + (-7412243 / 5406720 : k) * c ^ 2 * e * f + (-20111485 / 202752 : k) * e * f * g + (1370671 / 2027520 : k) * f ^ 3) * kappaQuarticInnerBCEFG810 b c e f g +
      ((3976167 / 1802240 : k) * b ^ 2 * e * g + (409455 / 720896 : k) * b ^ 2 * f ^ 2 + (-1512557 / 1441792 : k) * b * c * e * f + (-3 / 81920 : k) * c ^ 3 * g + (2298609 / 3604480 : k) * c ^ 2 * e ^ 2 + (1 / 2048 : k) * c * g ^ 2 + (-765979 / 450560 : k) * e ^ 2 * g + (687057 / 901120 : k) * e * f ^ 2) * muQuarticInnerBCEFG810 b c e f g +
      ((2513033 / 3604480 : k) * b ^ 2 * e * f + (-279621 / 450560 : k) * b * c * e ^ 2 + (55657 / 5120 : k) * b * g ^ 2 + (-1086059 / 7208960 : k) * c ^ 3 * f + (21065777 / 901120 : k) * c * f * g + (-363259 / 112640 : k) * e ^ 2 * f) * nuQuarticInnerBCEFG810 b c e f g +
      ((-1168559 / 245760 : k) * b ^ 2 * c * g + (-20099 / 1802240 : k) * b ^ 2 * e ^ 2 + (-62788921 / 4055040 : k) * b * f * g + (-766119 / 901120 : k) * c ^ 3 * e + (766137 / 112640 : k) * c * e * g + (-1370671 / 4055040 : k) * c * f ^ 2 + (765979 / 225280 : k) * e ^ 3) * xiQuarticInnerBCEFG810 b c e f g +
      ((1325389 / 360448 : k) * b * e * g + (682425 / 720896 : k) * b * f ^ 2 + (-845573 / 1441792 : k) * c * e * f) * omicronQuarticInnerBCEFG810 b c e f g +
      ((-1 / 5120 : k) * c ^ 2 * g + (21 / 56320 : k) * c * e ^ 2 + (1 / 320 : k) * g ^ 2) * piQuarticInnerBCEFG810 b c e f g =
      g ^ 4 := by
  simp only [kappaQuarticInnerBCEFG810, muQuarticInnerBCEFG810, nuQuarticInnerBCEFG810, xiQuarticInnerBCEFG810, omicronQuarticInnerBCEFG810, piQuarticInnerBCEFG810, primitiveQuarticInnerBCEFG810]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 20 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerBDEFG810 (b d e f g : k) : k :=
  (-15 : k) * b ^ 2 * d + 40 * b * g + 40 * d * e

def muQuarticInnerBDEFG810 (b d e f g : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + 640 * d * f + 320 * e ^ 2

def nuQuarticInnerBDEFG810 (b d e f g : k) : k :=
  (-15 : k) * b ^ 2 * f + (-15 : k) * b * d ^ 2 + 40 * d * g + 40 * e * f

def xiQuarticInnerBDEFG810 (b d e f g : k) : k :=
  55 * b ^ 3 * d + (-80 : k) * b ^ 2 * g + (-200 : k) * b * d * e + 320 * e * g + 160 * f ^ 2

def omicronQuarticInnerBDEFG810 (b d e f g : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + (-640 : k) * b * d * f + (-320 : k) * b * e ^ 2 + (-160 : k) * d ^ 3 + 1280 * f * g

def piQuarticInnerBDEFG810 (b d e f g : k) : k :=
  25 * b ^ 3 * f + 45 * b ^ 2 * d ^ 2 + (-80 : k) * b * d * g + (-120 : k) * b * e * f + (-80 : k) * d ^ 2 * e + 160 * g ^ 2

def primitiveQuarticInnerBDEFG810 (b d e f g : k) : k :=
  (-125 : k) * b ^ 4 * d + 120 * b ^ 3 * g + 680 * b ^ 2 * d * e + (-640 : k) * b * e * g + (-640 : k) * b * f ^ 2 + (-640 : k) * d ^ 2 * f + (-640 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_BDEFG_identity
    (b d e f g : k) :
    ((128 / 105 : k) * b ^ 6 * f + (5120 / 441 : k) * b ^ 4 * e * f + (-177823936 / 3573255 : k) * b ^ 3 * d ^ 2 * e + (-38150144 / 102093 : k) * b ^ 3 * g ^ 2 + (152600576 / 238217 : k) * b ^ 2 * d * e * g + (104102112512 / 58363165 : k) * b ^ 2 * d * f ^ 2 + (59592407552 / 35017899 : k) * b ^ 2 * e ^ 2 * f + (85705858944 / 58363165 : k) * b * d ^ 3 * f + (25209086464 / 35017899 : k) * b * d ^ 2 * e ^ 2 + (1220804608 / 714651 : k) * b * e * g ^ 2 + (-361404408832 / 35017899 : k) * b * f ^ 2 * g + (-14284309824 / 11672633 : k) * d ^ 5 + (108521978368 / 58363165 : k) * d ^ 2 * f * g + (-950559340544 / 175089495 : k) * d * e ^ 2 * g + (-1790846772224 / 525268485 : k) * d * e * f ^ 2 + (-33271402496 / 15007671 : k) * e ^ 3 * f) * kappaQuarticInnerBDEFG810 b d e f g +
      ((1 / 35 : k) * b ^ 8 + (48 / 245 : k) * b ^ 6 * e + (-4016 / 343 : k) * b ^ 4 * e ^ 2 + (-1024 / 735 : k) * b ^ 3 * f * g + (13184 / 343 : k) * b ^ 2 * e ^ 3 + (-2391599984 / 11672633 : k) * b * d ^ 3 * e + (-38150144 / 238217 : k) * b * d * g ^ 2 + (377768122496 / 525268485 : k) * b * e * f * g + (20122773056 / 58363165 : k) * b * f ^ 3 + (8289617408 / 25012785 : k) * d ^ 2 * e * g + (-1559295232 / 25012785 : k) * d ^ 2 * f ^ 2 + (10122437632 / 105053697 : k) * d * e ^ 2 * f + (305201152 / 714651 : k) * g ^ 3) * muQuarticInnerBDEFG810 b d e f g +
      ((3143068672 / 25012785 : k) * b ^ 3 * f ^ 2 + (14284309824 / 11672633 : k) * b * d ^ 4 + (-108521978368 / 58363165 : k) * b * d * f * g + (501913647104 / 175089495 : k) * b * e ^ 2 * g + (-546085888 / 58363165 : k) * b * e * f ^ 2 + (297767667712 / 175089495 : k) * d ^ 2 * e * f + (50640105472 / 35017899 : k) * d * e ^ 3 + (-4883218432 / 714651 : k) * f * g ^ 2) * nuQuarticInnerBDEFG810 b d e f g +
      ((98120811008 / 175089495 : k) * b * d * f ^ 2 + (1413427712 / 5002557 : k) * b * e ^ 2 * f + (42852929472 / 58363165 : k) * d ^ 3 * f + (29142529792 / 175089495 : k) * d ^ 2 * e ^ 2 + (-305201152 / 714651 : k) * e * g ^ 2 + (-135837635072 / 35017899 : k) * f ^ 2 * g) * xiQuarticInnerBDEFG810 b d e f g +
      ((-7312 / 343 : k) * b ^ 3 * e ^ 2 + (13184 / 343 : k) * b * e ^ 3 + (-3571077456 / 11672633 : k) * d ^ 3 * e + (14435398016 / 11672633 : k) * e * f * g + (16979704384 / 35017899 : k) * f ^ 3) * omicronQuarticInnerBDEFG810 b d e f g =
      b ^ 12 := by
  simp only [kappaQuarticInnerBDEFG810, muQuarticInnerBDEFG810, nuQuarticInnerBDEFG810, xiQuarticInnerBDEFG810, omicronQuarticInnerBDEFG810, piQuarticInnerBDEFG810, primitiveQuarticInnerBDEFG810]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 1 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

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

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoACDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (5 / 1024 * delta : k) • A ^ 3
  + (5 / 64 * delta : k) • (A * C)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E
  + (1 / 2 * epsilon : k) • D
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceACDEF810 A B C D E F G +
        degreeZeroKappaQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceACDEF810, degreeZeroKappaQuarticNoACDEF810]
  all_goals module

theorem kappaQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (kappaQuarticFaceACDEF810 A B C D E F G).coeff (C.natDegree + F.natDegree) =
      (1 / 16 : k) * kappaQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [kappaQuarticFaceACDEF810, kappaQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_CF : ((C * F)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hCne hFne]
  have hcf_CF : ((C * F)).coeff (C.natDegree + F.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DE : ((D * E)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (C.natDegree + F.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_CF, hcf_DE]
  ring

set_option maxHeartbeats 16000000 in
def muQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoACDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  - (45 / 262144 * l : k) • (A ^ 4 * B)
  - (9 / 8192 * l : k) • (A ^ 3 * D)
  - (9 / 8192 * l : k) • (A ^ 2 * B * C)
  + (63 / 8192 * l : k) • (A * B ^ 3)
  - (9 / 1024 * l : k) • (A ^ 2 * F)
  - (9 / 512 * l : k) • (A * B * E)
  - (9 / 512 * l : k) • (A * C * D)
  - (63 / 1024 * l : k) • (B ^ 2 * D)
  - (63 / 1024 * l : k) • (B * C ^ 2)
  + (9 / 64 * l : k) • (B * G)
  + (9 / 64 * l : k) • (C * F)
  + (9 / 64 * l : k) • (D * E)
  - (7 / 8192 * beta : k) • (A ^ 3 * B)
  - (7 / 1024 * beta : k) • (A ^ 2 * D)
  + (7 / 512 * beta : k) • (A * B * C)
  + (21 / 1024 * beta : k) • B ^ 3
  - (7 / 64 * beta : k) • (A * F)
  - (7 / 64 * beta : k) • (B * E)
  - (7 / 64 * beta : k) • (C * D)
  + (3 / 128 * gamma : k) • (A * B ^ 2)
  - (3 / 16 * gamma : k) • (B * D)
  - (3 / 32 * gamma : k) • C ^ 2
  + (3 / 4 * gamma : k) • G
  - (5 / 1024 * delta : k) • (A ^ 2 * B)
  - (5 / 64 * delta : k) • (A * D)
  - (15 / 64 * delta : k) • (B * C)
  + (5 / 8 * delta : k) • F
  - (1 / 8 * epsilon : k) • B ^ 2
  + (1 / 2 * epsilon : k) • E
  - (3 / 64 * zeta : k) • (A * B)
  + (3 / 8 * zeta : k) • D
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceACDEF810 A B C D E F G +
        degreeZeroMuQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceACDEF810, degreeZeroMuQuarticNoACDEF810]
  all_goals module

theorem muQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (muQuarticFaceACDEF810 A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) =
      (1 / 128 : k) * muQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [muQuarticFaceACDEF810, muQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_DF : ((D * F)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (A.natDegree + 2 * D.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * D.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AD2, hcf_C3, hcf_DF, hcf_E2]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 2 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

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

set_option maxHeartbeats 16000000 in
def nuQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoACDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  + (5 / 16 : k) • (D * G)
  + (105 / 4194304 * l : k) • A ^ 6
  + (135 / 262144 * l : k) • (A ^ 4 * C)
  + (9 / 4096 * l : k) • (A ^ 3 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 4096 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (9 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * F)
  - (9 / 512 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2
  + (7 / 65536 * beta : k) • A ^ 5
  + (7 / 4096 * beta : k) • (A ^ 3 * C)
  - (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 256 * beta : k) • (A * B * D)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2
  + (3 / 128 * gamma : k) • (A * B * C)
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 32 * gamma : k) • (A * F)
  - (3 / 16 * gamma : k) • (B * E)
  - (3 / 16 * gamma : k) • (C * D)
  + (15 / 32768 * delta : k) • A ^ 4
  + (5 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 512 * delta : k) • (A * B ^ 2)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G
  - (1 / 16 * epsilon : k) • (A * D)
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F
  + (1 / 512 * zeta : k) • A ^ 3
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  - (1 / 32 * eta : k) • (A * B)
  + (1 / 4 * eta : k) • D
  + (1 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceACDEF810 A B C D E F G +
        degreeZeroNuQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceACDEF810, degreeZeroNuQuarticNoACDEF810]
  all_goals module

theorem nuQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (nuQuarticFaceACDEF810 A B C D E F G).coeff (A.natDegree + C.natDegree + F.natDegree) =
      (1 / 128 : k) * nuQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [nuQuarticFaceACDEF810, nuQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_ACF : ((A * C * F)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) hFne, natDegree_mul hAne hCne]
  have hcf_ACF : ((A * C * F)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ACF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ADE : ((A * D * E)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    omega
  have hcf_ADE : ((A * D * E)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ADE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_EF : ((E * F)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (A.natDegree + C.natDegree + F.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_ACF, hcf_ADE, hcf_C2D, hcf_EF]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoACDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  + (5 / 16 : k) • (E * G)
  - (45 / 262144 * l : k) • (A ^ 4 * D)
  + (9 / 16384 * l : k) • (A ^ 3 * B * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 3)
  - (9 / 8192 * l : k) • (A ^ 3 * F)
  + (9 / 4096 * l : k) • (A ^ 2 * B * E)
  - (9 / 8192 * l : k) • (A ^ 2 * C * D)
  + (171 / 8192 * l : k) • (A * B ^ 2 * D)
  + (9 / 1024 * l : k) • (A * B * C ^ 2)
  + (63 / 2048 * l : k) • (B ^ 3 * C)
  - (9 / 512 * l : k) • (A * C * F)
  - (9 / 512 * l : k) • (A * D * E)
  - (45 / 1024 * l : k) • (B ^ 2 * F)
  - (27 / 256 * l : k) • (B * C * E)
  - (27 / 512 * l : k) • (B * D ^ 2)
  - (63 / 1024 * l : k) • (C ^ 2 * D)
  + (9 / 64 * l : k) • (D * G)
  + (9 / 64 * l : k) • (E * F)
  - (7 / 8192 * beta : k) • (A ^ 3 * D)
  + (7 / 2048 * beta : k) • (A ^ 2 * B * C)
  - (7 / 1024 * beta : k) • (A * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 2 * F)
  + (7 / 256 * beta : k) • (A * B * E)
  + (7 / 512 * beta : k) • (A * C * D)
  + (49 / 1024 * beta : k) • (B ^ 2 * D)
  + (7 / 128 * beta : k) • (B * C ^ 2)
  - (7 / 64 * beta : k) • (C * F)
  - (7 / 64 * beta : k) • (D * E)
  + (3 / 64 * gamma : k) • (A * B * D)
  + (3 / 32 * gamma : k) • (B ^ 2 * C)
  - (3 / 32 * gamma : k) • (B * F)
  - (3 / 16 * gamma : k) • (C * E)
  - (3 / 32 * gamma : k) • D ^ 2
  - (5 / 1024 * delta : k) • (A ^ 2 * D)
  + (5 / 128 * delta : k) • (A * B * C)
  + (5 / 128 * delta : k) • B ^ 3
  - (5 / 64 * delta : k) • (A * F)
  - (5 / 32 * delta : k) • (B * E)
  - (15 / 64 * delta : k) • (C * D)
  + (1 / 32 * epsilon : k) • (A * B ^ 2)
  - (3 / 16 * epsilon : k) • (B * D)
  - (1 / 8 * epsilon : k) • C ^ 2
  + (1 / 2 * epsilon : k) • G
  - (3 / 64 * zeta : k) • (A * D)
  - (3 / 16 * zeta : k) • (B * C)
  + (3 / 8 * zeta : k) • F
  - (1 / 16 * eta : k) • B ^ 2
  + (1 / 4 * eta : k) • E
  + (1 / 8 * theta : k) • D

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceACDEF810 A B C D E F G +
        degreeZeroXiQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceACDEF810, degreeZeroXiQuarticNoACDEF810]
  all_goals module

theorem xiQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (xiQuarticFaceACDEF810 A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) =
      (1 / 128 : k) * xiQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [xiQuarticFaceACDEF810, xiQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_ADF : ((A * D * F)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
  have hcf_ADF : ((A * D * F)).coeff (A.natDegree + D.natDegree + F.natDegree) =
      A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ADF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + D.natDegree + F.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (A.natDegree + D.natDegree + F.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_F2 : (F ^ 2).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (A.natDegree + D.natDegree + F.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_ADF, hcf_C2E, hcf_CD2, hcf_F2]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 3 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

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

set_option maxHeartbeats 16000000 in
def omicronQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 2 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  - (5 / 128 : k) • (A * E * F)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoACDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * D * G)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  + (5 / 16 : k) • (F * G)
  + (135 / 33554432 * l : k) • A ^ 7
  + (225 / 2097152 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (81 / 262144 * l : k) • (A ^ 4 * E)
  - (9 / 65536 * l : k) • (A ^ 3 * B * D)
  + (99 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  - (45 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (189 / 65536 * l : k) • (A * B ^ 4)
  + (9 / 8192 * l : k) • (A ^ 3 * G)
  - (9 / 4096 * l : k) • (A ^ 2 * B * F)
  + (27 / 8192 * l : k) • (A ^ 2 * C * E)
  + (45 / 4096 * l : k) • (A * B ^ 2 * E)
  + (99 / 4096 * l : k) • (A * B * C * D)
  + (9 / 8192 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 512 * l : k) • (A * C * G)
  - (9 / 256 * l : k) • (A * D * F)
  - (27 / 1024 * l : k) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)
  - (45 / 512 * l : k) • (B * D * E)
  - (45 / 1024 * l : k) • (C ^ 2 * E)
  - (27 / 512 * l : k) • (C * D ^ 2)
  + (9 / 64 * l : k) • (E * G)
  + (9 / 128 * l : k) • F ^ 2
  + (35 / 2097152 * beta : k) • A ^ 6
  + (49 / 131072 * beta : k) • (A ^ 4 * C)
  - (35 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 4096 * beta : k) • (A ^ 2 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)
  - (91 / 8192 * beta : k) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (7 / 512 * beta : k) • (A * C * E)
  + (7 / 512 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2
  + (3 / 2048 * gamma : k) • (A ^ 2 * B * C)
  - (9 / 1024 * gamma : k) • (A * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 2 * F)
  + (3 / 128 * gamma : k) • (A * B * E)
  + (3 / 128 * gamma : k) • (A * C * D)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)
  + (9 / 131072 * delta : k) • A ^ 5
  + (5 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 4096 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 128 * delta : k) • (A * B * D)
  + (5 / 512 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2
  - (1 / 256 * epsilon : k) • (A ^ 2 * D)
  + (1 / 32 * epsilon : k) • (A * B * C)
  + (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 16 * epsilon : k) • (A * F)
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  + (9 / 32768 * zeta : k) • A ^ 4
  + (3 / 1024 * zeta : k) • (A ^ 2 * C)
  + (9 / 512 * zeta : k) • (A * B ^ 2)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G
  - (1 / 512 * eta : k) • (A ^ 2 * B)
  - (1 / 32 * eta : k) • (A * D)
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (1 / 1024 * theta : k) • A ^ 3
  + (1 / 64 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceACDEF810 A B C D E F G +
        degreeZeroOmicronQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceACDEF810, degreeZeroOmicronQuarticNoACDEF810]
  all_goals module

theorem omicronQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (omicronQuarticFaceACDEF810 A B C D E F G).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      (1 / 2048 : k) * omicronQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [omicronQuarticFaceACDEF810, omicronQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2CF : ((A ^ 2 * C * F)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hCne, natDegree_pow]
  have hcf_A2CF : ((A ^ 2 * C * F)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A2CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2DE : ((A ^ 2 * D * E)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DE : ((A ^ 2 * D * E)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AC2D : ((A * C ^ 2 * D)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_AC2D : ((A * C ^ 2 * D)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AEF : ((A * E * F)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hEne) hFne, natDegree_mul hAne hEne]
    omega
  have hcf_AEF : ((A * E * F)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_AEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2F : ((C ^ 2 * F)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hFne, natDegree_pow]
    omega
  have hcf_C2F : ((C ^ 2 * F)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_C2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDE : ((C * D * E)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hEne, natDegree_mul hCne hDne]
    omega
  have hcf_CDE : ((C * D * E)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_CDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D3 : (D ^ 3).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (2 * A.natDegree + C.natDegree + F.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A2CF, hcf_A2DE, hcf_AC2D, hcf_AEF, hcf_C2F, hcf_CDE, hcf_D3]
  ring

set_option maxHeartbeats 16000000 in
def piQuarticFaceACDEF810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoACDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2
  + (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_ACDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceACDEF810 A B C D E F G +
        degreeZeroPiQuarticNoACDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceACDEF810, degreeZeroPiQuarticNoACDEF810]
  all_goals module

theorem piQuarticFaceACDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (piQuarticFaceACDEF810 A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      (1 / 256 : k) * piQuarticInnerACDEF810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hAC, hAD, hAE, hAF, hBlt, hGlt⟩
  simp only [piQuarticFaceACDEF810, piQuarticInnerACDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_ACD2 : ((A * C * D ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne, natDegree_pow]
  have hcf_ACD2 : ((A * C * D ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ACD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AF2 : ((A * F ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne), natDegree_pow]
    omega
  have hcf_AF2 : ((A * F ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_AF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C4 : (C ^ 4).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C4 : (C ^ 4).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CDF : ((C * D * F)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hFne, natDegree_mul hCne hDne]
    omega
  have hcf_CDF : ((C * D * F)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      C.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CE2 : ((C * E ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_CE2 : ((C * E ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_CE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D2E : ((D ^ 2 * E)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hEne, natDegree_pow]
    omega
  have hcf_D2E : ((D ^ 2 * E)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) =
      D.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_D2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_ACD2, hcf_AF2, hcf_C4, hcf_CDF, hcf_CE2, hcf_D2E]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 5 of `Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBaseScratch`.

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

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceBCDEF810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoBCDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (B * G)
  + (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (5 / 1024 * delta : k) • A ^ 3
  + (5 / 64 * delta : k) • (A * C)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E
  + (1 / 2 * epsilon : k) • D
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_BCDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBCDEF810 A B C D E F G +
        degreeZeroKappaQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceBCDEF810, degreeZeroKappaQuarticNoBCDEF810]
  all_goals module

theorem kappaQuarticFaceBCDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (kappaQuarticFaceBCDEF810 A B C D E F G).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 128 : k) * kappaQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  simp only [kappaQuarticFaceBCDEF810, kappaQuarticInnerBCDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hcf_B2D : ((B ^ 2 * D)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CF : ((C * F)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hCne hFne]
    omega
  have hcf_CF : ((C * F)).coeff (2 * B.natDegree + D.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DE : ((D * E)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (2 * B.natDegree + D.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2D, hcf_BC2, hcf_CF, hcf_DE]
  ring

set_option maxHeartbeats 16000000 in
def muQuarticFaceBCDEF810 (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoBCDEF810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  + (5 / 16 : k) • (C * G)
  - (45 / 262144 * l : k) • (A ^ 4 * B)
  - (9 / 8192 * l : k) • (A ^ 3 * D)
  - (9 / 8192 * l : k) • (A ^ 2 * B * C)
  + (63 / 8192 * l : k) • (A * B ^ 3)
  - (9 / 1024 * l : k) • (A ^ 2 * F)
  - (9 / 512 * l : k) • (A * B * E)
  - (9 / 512 * l : k) • (A * C * D)
  - (63 / 1024 * l : k) • (B ^ 2 * D)
  - (63 / 1024 * l : k) • (B * C ^ 2)
  + (9 / 64 * l : k) • (B * G)
  + (9 / 64 * l : k) • (C * F)
  + (9 / 64 * l : k) • (D * E)
  - (7 / 8192 * beta : k) • (A ^ 3 * B)
  - (7 / 1024 * beta : k) • (A ^ 2 * D)
  + (7 / 512 * beta : k) • (A * B * C)
  + (21 / 1024 * beta : k) • B ^ 3
  - (7 / 64 * beta : k) • (A * F)
  - (7 / 64 * beta : k) • (B * E)
  - (7 / 64 * beta : k) • (C * D)
  + (3 / 128 * gamma : k) • (A * B ^ 2)
  - (3 / 16 * gamma : k) • (B * D)
  - (3 / 32 * gamma : k) • C ^ 2
  + (3 / 4 * gamma : k) • G
  - (5 / 1024 * delta : k) • (A ^ 2 * B)
  - (5 / 64 * delta : k) • (A * D)
  - (15 / 64 * delta : k) • (B * C)
  + (5 / 8 * delta : k) • F
  - (1 / 8 * epsilon : k) • B ^ 2
  + (1 / 2 * epsilon : k) • E
  - (3 / 64 * zeta : k) • (A * B)
  + (3 / 8 * zeta : k) • D
  + (1 / 4 * eta : k) • C
  + (1 / 8 * theta : k) • B

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_BCDEF_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceBCDEF810 A B C D E F G +
        degreeZeroMuQuarticNoBCDEF810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceBCDEF810, degreeZeroMuQuarticNoBCDEF810]
  all_goals module

theorem muQuarticFaceBCDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEF810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (muQuarticFaceBCDEF810 A B C D E F G).coeff (4 * B.natDegree) =
      (1 / 2048 : k) * muQuarticInnerBCDEF810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hBC, hBD, hBE, hBF, hAlt, hGlt⟩
  simp only [muQuarticFaceBCDEF810, muQuarticInnerBCDEF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4 : (B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
  have hcf_B4 : (B ^ 4).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD : ((B * C * D)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    omega
  have hcf_BCD : ((B * C * D)).coeff (4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3 : (C ^ 3).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (4 * B.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_DF : ((D * F)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (4 * B.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (4 * B.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_B4, hcf_B2E, hcf_BCD, hcf_C3, hcf_DF, hcf_E2]
  ring

end QuarticKills810

end Max11DegreeRoutes
