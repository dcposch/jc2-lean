import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

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
