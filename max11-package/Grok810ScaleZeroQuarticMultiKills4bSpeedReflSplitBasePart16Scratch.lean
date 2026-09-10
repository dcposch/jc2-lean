import Grok810ScaleZeroQuarticMultiKills4bSpeedReflSplitBasePart15Scratch

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
