import Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitBasePart20Scratch

/-! # Part 21 of `Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerABCFG810 (a b c f g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b * c ^ 2 + 160 * b * g + 160 * c * f

def muQuarticInnerABCFG810 (a b c f g : k) : k :=
  60 * a * b ^ 2 * c + (-160 : k) * a * b * f + 35 * b ^ 4 + (-80 : k) * c ^ 3 + 640 * c * g

def nuQuarticInnerABCFG810 (a b c f g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 60 * a * b * c ^ 2 + (-160 : k) * a * b * g + (-160 : k) * a * c * f + 280 * b ^ 3 * c + (-480 : k) * b ^ 2 * f

def xiQuarticInnerABCFG810 (a b c f g : k) : k :=
  (-15 : k) * a * b ^ 4 + 180 * b ^ 2 * c ^ 2 + (-160 : k) * b ^ 2 * g + (-400 : k) * b * c * f + 320 * f ^ 2

def omicronQuarticInnerABCFG810 (a b c f g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * b * g + (-160 : k) * a ^ 2 * c * f + (-1120 : k) * a * b ^ 3 * c + 1600 * a * b ^ 2 * f + (-336 : k) * b ^ 5 + 2880 * b * c ^ 3 + (-7680 : k) * b * c * g + (-5120 : k) * c ^ 2 * f + 20480 * f * g

def piQuarticInnerABCFG810 (a b c f g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-360 : k) * a * b ^ 2 * c ^ 2 + 320 * a * b ^ 2 * g + 640 * a * b * c * f + (-1280 : k) * a * f ^ 2 + (-560 : k) * b ^ 4 * c + 800 * b ^ 3 * f + 240 * c ^ 4 + (-1280 : k) * c ^ 2 * g + 5120 * g ^ 2

def primitiveQuarticInnerABCFG810 (a b c f g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * b * g + (-160 : k) * a ^ 3 * c * f + 120 * a ^ 2 * b ^ 3 * c + (-160 : k) * a ^ 2 * b ^ 2 * f + 520 * a * b ^ 5 + (-960 : k) * a * b * c ^ 3 + 2560 * a * b * c * g + (-20480 : k) * a * f * g + (-8480 : k) * b ^ 3 * c ^ 2 + 3840 * b ^ 3 * g + 21760 * b ^ 2 * c * f + (-20480 : k) * b * f ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_ABCFG_identity
    (a b c f g : k) :
    ((-19 / 17280 : k) * a ^ 3 * b * c + (3 / 320 : k) * a ^ 3 * f + (-612467 / 202936320 : k) * a ^ 2 * b ^ 3 + (477137 / 25367040 : k) * a * b * c ^ 2 + (54337 / 1981800 : k) * a * b * g + (1083493 / 12683520 : k) * a * c * f + (-12611011 / 126835200 : k) * b ^ 3 * c + (1600459 / 7927200 : k) * b ^ 2 * f) * kappaQuarticInnerABCFG810 a b c f g +
      ((1 / 144 : k) * a * b ^ 2 * c + (-23 / 960 : k) * a * b * f + (-9751 / 4227840 : k) * b ^ 4 + (1 / 160 : k) * c ^ 3 + (-1 / 20 : k) * c * g) * muQuarticInnerABCFG810 a b c f g +
      ((-19 / 17280 : k) * a ^ 2 * b * c + (77 / 8640 : k) * a ^ 2 * f + (-21029 / 8455680 : k) * b * c ^ 2 + (113057 / 1981800 : k) * b * g + (784021 / 12683520 : k) * c * f) * nuQuarticInnerABCFG810 a b c f g +
      ((-1 / 1080 : k) * a ^ 2 * b ^ 2 + (89 / 4320 : k) * a * c ^ 2 + (-4 / 135 : k) * a * g + (-1043357 / 126835200 : k) * b ^ 2 * c) * xiQuarticInnerABCFG810 a b c f g +
      ((1 / 2160 : k) * a * f + (-9751 / 40587264 : k) * b ^ 3) * omicronQuarticInnerABCFG810 a b c f g +
      ((1 / 160 : k) * c ^ 2) * piQuarticInnerABCFG810 a b c f g =
      c ^ 6 := by
  simp only [kappaQuarticInnerABCFG810, muQuarticInnerABCFG810, nuQuarticInnerABCFG810, xiQuarticInnerABCFG810, omicronQuarticInnerABCFG810, piQuarticInnerABCFG810, primitiveQuarticInnerABCFG810]
  ring

end QuarticKills810

end Max11DegreeRoutes
