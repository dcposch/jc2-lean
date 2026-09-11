import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

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
