import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 0 of `Grok810ScaleZeroQuarticMultiKills2SpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerBCDE810 (b c d e : k) : k :=
  (-15 : k) * b ^ 2 * d + (-15 : k) * b * c ^ 2 + 40 * d * e

def muQuarticInnerBCDE810 (b c d e : k) : k :=
  35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 320 * e ^ 2

def nuQuarticInnerBCDE810 (b c d e : k) : k :=
  35 * b ^ 3 * c + (-120 : k) * b * c * e + (-60 : k) * b * d ^ 2 + (-60 : k) * c ^ 2 * d

def xiQuarticInnerBCDE810 (b c d e : k) : k :=
  55 * b ^ 3 * d + 90 * b ^ 2 * c ^ 2 + (-200 : k) * b * d * e + (-120 : k) * c ^ 2 * e + (-120 : k) * c * d ^ 2

def omicronQuarticInnerBCDE810 (b c d e : k) : k :=
  (-21 : k) * b ^ 5 + 160 * b ^ 3 * e + 540 * b ^ 2 * c * d + 180 * b * c ^ 3 + (-320 : k) * b * e ^ 2 + (-800 : k) * c * d * e + (-160 : k) * d ^ 3

def piQuarticInnerBCDE810 (b c d e : k) : k :=
  (-35 : k) * b ^ 4 * c + 180 * b ^ 2 * c * e + 90 * b ^ 2 * d ^ 2 + 180 * b * c ^ 2 * d + 15 * c ^ 4 + (-160 : k) * c * e ^ 2 + (-160 : k) * d ^ 2 * e

def primitiveQuarticInnerBCDE810 (b c d e : k) : k :=
  (-125 : k) * b ^ 4 * d + (-265 : k) * b ^ 3 * c ^ 2 + 680 * b ^ 2 * d * e + 720 * b * c ^ 2 * e + 720 * b * c * d ^ 2 + 240 * c ^ 3 * d + (-640 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_BCDE_identity
    (b c d e : k) :
    ((-127253 / 9400320 : k) * b ^ 3 * c + (-1287 / 43520 : k) * b * c * e + (83 / 2304 : k) * b * d ^ 2 + (-9487 / 57600 : k) * c ^ 2 * d) * kappaQuarticInnerBCDE810 b c d e +
      ((21 / 81920 : k) * b ^ 4 + (-41 / 10240 : k) * b ^ 2 * e + (-793 / 174080 : k) * b * c * d + (-203 / 51200 : k) * c ^ 3 + (1 / 320 : k) * e ^ 2) * muQuarticInnerBCDE810 b c d e +
      ((-73409 / 7833600 : k) * b * c ^ 2 + (7 / 1728 : k) * d * e) * nuQuarticInnerBCDE810 b c d e +
      ((-1855 / 313344 : k) * b ^ 2 * c + (179 / 11520 : k) * c * e + (17 / 1536 : k) * d ^ 2) * xiQuarticInnerBCDE810 b c d e +
      ((7 / 16384 : k) * b ^ 3 + (-13 / 2048 : k) * b * e + (-17 / 2048 : k) * c * d) * omicronQuarticInnerBCDE810 b c d e +
      ((-203 / 9600 : k) * c ^ 2) * piQuarticInnerBCDE810 b c d e =
      e ^ 4 := by
  simp only [kappaQuarticInnerBCDE810, muQuarticInnerBCDE810, nuQuarticInnerBCDE810, xiQuarticInnerBCDE810, omicronQuarticInnerBCDE810, piQuarticInnerBCDE810, primitiveQuarticInnerBCDE810]
  ring

end QuarticKills810

end Max11DegreeRoutes
