import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 0 of `Grok810ScaleZeroQuarticMultiKills4Scratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills4Scratch`; statements are byte-identical.
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

def kappaQuarticInnerABDEF810 (a b d e f : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + 160 * d * e

def muQuarticInnerABDEF810 (a b d e f : k) : k :=
  (-160 : k) * a * b * f + (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + (-240 : k) * b ^ 2 * e + 640 * d * f + 320 * e ^ 2

def nuQuarticInnerABDEF810 (a b d e f : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + (-160 : k) * a * d * e + (-480 : k) * b ^ 2 * f + (-480 : k) * b * d ^ 2 + 1280 * e * f

def xiQuarticInnerABDEF810 (a b d e f : k) : k :=
  (-15 : k) * a * b ^ 4 + 60 * a * b ^ 2 * e + (-160 : k) * a * d * f + 110 * b ^ 3 * d + (-400 : k) * b * d * e + 320 * f ^ 2

def omicronQuarticInnerABDEF810 (a b d e f : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + (-160 : k) * a ^ 2 * d * e + 1600 * a * b ^ 2 * f + 2240 * a * b * d ^ 2 + (-2560 : k) * a * e * f + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + (-10240 : k) * b * d * f + (-5120 : k) * b * e ^ 2 + (-2560 : k) * d ^ 3

def piQuarticInnerABDEF810 (a b d e f : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + 1280 * a * b * d * e + (-1280 : k) * a * f ^ 2 + 800 * b ^ 3 * f + 1440 * b ^ 2 * d ^ 2 + (-3840 : k) * b * e * f + (-2560 : k) * d ^ 2 * e

def primitiveQuarticInnerABDEF810 (a b d e f : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + (-160 : k) * a ^ 3 * d * e + (-160 : k) * a ^ 2 * b ^ 2 * f + (-800 : k) * a ^ 2 * b * d ^ 2 + (-1280 : k) * a ^ 2 * e * f + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + 10240 * a * b * d * f + 5120 * a * b * e ^ 2 + 2560 * a * d ^ 3 + (-4000 : k) * b ^ 4 * d + 21760 * b ^ 2 * d * e + (-20480 : k) * b * f ^ 2 + (-20480 : k) * d ^ 2 * f + (-20480 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_ABDEF_identity
    (a b d e f : k) :
    ((-927151 / 2536362496 : k) * a ^ 5 * b + (-3997141 / 10145449984 : k) * a ^ 4 * d + (-111523400539 / 4869815992320 : k) * a ^ 3 * f + (-1048432078031 / 19479263969280 : k) * a ^ 2 * b ^ 3 + (147487636877 / 811635998720 : k) * a ^ 2 * b * e + (98482457137 / 162327199744 : k) * a * b ^ 2 * d + (-82641253833 / 101454499840 : k) * a * d * e + (-201676030359 / 202908999680 : k) * b ^ 2 * f + (-293951484757 / 304363499520 : k) * b * d ^ 2 + (32197701499 / 19022718720 : k) * e * f) * kappaQuarticInnerABDEF810 a b d e f +
      ((-6490057 / 7609087488 : k) * a ^ 3 * b ^ 2 + (-3085375 / 475567968 : k) * a ^ 2 * b * d + (6302437453 / 76090874880 : k) * a * b * f + (3804783 / 317045312 : k) * a * d ^ 2 + (21 / 81920 : k) * b ^ 4 + (-41 / 10240 : k) * b ^ 2 * e + (-1356487373 / 38045437440 : k) * d * f + (1 / 320 : k) * e ^ 2) * muQuarticInnerABDEF810 a b d e f +
      ((-927151 / 3804543744 : k) * a ^ 4 * b + (-96179 / 5072724992 : k) * a ^ 3 * d + (-83456469437 / 4869815992320 : k) * a ^ 2 * f + (-88978591727 / 1217453998080 : k) * a * b * e + (93207608691 / 811635998720 : k) * b ^ 2 * d + (-25813450089 / 101454499840 : k) * d * e) * nuQuarticInnerABDEF810 a b d e f +
      ((-23854907 / 1902271872 : k) * a ^ 2 * b ^ 2 + (-927151 / 158522656 : k) * a ^ 2 * e + (4223011327 / 30436349952 : k) * a * b * d + (-15282354047 / 76090874880 : k) * b * f + (-657093637 / 5072724992 : k) * d ^ 2) * xiQuarticInnerABDEF810 a b d e f +
      ((-927151 / 7609087488 : k) * a ^ 3 * b + (-3804783 / 10145449984 : k) * a ^ 2 * d + (2945305359 / 324654399488 : k) * a * f + (7 / 262144 : k) * b ^ 3 + (-13 / 32768 : k) * b * e) * omicronQuarticInnerABDEF810 a b d e f +
      ((947679403 / 202908999680 : k) * a * b ^ 2 + (-665909 / 19815332 : k) * a * e + (607275101 / 76090874880 : k) * b * d) * piQuarticInnerABDEF810 a b d e f +
      ((-15282354047 / 4869815992320 : k) * f) * primitiveQuarticInnerABDEF810 a b d e f =
      e ^ 4 := by
  simp only [kappaQuarticInnerABDEF810, muQuarticInnerABDEF810, nuQuarticInnerABDEF810, xiQuarticInnerABDEF810, omicronQuarticInnerABDEF810, piQuarticInnerABDEF810, primitiveQuarticInnerABDEF810]
  ring

end QuarticKills810

end Max11DegreeRoutes
