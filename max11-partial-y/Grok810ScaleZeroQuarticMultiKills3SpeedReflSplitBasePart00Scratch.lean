import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 0 of `Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerABCDE810 (a b c d e : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + (-60 : k) * b * c ^ 2 + 160 * d * e

def muQuarticInnerABCDE810 (a b c d e : k) : k :=
  60 * a * b ^ 2 * c + (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 320 * e ^ 2

def nuQuarticInnerABCDE810 (a b c d e : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + 60 * a * b * c ^ 2 + (-160 : k) * a * d * e + 280 * b ^ 3 * c + (-960 : k) * b * c * e + (-480 : k) * b * d ^ 2 + (-480 : k) * c ^ 2 * d

def xiQuarticInnerABCDE810 (a b c d e : k) : k :=
  (-15 : k) * a * b ^ 4 + 60 * a * b ^ 2 * e + 120 * a * b * c * d + 110 * b ^ 3 * d + 180 * b ^ 2 * c ^ 2 + (-400 : k) * b * d * e + (-240 : k) * c ^ 2 * e + (-240 : k) * c * d ^ 2

def omicronQuarticInnerABCDE810 (a b c d e : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * d * e + (-1120 : k) * a * b ^ 3 * c + 1920 * a * b * c * e + 2240 * a * b * d ^ 2 + 960 * a * c ^ 2 * d + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + 8640 * b ^ 2 * c * d + 2880 * b * c ^ 3 + (-5120 : k) * b * e ^ 2 + (-12800 : k) * c * d * e + (-2560 : k) * d ^ 3

def piQuarticInnerABCDE810 (a b c d e : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + (-360 : k) * a * b ^ 2 * c ^ 2 + 1280 * a * b * d * e + 640 * a * c * d ^ 2 + (-560 : k) * b ^ 4 * c + 2880 * b ^ 2 * c * e + 1440 * b ^ 2 * d ^ 2 + 2880 * b * c ^ 2 * d + 240 * c ^ 4 + (-2560 : k) * c * e ^ 2 + (-2560 : k) * d ^ 2 * e

def primitiveQuarticInnerABCDE810 (a b c d e : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * d * e + 120 * a ^ 2 * b ^ 3 * c + 960 * a ^ 2 * b * c * e + (-800 : k) * a ^ 2 * b * d ^ 2 + 480 * a ^ 2 * c ^ 2 * d + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + (-8640 : k) * a * b ^ 2 * c * d + (-960 : k) * a * b * c ^ 3 + 5120 * a * b * e ^ 2 + 7680 * a * c * d * e + 2560 * a * d ^ 3 + (-4000 : k) * b ^ 4 * d + (-8480 : k) * b ^ 3 * c ^ 2 + 21760 * b ^ 2 * d * e + 23040 * b * c ^ 2 * e + 23040 * b * c * d ^ 2 + 7680 * c ^ 3 * d + (-20480 : k) * d * e ^ 2

set_option maxHeartbeats 32000000 in
theorem quarticInner_ABCDE_identity
    (a b c d e : k) :
    ((6270151 / 161582657280 : k) * a ^ 4 * b ^ 2 + (57789874409 / 20359414817280 : k) * a ^ 3 * b * d + (-86571733 / 188513100160 : k) * a ^ 3 * c ^ 2 + (313556241017 / 81437659269120 : k) * a ^ 2 * b ^ 2 * c + (-3145842257 / 484747971840 : k) * a ^ 2 * c * e + (-597828070919 / 83288515161600 : k) * a ^ 2 * d ^ 2 + (-60633607724453 / 36646946671104000 : k) * a * b ^ 4 + (-148951577329 / 763478055648000 : k) * a * b ^ 2 * e + (2317541225143 / 42415447536000 : k) * a * b * c * d + (-2122944186521 / 458086833388800 : k) * a * c ^ 3 + (991663014161 / 114521708347200 : k) * a * e ^ 2 + (-112538284651 / 3029674824000 : k) * b ^ 3 * d + (4870242580589 / 76347805564800 : k) * b ^ 2 * c ^ 2 + (660662147951 / 3976448206500 : k) * b * d * e + (-129608330177 / 1060386188400 : k) * c ^ 2 * e + (-86368775771 / 963987444000 : k) * c * d ^ 2) * kappaQuarticInnerABCDE810 a b c d e +
      ((2897251162063 / 305391222259200 : k) * a * b ^ 2 * d + (-34386617 / 28276965024 : k) * a * b * c ^ 2 + (-6270151 / 2524729020 : k) * a * d * e + (88143537314369 / 4580868333888000 : k) * b ^ 3 * c + (-1512302466233 / 27267073416000 : k) * b * c * e + (-676588668883 / 76347805564800 : k) * b * d ^ 2 + (-16273189426643 / 381739027824000 : k) * c ^ 2 * d) * muQuarticInnerABCDE810 a b c d e +
      ((6270151 / 242373985920 : k) * a ^ 3 * b ^ 2 + (18970684423 / 10179707408640 : k) * a ^ 2 * b * d + (-86571733 / 282769650240 : k) * a ^ 2 * c ^ 2 + (-2254384571 / 565539300480 : k) * a * c * e + (-1270143061021 / 229043416694400 : k) * a * d ^ 2 + (6841079407889 / 3331540606464000 : k) * b ^ 4 + (-4255523320633 / 763478055648000 : k) * b ^ 2 * e + (-65693684783 / 14138482512000 : k) * b * c * d + (1250808061399 / 458086833388800 : k) * c ^ 3 + (422834915441 / 114521708347200 : k) * e ^ 2) * nuQuarticInnerABCDE810 a b c d e +
      ((6270151 / 9089024472 : k) * a * b * e + (86571733 / 42415447536 : k) * a * c * d + (-3929701921 / 132548273550 : k) * b ^ 2 * d + (45532903513 / 9543475695600 : k) * b * c ^ 2 + (21506032619 / 265096547100 : k) * d * e) * xiQuarticInnerABCDE810 a b c d e +
      ((6270151 / 484747971840 : k) * a ^ 2 * b ^ 2 + (2205389507 / 2262157201920 : k) * a * b * d + (-86571733 / 565539300480 : k) * a * c ^ 2 + (95497853657 / 81437659269120 : k) * b ^ 2 * c + (-8494588373 / 3393235802880 : k) * c * e + (-1 / 2560 : k) * d ^ 2) * omicronQuarticInnerABCDE810 a b c d e +
      ((-347497313 / 848308950720 : k) * a * b * c + (7190494459 / 4712827504000 : k) * b ^ 3 + (-105315881357 / 31811585652000 : k) * b * e + (-1288470823 / 147275859500 : k) * c * d) * piQuarticInnerABCDE810 a b c d e =
      d ^ 5 := by
  simp only [kappaQuarticInnerABCDE810, muQuarticInnerABCDE810, nuQuarticInnerABCDE810, xiQuarticInnerABCDE810, omicronQuarticInnerABCDE810, piQuarticInnerABCDE810, primitiveQuarticInnerABCDE810]
  ring

end QuarticKills810

end Max11DegreeRoutes
