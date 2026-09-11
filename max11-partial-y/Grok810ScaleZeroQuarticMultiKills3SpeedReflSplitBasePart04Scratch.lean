import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 4 of `Grok810ScaleZeroQuarticMultiKills3SpeedReflSplitBaseScratch`.

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

def kappaQuarticInnerABCDF810 (a b c d f : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + (-60 : k) * b * c ^ 2 + 160 * c * f

def muQuarticInnerABCDF810 (a b c d f : k) : k :=
  60 * a * b ^ 2 * c + (-160 : k) * a * b * f + (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * d * f

def nuQuarticInnerABCDF810 (a b c d f : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + 60 * a * b * c ^ 2 + (-160 : k) * a * c * f + 280 * b ^ 3 * c + (-480 : k) * b ^ 2 * f + (-480 : k) * b * d ^ 2 + (-480 : k) * c ^ 2 * d

def xiQuarticInnerABCDF810 (a b c d f : k) : k :=
  (-15 : k) * a * b ^ 4 + 120 * a * b * c * d + (-160 : k) * a * d * f + 110 * b ^ 3 * d + 180 * b ^ 2 * c ^ 2 + (-400 : k) * b * c * f + (-240 : k) * c * d ^ 2 + 320 * f ^ 2

def omicronQuarticInnerABCDF810 (a b c d f : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * c * f + (-1120 : k) * a * b ^ 3 * c + 1600 * a * b ^ 2 * f + 2240 * a * b * d ^ 2 + 960 * a * c ^ 2 * d + (-336 : k) * b ^ 5 + 8640 * b ^ 2 * c * d + 2880 * b * c ^ 3 + (-10240 : k) * b * d * f + (-5120 : k) * c ^ 2 * f + (-2560 : k) * d ^ 3

def piQuarticInnerABCDF810 (a b c d f : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + (-360 : k) * a * b ^ 2 * c ^ 2 + 640 * a * b * c * f + 640 * a * c * d ^ 2 + (-1280 : k) * a * f ^ 2 + (-560 : k) * b ^ 4 * c + 800 * b ^ 3 * f + 1440 * b ^ 2 * d ^ 2 + 2880 * b * c ^ 2 * d + 240 * c ^ 4 + (-3840 : k) * c * d * f

def primitiveQuarticInnerABCDF810 (a b c d f : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * c * f + 120 * a ^ 2 * b ^ 3 * c + (-160 : k) * a ^ 2 * b ^ 2 * f + (-800 : k) * a ^ 2 * b * d ^ 2 + 480 * a ^ 2 * c ^ 2 * d + 520 * a * b ^ 5 + (-8640 : k) * a * b ^ 2 * c * d + (-960 : k) * a * b * c ^ 3 + 10240 * a * b * d * f + 2560 * a * d ^ 3 + (-4000 : k) * b ^ 4 * d + (-8480 : k) * b ^ 3 * c ^ 2 + 21760 * b ^ 2 * c * f + 23040 * b * c * d ^ 2 + (-20480 : k) * b * f ^ 2 + 7680 * c ^ 3 * d + (-20480 : k) * d ^ 2 * f

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABCDF_identity
    (a b c d f : k) :
    ((-57835347733273 / 769924729692505600 : k) * a ^ 4 * b ^ 2 + (-1563129768047897 / 2309774189077516800 : k) * a ^ 3 * b * d + (5382943361775401 / 4619548378155033600 : k) * a ^ 3 * c ^ 2 + (-11265744504038223 / 3079698918770022400 : k) * a ^ 2 * b ^ 2 * c + (2673074832903691 / 2309774189077516800 : k) * a ^ 2 * b * f + (664495135134367 / 461954837815503360 : k) * a ^ 2 * d ^ 2 + (-192944225348059 / 3695638702524026880 : k) * a * b ^ 4 + (-2087399597233699 / 288721773634689600 : k) * a * b * c * d + (759562920144467 / 76992472969250560 : k) * a * c ^ 3 + (21072748409921 / 1244490403597800 : k) * a * d * f + (307894897523789 / 38496236484625280 : k) * b ^ 3 * d + (-771185997109597 / 14436088681734480 : k) * b ^ 2 * c ^ 2 + (3698186891543377 / 28872177363468960 : k) * b * c * f + (1499080998952363 / 144360886817344800 : k) * c * d ^ 2 + (-52826963476427 / 6015036950722700 : k) * f ^ 2) * kappaQuarticInnerABCDF810 a b c d f +
      ((161106438453 / 3007518475361350 : k) * a ^ 2 * c * d + (-6444467494568867 / 769924729692505600 : k) * a * b ^ 2 * d + (-84040131383607 / 48120295605781600 : k) * a * b * c ^ 2 + (32524357404553 / 12030073901445400 : k) * a * c * f + (-54781736524703029 / 2309774189077516800 : k) * b ^ 3 * c + (8588326696245347 / 192481182423126400 : k) * b ^ 2 * f + (1353935614171647 / 192481182423126400 : k) * b * d ^ 2 + (4821746681135979 / 192481182423126400 : k) * c ^ 2 * d) * muQuarticInnerABCDF810 a b c d f +
      ((-19887073567469 / 384962364846252800 : k) * a ^ 3 * b ^ 2 + (-526295789125267 / 1154887094538758400 : k) * a ^ 2 * b * d + (1056111247914221 / 1539849459385011200 : k) * a ^ 2 * c ^ 2 + (-4925960474308633 / 1154887094538758400 : k) * a * b * f + (-190044737339509 / 144360886817344800 : k) * a * d ^ 2 + (12873838671929833 / 18478193512620134400 : k) * b ^ 4 + (-182130855907119 / 96240591211563200 : k) * b * c * d + (1973066072711989 / 1154887094538758400 : k) * c ^ 3 + (62603292110023 / 36090221704336200 : k) * d * f) * nuQuarticInnerABCDF810 a b c d f +
      ((161106438453 / 6015036950722700 : k) * a ^ 2 * b * c + (-161106438453 / 3007518475361350 : k) * a ^ 2 * f + (45090659603887 / 24060147802890800 : k) * a * c * d + (182431231317461 / 24060147802890800 : k) * b ^ 2 * d + (21844447487906 / 4511277713042025 : k) * b * c ^ 2 + (52826963476427 / 12030073901445400 : k) * c * f) * xiQuarticInnerABCDF810 a b c d f +
      ((-3612240119667 / 153984945938501120 : k) * a ^ 2 * b ^ 2 + (-48471016205213 / 153984945938501120 : k) * a * b * d + (195900231172481 / 923909675631006720 : k) * a * c ^ 2 + (-880950041719171 / 615939783754004480 : k) * b ^ 2 * c + (461305967175219 / 153984945938501120 : k) * b * f + (-1 / 2560 : k) * d ^ 2) * omicronQuarticInnerABCDF810 a b c d f +
      ((161106438453 / 24060147802890800 : k) * a ^ 2 * d + (-53702146151 / 3007518475361350 : k) * a * b * c + (-161106438453 / 12030073901445400 : k) * a * f + (-21236867397673 / 76992472969250560 : k) * b ^ 3 + (154531575430553 / 48120295605781600 : k) * c * d) * piQuarticInnerABCDF810 a b c d f +
      ((1235108462170333 / 4619548378155033600 : k) * c ^ 2) * primitiveQuarticInnerABCDF810 a b c d f =
      d ^ 5 := by
  simp only [kappaQuarticInnerABCDF810, muQuarticInnerABCDF810, nuQuarticInnerABCDF810, xiQuarticInnerABCDF810, omicronQuarticInnerABCDF810, piQuarticInnerABCDF810, primitiveQuarticInnerABCDF810]
  ring

end QuarticKills810

end Max11DegreeRoutes
