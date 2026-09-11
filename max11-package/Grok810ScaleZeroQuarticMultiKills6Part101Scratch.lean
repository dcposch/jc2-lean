import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch
import Grok810ScaleZeroQuarticDefsScratch

/-! # Part 0 of `Grok810ScaleZeroQuarticMultiKills6Scratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills6Scratch`; statements are byte-identical.
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

def kappaQuarticInnerABCDEG810 (a b c d e g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + (-60 : k) * b * c ^ 2 + 160 * b * g + 160 * d * e

def muQuarticInnerABCDEG810 (a b c d e g : k) : k :=
  60 * a * b ^ 2 * c + (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * c * g + 320 * e ^ 2

def nuQuarticInnerABCDEG810 (a b c d e g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + 60 * a * b * c ^ 2 + (-160 : k) * a * b * g + (-160 : k) * a * d * e + 280 * b ^ 3 * c + (-960 : k) * b * c * e + (-480 : k) * b * d ^ 2 + (-480 : k) * c ^ 2 * d + 1280 * d * g

def xiQuarticInnerABCDEG810 (a b c d e g : k) : k :=
  (-15 : k) * a * b ^ 4 + 60 * a * b ^ 2 * e + 120 * a * b * c * d + 110 * b ^ 3 * d + 180 * b ^ 2 * c ^ 2 + (-160 : k) * b ^ 2 * g + (-400 : k) * b * d * e + (-240 : k) * c ^ 2 * e + (-240 : k) * c * d ^ 2 + 640 * e * g

def omicronQuarticInnerABCDEG810 (a b c d e g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * b * g + (-160 : k) * a ^ 2 * d * e + (-1120 : k) * a * b ^ 3 * c + 1920 * a * b * c * e + 2240 * a * b * d ^ 2 + 960 * a * c ^ 2 * d + (-2560 : k) * a * d * g + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + 8640 * b ^ 2 * c * d + 2880 * b * c ^ 3 + (-7680 : k) * b * c * g + (-5120 : k) * b * e ^ 2 + (-12800 : k) * c * d * e + (-2560 : k) * d ^ 3

def piQuarticInnerABCDEG810 (a b c d e g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + (-360 : k) * a * b ^ 2 * c ^ 2 + 320 * a * b ^ 2 * g + 1280 * a * b * d * e + 640 * a * c * d ^ 2 + (-560 : k) * b ^ 4 * c + 2880 * b ^ 2 * c * e + 1440 * b ^ 2 * d ^ 2 + 2880 * b * c ^ 2 * d + (-2560 : k) * b * d * g + 240 * c ^ 4 + (-1280 : k) * c ^ 2 * g + (-2560 : k) * c * e ^ 2 + (-2560 : k) * d ^ 2 * e + 5120 * g ^ 2

def primitiveQuarticInnerABCDEG810 (a b c d e g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * b * g + (-160 : k) * a ^ 3 * d * e + 120 * a ^ 2 * b ^ 3 * c + 960 * a ^ 2 * b * c * e + (-800 : k) * a ^ 2 * b * d ^ 2 + 480 * a ^ 2 * c ^ 2 * d + (-1280 : k) * a ^ 2 * d * g + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + (-8640 : k) * a * b ^ 2 * c * d + (-960 : k) * a * b * c ^ 3 + 2560 * a * b * c * g + 5120 * a * b * e ^ 2 + 7680 * a * c * d * e + 2560 * a * d ^ 3 + (-4000 : k) * b ^ 4 * d + (-8480 : k) * b ^ 3 * c ^ 2 + 3840 * b ^ 3 * g + 21760 * b ^ 2 * d * e + 23040 * b * c ^ 2 * e + 23040 * b * c * d ^ 2 + (-20480 : k) * b * e * g + 7680 * c ^ 3 * d + (-20480 : k) * c * d * g + (-20480 : k) * d * e ^ 2

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABCDEG_identity
    (a b c d e g : k) :
    ((-17672695029 / 95588109489152 : k) * a ^ 5 * c * d + (-604163757 / 27310888425472 : k) * a ^ 4 * b * c ^ 2 + (30019 / 1200513792 : k) * a ^ 4 * b * g + (12066271969 / 23897027372288 : k) * a ^ 4 * d * e + (-9069026859493 / 901259318040576000 : k) * a ^ 3 * b ^ 3 * c + (1101605092183 / 3413861053184000 : k) * a ^ 3 * b * c * e + (-48602314590521 / 394300951642752000 : k) * a ^ 3 * b * d ^ 2 + (-645301141427 / 170693052659200 : k) * a ^ 3 * c ^ 2 * d + (10220631313229 / 4480692632304000 : k) * a ^ 3 * d * g + (-1759486679927 / 22531482951014400 : k) * a ^ 2 * b ^ 5 + (1759486679927 / 3285841263689600 : k) * a ^ 2 * b ^ 3 * e + (-77469005293721 / 525734602190336000 : k) * a ^ 2 * b ^ 2 * c * d + (-459143287257503 / 78860190328550400 : k) * a ^ 2 * b * c ^ 3 + (84376133728691 / 7041088422192000 : k) * a ^ 2 * b * c * g + (-263314853062361 / 98575237910688000 : k) * a ^ 2 * b * e ^ 2 + (375385654640681 / 24643809477672000 : k) * a ^ 2 * c * d * e + (-40095429863627 / 6917560555136000 : k) * a ^ 2 * d ^ 3 + (-4966395462896383 / 901259318040576000 : k) * a * b ^ 4 * d + (-520075775318993 / 225314829510144000 : k) * a * b ^ 3 * c ^ 2 + (85314470393953 / 13143365054758400 : k) * a * b ^ 3 * g + (16192429496094539 / 394300951642752000 : k) * a * b ^ 2 * d * e + (64543962514721 / 1642920631844800 : k) * a * b * c ^ 2 * e + (-398788843965307 / 8961385264608000 : k) * a * b * c * d ^ 2 + (-187276975670713 / 4107301579612000 : k) * a * b * e * g + (-1603347820402137 / 131433650547584000 : k) * a * c ^ 3 * d + (1087642621384183 / 49287618955344000 : k) * a * c * d * g + (-387003870745137 / 32858412636896000 : k) * a * d * e ^ 2 + (-839263404706879 / 112657414755072000 : k) * b ^ 5 * c + (1041637475675851 / 12321904738836000 : k) * b ^ 3 * c * e + (22260810939739 / 716910821168640 : k) * b ^ 3 * d ^ 2 + (-8170933517997911 / 65716825273792000 : k) * b ^ 2 * c ^ 2 * d + (-78395108625511 / 1173514737032000 : k) * b ^ 2 * d * g + (-6713733855925793 / 98575237910688000 : k) * b * c ^ 4 + (1430518783820503 / 12321904738836000 : k) * b * c ^ 2 * g + (-104687841831847 / 586757368516000 : k) * b * c * e ^ 2 + (-330970781020109 / 1760272105548000 : k) * b * d ^ 2 * e + (120076 / 117237675 : k) * b * g ^ 2 + (990775482708103 / 6160952369418000 : k) * c ^ 2 * d * e + (39727642863481 / 1232190473883600 : k) * c * d ^ 3 + (694145830414847 / 1540238092354500 : k) * d * e * g) * kappaQuarticInnerABCDEG810 a b c d e g +
      ((-43910447630897 / 32858412636896000 : k) * a * b ^ 2 * c * e + (750992044025521 / 788601903285504000 : k) * a * b ^ 2 * d ^ 2 + (433776350207 / 597425684307200 : k) * a * b * c ^ 2 * d + (-50317900293209 / 12321904738836000 : k) * a * b * d * g + (-48602314590521 / 8214603159224000 : k) * a * d ^ 2 * e + (-1759486679927 / 2347029474064000 : k) * b ^ 6 + (1759486679927 / 308047618470900 : k) * b ^ 4 * e + (817290516522611 / 262867301095168000 : k) * b ^ 3 * c * d + (-224128894162361 / 65716825273792000 : k) * b ^ 2 * c ^ 3 + (216363810465641 / 24643809477672000 : k) * b ^ 2 * c * g + (-1759486679927 / 154023809235450 : k) * b ^ 2 * e ^ 2 + (575133182054297 / 32858412636896000 : k) * b * c * d * e + (-39089934288281 / 197150475821376000 : k) * b * d ^ 3 + (85505667 / 386024584550 : k) * c ^ 3 * e + (501404177246829 / 65716825273792000 : k) * c ^ 2 * d ^ 2 + (-114007556 / 193012292275 : k) * c * e * g + (-216683393845711 / 8214603159224000 : k) * d ^ 2 * g) * muQuarticInnerABCDEG810 a b c d e g +
      ((-53018085087 / 477940547445760 : k) * a ^ 4 * c * d + (-1812491271 / 136554442127360 : k) * a ^ 3 * b * c ^ 2 + (30019 / 2000856320 : k) * a ^ 3 * b * g + (36198815907 / 119485136861440 : k) * a ^ 3 * d * e + (51902711702253 / 262867301095168000 : k) * a ^ 2 * b * c * e + (-2151807631077 / 1194851368614400 : k) * a ^ 2 * c ^ 2 * d + (2041526890369 / 1493564210768000 : k) * a ^ 2 * d * g + (-438507495113669 / 105146920438067200 : k) * a * b * c ^ 3 + (1710948899186353 / 197150475821376000 : k) * a * b * c * g + (-64311795288427 / 32858412636896000 : k) * a * b * e ^ 2 + (74692106534901 / 5974256843072000 : k) * a * c * d * e + (-64330676187919 / 26286730109516800 : k) * a * d ^ 3 + (-1395025868772607 / 901259318040576000 : k) * b ^ 4 * d + (-601392592175711 / 225314829510144000 : k) * b ^ 3 * c ^ 2 + (259413971171987 / 39430095164275200 : k) * b ^ 3 * g + (6697458059724203 / 394300951642752000 : k) * b ^ 2 * d * e + (3386993068727 / 187762357925120 : k) * b * c ^ 2 * e + (-217835657708257 / 17922770529216000 : k) * b * c * d ^ 2 + (-569718563353339 / 12321904738836000 : k) * b * e * g + (-1044667859469 / 150209886340096 : k) * c ^ 3 * d + (850731320408861 / 49287618955344000 : k) * c * d * g + (-21828275650511 / 597425684307200 : k) * d * e ^ 2) * nuQuarticInnerABCDEG810 a b c d e g +
      ((28501889 / 393043213360 : k) * a * b * d * e + (680127990671 / 205365078980600 : k) * a * c * d ^ 2 + (1284119743 / 4323475346960 : k) * b ^ 2 * c * e + (44794759672709 / 24643809477672000 : k) * b ^ 2 * d ^ 2 + (-2273692215499 / 513412697451500 : k) * b * c ^ 2 * d + (-13834478299 / 20266290688875 : k) * b * d * g + (-28501889 / 386024584550 : k) * c ^ 4 + (114007556 / 193012292275 : k) * c ^ 2 * g + (57003778 / 193012292275 : k) * c * e ^ 2 + (-2987936060537 / 256706348725750 : k) * d ^ 2 * e) * xiQuarticInnerABCDEG810 a b c d e g +
      ((-17672695029 / 477940547445760 : k) * a ^ 3 * c * d + (-604163757 / 136554442127360 : k) * a ^ 2 * b * c ^ 2 + (30019 / 6002568960 : k) * a ^ 2 * b * g + (12066271969 / 119485136861440 : k) * a ^ 2 * d * e + (3796366261283 / 52573460219033600 : k) * a * b * c * e + (-19736602933 / 47794054744576 : k) * a * c ^ 2 * d + (405706005797 / 896138526460800 : k) * a * d * g + (-1759486679927 / 22531482951014400 : k) * b ^ 5 + (1759486679927 / 3285841263689600 : k) * b ^ 3 * e + (-126634124853 / 221361937764352 : k) * b ^ 2 * c * d + (-95278175754313 / 63088152262840320 : k) * b * c ^ 3 + (41335486656813 / 13143365054758400 : k) * b * c * g + (-1759486679927 / 2464380947767200 : k) * b * e ^ 2 + (166852971808343 / 39430095164275200 : k) * c * d * e + (-1 / 2560 : k) * d ^ 3) * omicronQuarticInnerABCDEG810 a b c d e g +
      ((67919880489 / 293378684258000 : k) * a * b * c * d + (167669417243 / 2347029474064000 : k) * b ^ 3 * d + (3396585981 / 234702947406400 : k) * b ^ 2 * c ^ 2 + (-30019 / 937901400 : k) * b ^ 2 * g + (-1284508581201 / 2053650789806000 : k) * b * d * e + (5592190551 / 6755430229625 : k) * c * d ^ 2) * piQuarticInnerABCDEG810 a b c d e g +
      ((-17672695029 / 477940547445760 : k) * a ^ 2 * c * d + (-604163757 / 136554442127360 : k) * a * b * c ^ 2 + (30019 / 6002568960 : k) * a * b * g + (12066271969 / 119485136861440 : k) * a * d * e + (-9069026859493 / 901259318040576000 : k) * b ^ 3 * c + (13939049089423 / 262867301095168000 : k) * b * c * e + (-48602314590521 / 394300951642752000 : k) * b * d ^ 2 + (-65438526181 / 170693052659200 : k) * c ^ 2 * d + (295360087591 / 640098947472000 : k) * d * g) * primitiveQuarticInnerABCDEG810 a b c d e g =
      d ^ 6 := by
  simp only [kappaQuarticInnerABCDEG810, muQuarticInnerABCDEG810, nuQuarticInnerABCDEG810, xiQuarticInnerABCDEG810, omicronQuarticInnerABCDEG810, piQuarticInnerABCDEG810, primitiveQuarticInnerABCDEG810]
  ring

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 1 of `Grok810ScaleZeroQuarticMultiKills6Scratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills6Scratch`; statements are byte-identical.
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
def kappaQuarticFaceABCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)
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
theorem degreeZeroKappaQuartic810_eq_ABCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABCDEG810 A B C D E F G +
        degreeZeroKappaQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABCDEG810, degreeZeroKappaQuarticNoABCDEG810]
  all_goals module

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoABCDEG810` (30 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoABCDEG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 16 : k), (63 / 262144 * l : k), (45 / 8192 * l : k),
      (-(9 / 16384 * l) : k), (27 / 1024 * l : k), (-(9 / 512 * l) : k),
      (9 / 1024 * l : k), (-(63 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 128 * l : k),
      (35 / 32768 * beta : k), (21 / 1024 * beta : k), (7 / 1024 * beta : k),
      (7 / 64 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (7 / 8 * beta : k), (-(3 / 16 * gamma) : k), (3 / 4 * gamma : k),
      (5 / 1024 * delta : k), (5 / 64 * delta : k), (-(15 / 128 * delta) : k),
      (5 / 8 * delta : k), (1 / 2 * epsilon : k), (3 / 128 * zeta : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [0, 0, 1, 0, 0, 1, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroKappaQuarticNoABCDEG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoABCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroKappaQuarticNoABCDEG810_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
    Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    mul_one, one_mul, and_true, true_and, natDegree_zero]
  repeat' apply And.intro
  all_goals first
    | (right; right; omega)
    | (left; norm_num; done)
    | (right; left; simp; done)
    | trivial

theorem kappaQuarticFaceABCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceABCDEG810 A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 512 : k) * kappaQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  simp only [kappaQuarticFaceABCDEG810, kappaQuarticInnerABCDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2D : ((B ^ 2 * D)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BG : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    omega
  have hcf_BG : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DE : ((D * E)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_B2D, hcf_BC2, hcf_BG, hcf_DE]
  ring

set_option maxHeartbeats 16000000 in
def muQuarticFaceABCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoABCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * B * F)
  + (5 / 16 : k) • (D * F)
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

end QuarticKills810

end Max11DegreeRoutes
/-! # Part 4 of `Grok810ScaleZeroQuarticMultiKills6Scratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills6Scratch`; statements are byte-identical.
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
def omicronQuarticFaceABCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * D * G)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 64 : k) • (B * E ^ 2)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoABCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 2 * C * F)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  - (5 / 128 : k) • (A * E * F)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (C ^ 2 * F)
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
theorem degreeZeroOmicronQuartic810_eq_ABCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceABCDEG810 A B C D E F G +
        degreeZeroOmicronQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceABCDEG810, degreeZeroOmicronQuarticNoABCDEG810]
  all_goals module

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroOmicronQuarticNoABCDEG810` (84 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronQuarticNoABCDEG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroOmicronQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 2048) : k), (25 / 1024 : k), (-(5 / 128) : k),
      (-(5 / 32) : k), (-(5 / 64) : k), (5 / 16 : k),
      (135 / 33554432 * l : k), (225 / 2097152 * l : k), (-(171 / 4194304 * l) : k),
      (81 / 262144 * l : k), (-(9 / 65536 * l) : k), (99 / 131072 * l : k),
      (-(45 / 131072 * l) : k), (-(189 / 65536 * l) : k), (9 / 8192 * l : k),
      (-(9 / 4096 * l) : k), (27 / 8192 * l : k), (45 / 4096 * l : k),
      (99 / 4096 * l : k), (9 / 8192 * l : k), (189 / 8192 * l : k),
      (567 / 16384 * l : k), (9 / 512 * l : k), (-(9 / 256 * l) : k),
      (-(27 / 1024 * l) : k), (-(9 / 128 * l) : k), (-(45 / 512 * l) : k),
      (-(45 / 1024 * l) : k), (-(27 / 512 * l) : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (35 / 2097152 * beta : k), (49 / 131072 * beta : k),
      (-(35 / 131072 * beta) : k), (7 / 8192 * beta : k), (-(7 / 4096 * beta) : k),
      (21 / 8192 * beta : k), (-(91 / 8192 * beta) : k), (-(189 / 32768 * beta) : k),
      (7 / 512 * beta : k), (7 / 512 * beta : k), (35 / 1024 * beta : k),
      (21 / 256 * beta : k), (7 / 512 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (3 / 2048 * gamma : k), (-(9 / 1024 * gamma) : k),
      (-(3 / 512 * gamma) : k), (3 / 128 * gamma : k), (3 / 128 * gamma : k),
      (9 / 128 * gamma : k), (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (9 / 131072 * delta : k), (5 / 4096 * delta : k),
      (-(5 / 4096 * delta) : k), (5 / 128 * delta : k), (5 / 512 * delta : k),
      (45 / 512 * delta : k), (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k),
      (-(15 / 128 * delta) : k), (-(1 / 256 * epsilon) : k), (1 / 32 * epsilon : k),
      (1 / 32 * epsilon : k), (-(1 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k),
      (-(3 / 16 * epsilon) : k), (9 / 32768 * zeta : k), (3 / 1024 * zeta : k),
      (9 / 512 * zeta : k), (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k),
      (3 / 8 * zeta : k), (-(1 / 512 * eta) : k), (-(1 / 32 * eta) : k),
      (-(3 / 32 * eta) : k), (1 / 4 * eta : k), (1 / 1024 * theta : k),
      (1 / 64 * theta : k), (-(3 / 128 * theta) : k), (1 / 8 * theta : k)]
      [
      [2, 0, 1, 0, 0, 1, 0], [1, 2, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 1], [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0],
      [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0],
      [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0],
      [2, 0, 1, 0, 1, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0],
      [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0], [6, 0, 0, 0, 0, 0, 0],
      [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0],
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0],
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0],
      [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]] := by
  simp only [degreeZeroOmicronQuarticNoABCDEG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoABCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroOmicronQuarticNoABCDEG810_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
    Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    mul_one, one_mul, and_true, true_and, natDegree_zero]
  repeat' apply And.intro
  all_goals first
    | (right; right; omega)
    | (left; norm_num; done)
    | (right; left; simp; done)
    | trivial

theorem omicronQuarticFaceABCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceABCDEG810 A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * omicronQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  simp only [omicronQuarticFaceABCDEG810, omicronQuarticInnerABCDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BC2 : ((A ^ 2 * B * C ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BC2 : ((A ^ 2 * B * C ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BG : ((A ^ 2 * B * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow]
    omega
  have hcf_A2BG : ((A ^ 2 * B * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2BG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2DE : ((A ^ 2 * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DE : ((A ^ 2 * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB3C : ((A * B ^ 3 * C)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3C : ((A * B ^ 3 * C)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_AB3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCE : ((A * B * C * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCE : ((A * B * C * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ABCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABD2 : ((A * B * D ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hDne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABD2 : ((A * B * D ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ABD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AC2D : ((A * C ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_AC2D : ((A * C ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ADG : ((A * D * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
    omega
  have hcf_ADG : ((A * D * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ADG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B5 : (B ^ 5).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CD : ((B ^ 2 * C * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hDne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CD : ((B ^ 2 * C * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_B2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCG : ((B * C * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hGne, natDegree_mul hBne hCne]
    omega
  have hcf_BCG : ((B * C * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BCG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BE2 : ((B * E ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_BE2 : ((B * E ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_BE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDE : ((C * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hEne, natDegree_mul hCne hDne]
    omega
  have hcf_CDE : ((C * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_CDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D3 : (D ^ 3).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (3 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A3B3, hcf_A2B2D, hcf_A2BC2, hcf_A2BG, hcf_A2DE, hcf_AB3C, hcf_ABCE, hcf_ABD2, hcf_AC2D, hcf_ADG, hcf_B5, hcf_B3E, hcf_B2CD, hcf_BC3, hcf_BCG, hcf_BE2, hcf_CDE, hcf_D3]
  ring

set_option maxHeartbeats 16000000 in
def piQuarticFaceABCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoABCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
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

end QuarticKills810

end Max11DegreeRoutes
