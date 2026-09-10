import Grok810ScaleZeroQuarticMultiKills5Scratch

/-! # Quartic Stage A multi-cone certificates (part 6: 6-letter cones ABCDEG–ABCEFG) -/

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
  simp only [degreeZeroKappaQuarticNoABCDEG810]
  compute_degree
  omega

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

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_ABCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceABCDEG810 A B C D E F G +
        degreeZeroMuQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceABCDEG810, degreeZeroMuQuarticNoABCDEG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoABCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G) :
    (degreeZeroMuQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroMuQuarticNoABCDEG810]
  compute_degree
  omega

theorem muQuarticFaceABCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceABCDEG810 A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 2048 : k) * muQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  simp only [muQuarticFaceABCDEG810, muQuarticInnerABCDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD : ((B * C * D)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    omega
  have hcf_BCD : ((B * C * D)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CG : ((C * G)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne hGne]
    omega
  have hcf_CG : ((C * G)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_AD2, hcf_B4, hcf_B2E, hcf_BCD, hcf_C3, hcf_CG, hcf_E2]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceABCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoABCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * C * F)
  - (15 / 128 : k) • (B ^ 2 * F)
  + (5 / 16 : k) • (E * F)
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
theorem degreeZeroNuQuartic810_eq_ABCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceABCDEG810 A B C D E F G +
        degreeZeroNuQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceABCDEG810, degreeZeroNuQuarticNoABCDEG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoABCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G) :
    (degreeZeroNuQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroNuQuarticNoABCDEG810]
  compute_degree
  omega

theorem nuQuarticFaceABCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceABCDEG810 A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 4096 : k) * nuQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  simp only [nuQuarticFaceABCDEG810, nuQuarticInnerABCDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2D : ((A * B ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABC2 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC2 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_ABC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABG : ((A * B * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    omega
  have hcf_ABG : ((A * B * G)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ABG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ADE : ((A * D * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    omega
  have hcf_ADE : ((A * D * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ADE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
    omega
  have hcf_B3C : ((B ^ 3 * C)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DG : ((D * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hGne]
    omega
  have hcf_DG : ((D * G)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_DG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A2B3, hcf_AB2D, hcf_ABC2, hcf_ABG, hcf_ADE, hcf_B3C, hcf_BCE, hcf_BD2, hcf_C2D, hcf_DG]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceABCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoABCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  - (25 / 128 : k) • (B * C * F)
  + (5 / 32 : k) • F ^ 2
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
theorem degreeZeroXiQuartic810_eq_ABCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceABCDEG810 A B C D E F G +
        degreeZeroXiQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceABCDEG810, degreeZeroXiQuarticNoABCDEG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoABCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G) :
    (degreeZeroXiQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroXiQuarticNoABCDEG810]
  compute_degree
  omega

theorem xiQuarticFaceABCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (xiQuarticFaceABCDEG810 A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) =
      (1 / 2048 : k) * xiQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  simp only [xiQuarticFaceABCDEG810, xiQuarticInnerABCDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB4 : ((A * B ^ 4)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 4 hBne), natDegree_pow]
  have hcf_AB4 : ((A * B ^ 4)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 4 := by
    rw [← hdeg_AB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCD : ((A * B * C * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCD : ((A * B * C * D)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_ABCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
    omega
  have hcf_B3D : ((B ^ 3 * D)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B2G : ((B ^ 2 * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hGne, natDegree_pow]
    omega
  have hcf_B2G : ((B ^ 2 * G)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_B2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDE : ((B * D * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hEne, natDegree_mul hBne hDne]
    omega
  have hcf_BDE : ((B * D * E)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_EG : ((E * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hEne hGne]
    omega
  have hcf_EG : ((E * G)).coeff (A.natDegree + 4 * B.natDegree) =
      E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_EG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB4, hcf_AB2E, hcf_ABCD, hcf_B3D, hcf_B2C2, hcf_B2G, hcf_BDE, hcf_C2E, hcf_CD2, hcf_EG]
  ring

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
  simp only [degreeZeroOmicronQuarticNoABCDEG810]
  compute_degree
  omega

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

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_ABCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceABCDEG810 A B C D E F G +
        degreeZeroPiQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceABCDEG810, degreeZeroPiQuarticNoABCDEG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoABCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G) :
    (degreeZeroPiQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroPiQuarticNoABCDEG810]
  compute_degree
  omega

theorem piQuarticFaceABCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceABCDEG810 A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) =
      (1 / 4096 : k) * piQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  simp only [piQuarticFaceABCDEG810, piQuarticInnerABCDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B4 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B4 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hdeg_A2B4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB3D : ((A * B ^ 3 * D)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3D : ((A * B ^ 3 * D)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_AB3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2C2 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_AB2C2 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_AB2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2G : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2G : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_AB2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABDE : ((A * B * D * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne]
    omega
  have hcf_ABDE : ((A * B * D * E)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ABDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ACD2 : ((A * C * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne, natDegree_pow]
    omega
  have hcf_ACD2 : ((A * C * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ACD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4C : ((B ^ 4 * C)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hCne, natDegree_pow]
    omega
  have hcf_B4C : ((B ^ 4 * C)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 4 * C.leadingCoeff := by
    rw [← hdeg_B4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CE : ((B ^ 2 * C * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CE : ((B ^ 2 * C * E)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2CE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D2 : ((B ^ 2 * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hDne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2D2 : ((B ^ 2 * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff ^ 2 := by
    rw [← hdeg_B2D2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_BC2D : ((B * C ^ 2 * D)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2D : ((B * C ^ 2 * D)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_BC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDG : ((B * D * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hGne, natDegree_mul hBne hDne]
    omega
  have hcf_BDG : ((B * D * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C4 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C2G : ((C ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow]
    omega
  have hcf_C2G : ((C ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_C2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CE2 : ((C * E ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_CE2 : ((C * E ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_CE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D2E : ((D ^ 2 * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hEne, natDegree_pow]
    omega
  have hcf_D2E : ((D ^ 2 * E)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      D.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_D2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_G2 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_G2 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A2B4, hcf_AB3D, hcf_AB2C2, hcf_AB2G, hcf_ABDE, hcf_ACD2, hcf_B4C, hcf_B2CE, hcf_B2D2, hcf_BC2D, hcf_BDG, hcf_C4, hcf_C2G, hcf_CE2, hcf_D2E, hcf_G2]
  ring

set_option maxHeartbeats 16000000 in
def primitiveQuarticFaceABCDEG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  + (5 / 128 : k) • (A * B * C * G)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (15 / 128 : k) • (A * C * D * E)
  + (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveQuarticNoABCDEG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  - (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 32 : k) • (A * B * D * F)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  + (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (171 / 262144 * l : k) • (A ^ 5 * E)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (45 / 32768 * l : k) • (A ^ 4 * G)
  - (9 / 4096 * l : k) • (A ^ 3 * B * F)
  + (99 / 8192 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (9 / 4096 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (243 / 8192 * l : k) • (A * B ^ 3 * D)
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (27 / 1024 * l : k) • (A ^ 2 * C * G)
  - (9 / 512 * l : k) • (A ^ 2 * D * F)
  + (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)
  + (9 / 1024 * l : k) • (A * B ^ 2 * G)
  + (9 / 256 * l : k) • (A * B * C * F)
  + (45 / 512 * l : k) • (A * B * D * E)
  + (9 / 1024 * l : k) • (A * C ^ 2 * E)
  + (9 / 256 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  + (9 / 64 * l : k) • (A * E * G)
  - (9 / 64 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2
  + (25 / 1048576 * beta : k) • A ^ 7
  + (21 / 32768 * beta : k) • (A ^ 5 * C)
  - (119 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 16384 * beta : k) • (A ^ 4 * E)
  - (7 / 2048 * beta : k) • (A ^ 3 * B * D)
  + (21 / 4096 * beta : k) • (A ^ 3 * C ^ 2)
  - (21 / 8192 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (119 / 16384 * beta : k) • (A * B ^ 4)
  + (21 / 512 * beta : k) • (A ^ 2 * C * E)
  - (7 / 512 * beta : k) • (A ^ 2 * D ^ 2)
  - (21 / 512 * beta : k) • (A * B ^ 2 * E)
  - (7 / 128 * beta : k) • (A * B * C * D)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 64 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)
  + (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2
  + (3 / 2048 * gamma : k) • (A ^ 3 * B * C)
  + (3 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 3 * F)
  + (3 / 256 * gamma : k) • (A ^ 2 * B * E)
  + (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 128 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 128 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  - (3 / 32 * gamma : k) • (A * C * F)
  + (3 / 16 * gamma : k) • (A * D * E)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)
  + (25 / 262144 * delta : k) • A ^ 6
  + (35 / 16384 * delta : k) • (A ^ 4 * C)
  - (25 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  - (5 / 512 * delta : k) • (A ^ 2 * B * D)
  + (15 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (65 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (5 / 64 * delta : k) • (A * C * E)
  + (5 / 64 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2
  - (1 / 256 * epsilon : k) • (A ^ 3 * D)
  + (1 / 64 * epsilon : k) • (A ^ 2 * B * C)
  - (1 / 32 * epsilon : k) • (A * B ^ 3)
  - (1 / 32 * epsilon : k) • (A ^ 2 * F)
  + (1 / 8 * epsilon : k) • (A * B * E)
  + (1 / 16 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)
  + (3 / 8192 * zeta : k) • A ^ 5
  + (3 / 512 * zeta : k) • (A ^ 3 * C)
  - (3 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (3 / 32 * zeta : k) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2
  - (1 / 512 * eta : k) • (A ^ 3 * B)
  - (1 / 64 * eta : k) • (A ^ 2 * D)
  + (1 / 32 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • B ^ 3
  - (1 / 4 * eta : k) • (A * F)
  - (1 / 4 * eta : k) • (B * E)
  - (1 / 4 * eta : k) • (C * D)
  + (5 / 4096 * theta : k) • A ^ 4
  + (3 / 128 * theta : k) • (A ^ 2 * C)
  + (1 / 128 * theta : k) • (A * B ^ 2)
  + (1 / 8 * theta : k) • (A * E)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveQuartic810_eq_ABCDEG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticFaceABCDEG810 A B C D E F G +
        degreeZeroPrimitiveQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810,
    rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810, primitiveQuarticFaceABCDEG810, degreeZeroPrimitiveQuarticNoABCDEG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveQuarticNoABCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G) :
    (degreeZeroPrimitiveQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  simp only [degreeZeroPrimitiveQuarticNoABCDEG810]
  compute_degree
  omega

theorem primitiveQuarticFaceABCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (primitiveQuarticFaceABCDEG810 A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * primitiveQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  simp only [primitiveQuarticFaceABCDEG810, primitiveQuarticInnerABCDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A4B3 : ((A ^ 4 * B ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A4B3 : ((A ^ 4 * B ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A4B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3B2D : ((A ^ 3 * B ^ 2 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A3B2D : ((A ^ 3 * B ^ 2 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A3B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3BC2 : ((A ^ 3 * B * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 3 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A3BC2 : ((A ^ 3 * B * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A3BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3BG : ((A ^ 3 * B * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne, natDegree_pow]
    omega
  have hcf_A3BG : ((A ^ 3 * B * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A3BG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A3DE : ((A ^ 3 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 3 hAne) hDne, natDegree_pow]
    omega
  have hcf_A3DE : ((A ^ 3 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A3DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2B3C : ((A ^ 2 * B ^ 3 * C)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne)) hCne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B3C : ((A ^ 2 * B ^ 3 * C)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_A2B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BCE : ((A ^ 2 * B * C * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hCne) hEne, natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hCne, natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow]
    omega
  have hcf_A2BCE : ((A ^ 2 * B * C * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2BD2 : ((A ^ 2 * B * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hDne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BD2 : ((A ^ 2 * B * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2C2D : ((A ^ 2 * C ^ 2 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2C2D : ((A ^ 2 * C ^ 2 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2DG : ((A ^ 2 * D * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DG : ((A ^ 2 * D * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2DG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB5 : ((A * B ^ 5)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 5 hBne), natDegree_pow]
    omega
  have hcf_AB5 : ((A * B ^ 5)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 5 := by
    rw [← hdeg_AB5, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB3E : ((A * B ^ 3 * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3E : ((A * B ^ 3 * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_AB3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2CD : ((A * B ^ 2 * C * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne) hDne, natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2CD : ((A * B ^ 2 * C * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_AB2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABC3 : ((A * B * C ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 3 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC3 : ((A * B * C ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_ABC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCG : ((A * B * C * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hGne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCG : ((A * B * C * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ABCG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABE2 : ((A * B * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hEne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABE2 : ((A * B * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_ABE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ACDE : ((A * C * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hCne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hCne) hDne, natDegree_mul hAne hCne]
    omega
  have hcf_ACDE : ((A * C * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ACDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AD3 : ((A * D ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hDne), natDegree_pow]
    omega
  have hcf_AD3 : ((A * D ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 3 := by
    rw [← hdeg_AD3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4D : ((B ^ 4 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hDne, natDegree_pow]
    omega
  have hcf_B4D : ((B ^ 4 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 4 * D.leadingCoeff := by
    rw [← hdeg_B4D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3C2 : ((B ^ 3 * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B3C2 : ((B ^ 3 * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B3C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B3G : ((B ^ 3 * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hGne, natDegree_pow]
    omega
  have hcf_B3G : ((B ^ 3 * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * G.leadingCoeff := by
    rw [← hdeg_B3G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2DE : ((B ^ 2 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2DE : ((B ^ 2 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2E : ((B * C ^ 2 * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hEne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2E : ((B * C ^ 2 * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_BC2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD2 : ((B * C * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) (pow_ne_zero 2 hDne), natDegree_mul hBne hCne, natDegree_pow]
    omega
  have hcf_BCD2 : ((B * C * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BCD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BEG : ((B * E * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hEne) hGne, natDegree_mul hBne hEne]
    omega
  have hcf_BEG : ((B * E * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BEG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3D : ((C ^ 3 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hCne) hDne, natDegree_pow]
    omega
  have hcf_C3D : ((C ^ 3 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_C3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDG : ((C * D * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hGne, natDegree_mul hCne hDne]
    omega
  have hcf_CDG : ((C * D * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_DE2 : ((D * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_DE2 : ((D * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_DE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A4B3, hcf_A3B2D, hcf_A3BC2, hcf_A3BG, hcf_A3DE, hcf_A2B3C, hcf_A2BCE, hcf_A2BD2, hcf_A2C2D, hcf_A2DG, hcf_AB5, hcf_AB3E, hcf_AB2CD, hcf_ABC3, hcf_ABCG, hcf_ABE2, hcf_ACDE, hcf_AD3, hcf_B4D, hcf_B3C2, hcf_B3G, hcf_B2DE, hcf_BC2E, hcf_BCD2, hcf_BEG, hcf_C3D, hcf_CDG, hcf_DE2]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_ABCDEG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := primitiveQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroPrimitiveQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_ABCDEG_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff
  have hpow : D.leadingCoeff ^ 6 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact hlc ((pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hpow)


def kappaQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + (-60 : k) * b * c ^ 2 + 160 * b * g + 160 * c * f

def muQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  60 * a * b ^ 2 * c + (-160 : k) * a * b * f + (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * c * g + 640 * d * f

def nuQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + 60 * a * b * c ^ 2 + (-160 : k) * a * b * g + (-160 : k) * a * c * f + 280 * b ^ 3 * c + (-480 : k) * b ^ 2 * f + (-480 : k) * b * d ^ 2 + (-480 : k) * c ^ 2 * d + 1280 * d * g

def xiQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  (-15 : k) * a * b ^ 4 + 120 * a * b * c * d + (-160 : k) * a * d * f + 110 * b ^ 3 * d + 180 * b ^ 2 * c ^ 2 + (-160 : k) * b ^ 2 * g + (-400 : k) * b * c * f + (-240 : k) * c * d ^ 2 + 320 * f ^ 2

def omicronQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * b * g + (-160 : k) * a ^ 2 * c * f + (-1120 : k) * a * b ^ 3 * c + 1600 * a * b ^ 2 * f + 2240 * a * b * d ^ 2 + 960 * a * c ^ 2 * d + (-2560 : k) * a * d * g + (-336 : k) * b ^ 5 + 8640 * b ^ 2 * c * d + 2880 * b * c ^ 3 + (-7680 : k) * b * c * g + (-10240 : k) * b * d * f + (-5120 : k) * c ^ 2 * f + (-2560 : k) * d ^ 3 + 20480 * f * g

def piQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-480 : k) * a * b ^ 3 * d + (-360 : k) * a * b ^ 2 * c ^ 2 + 320 * a * b ^ 2 * g + 640 * a * b * c * f + 640 * a * c * d ^ 2 + (-1280 : k) * a * f ^ 2 + (-560 : k) * b ^ 4 * c + 800 * b ^ 3 * f + 1440 * b ^ 2 * d ^ 2 + 2880 * b * c ^ 2 * d + (-2560 : k) * b * d * g + 240 * c ^ 4 + (-1280 : k) * c ^ 2 * g + (-3840 : k) * c * d * f + 5120 * g ^ 2

def primitiveQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + (-60 : k) * a ^ 3 * b ^ 2 * d + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * b * g + (-160 : k) * a ^ 3 * c * f + 120 * a ^ 2 * b ^ 3 * c + (-160 : k) * a ^ 2 * b ^ 2 * f + (-800 : k) * a ^ 2 * b * d ^ 2 + 480 * a ^ 2 * c ^ 2 * d + (-1280 : k) * a ^ 2 * d * g + 520 * a * b ^ 5 + (-8640 : k) * a * b ^ 2 * c * d + (-960 : k) * a * b * c ^ 3 + 2560 * a * b * c * g + 10240 * a * b * d * f + 2560 * a * d ^ 3 + (-20480 : k) * a * f * g + (-4000 : k) * b ^ 4 * d + (-8480 : k) * b ^ 3 * c ^ 2 + 3840 * b ^ 3 * g + 21760 * b ^ 2 * c * f + 23040 * b * c * d ^ 2 + (-20480 : k) * b * f ^ 2 + 7680 * c ^ 3 * d + (-20480 : k) * c * d * g + (-20480 : k) * d ^ 2 * f

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABCDFG_identity
    (a b c d f g : k) :
    ((876483770191 / 57744057588224 : k) * a ^ 4 * b * c ^ 2 + (-13111824287 / 1862711535104 : k) * a ^ 4 * b * g + (-1159758490199 / 57744057588224 : k) * a ^ 4 * c * f + (-382943254258883 / 3048886240658227200 : k) * a ^ 3 * b ^ 3 * c + (203661567940141 / 254073853388185600 : k) * a ^ 3 * b ^ 2 * f + (162964447860993 / 36296264769740800 : k) * a ^ 3 * b * d ^ 2 + (-192782468103 / 12553055997440 : k) * a ^ 3 * c ^ 2 * d + (-567322695673 / 37659167992320 : k) * a ^ 3 * d * g + (4372128747697 / 232296094526341120 : k) * a ^ 2 * b ^ 5 + (-8883471500926707 / 508147706776371200 : k) * a ^ 2 * b ^ 2 * c * d + (9294626144752917 / 63518463347046400 : k) * a ^ 2 * b * c ^ 3 + (1085413036877447 / 23819423755142400 : k) * a ^ 2 * b * c * g + (15251803434807077 / 1333887730287974400 : k) * a ^ 2 * b * d * f + (-614927651944597 / 4330804319116800 : k) * a ^ 2 * c ^ 2 * f + (-54824910649910239 / 889258486858649600 : k) * a ^ 2 * d ^ 3 + (9156344039 / 2984890194880 : k) * a ^ 2 * f * g + (563462879754007 / 127036926694092800 : k) * a * b ^ 4 * d + (-563634703262547239 / 6097772481316454400 : k) * a * b ^ 3 * c ^ 2 + (205691201384738063 / 1067110184230379520 : k) * a * b ^ 3 * g + (1258224178580510459 / 5335550921151897600 : k) * a * b ^ 2 * c * f + (-966254141234014949 / 1333887730287974400 : k) * a * b * c * d ^ 2 + (13822077444865889 / 166735966285996800 : k) * a * b * f ^ 2 + (-160257382590964217 / 889258486858649600 : k) * a * c ^ 3 * d + (-25487901599571739 / 30315630233817600 : k) * a * c * d * g + (115542502561061803 / 166735966285996800 : k) * a * d ^ 2 * f + (11517374573658787 / 762221560164556800 : k) * b ^ 5 * c + (37363319152837827 / 889258486858649600 : k) * b ^ 4 * f + (-21912017970267499 / 77326824944230400 : k) * b ^ 3 * d ^ 2 + (-4731526664929552293 / 1778516973717299200 : k) * b ^ 2 * c ^ 2 * d + (-3601798944239999 / 5014615527398400 : k) * b ^ 2 * d * g + (-2668087471364311 / 9074066192435200 : k) * b * c ^ 4 + (-369315182070389 / 1134258274054400 : k) * b * c ^ 2 * g + (478460918764723051 / 83367983142998400 : k) * b * c * d * f + (33275644234359 / 31014874681175 : k) * b * g ^ 2 + (283181612884957 / 307347403292160 : k) * c ^ 3 * f + (2724987940039361 / 3624694919260800 : k) * c * d ^ 3 + (-3037197967137901 / 850693705540800 : k) * c * f * g + (-1933647010850117 / 604115819876800 : k) * d * f ^ 2) * kappaQuarticInnerABCDFG810 a b c d f g +
      ((-106128823798379477 / 1778516973717299200 : k) * a * b ^ 2 * d ^ 2 + (5259409458983929 / 127036926694092800 : k) * a * b * c ^ 2 * d + (852652795636909 / 15879615836761600 : k) * a * b * d * g + (-521791582409 / 346464345529344 : k) * a * c * d * f + (13116386243091 / 72592529539481600 : k) * b ^ 6 + (-47650227562174561 / 381110780082278400 : k) * b ^ 3 * c * d + (4569382566378759 / 254073853388185600 : k) * b ^ 2 * c ^ 3 + (23152319960329913 / 95277695020569600 : k) * b ^ 2 * c * g + (38698926182597837 / 222314621714662400 : k) * b ^ 2 * d * f + (-6453256793899123 / 38111078008227840 : k) * b * c ^ 2 * f + (17574653345402907 / 88925848685864960 : k) * b * d ^ 3 + (-284141264836251 / 1587961583676160 : k) * b * f * g + (16816494639790619 / 444629243429324800 : k) * c ^ 2 * d ^ 2 + (9265244263065671 / 23819423755142400 : k) * c * f ^ 2 + (-769226554419927 / 1792859852537600 : k) * d ^ 2 * g) * muQuarticInnerABCDFG810 a b c d f g +
      ((2629451310573 / 288720287941120 : k) * a ^ 3 * b * c ^ 2 + (-39335472861 / 9313557675520 : k) * a ^ 3 * b * g + (-3479275470597 / 288720287941120 : k) * a ^ 3 * c * f + (1360940780584439 / 508147706776371200 : k) * a ^ 2 * b * d ^ 2 + (-25032793346557 / 3175923167352320 : k) * a ^ 2 * c ^ 2 * d + (-24010228037457 / 3175923167352320 : k) * a ^ 2 * d * g + (553904777526981 / 11046689277747200 : k) * a * b * c ^ 3 + (974539765217 / 18168896838400 : k) * a * b * c * g + (-11355632070228541 / 333471932571993600 : k) * a * b * d * f + (-10172471651039 / 303916092569600 : k) * a * c ^ 2 * f + (-11391115361805017 / 889258486858649600 : k) * a * d ^ 3 + (3709485043 / 135676827040 : k) * a * f * g + (-4443014213160829 / 508147706776371200 : k) * b ^ 4 * d + (-273480823088980919 / 6097772481316454400 : k) * b ^ 3 * c ^ 2 + (166862667776312779 / 5335550921151897600 : k) * b ^ 3 * g + (167786507052955113 / 1778516973717299200 : k) * b ^ 2 * c * f + (-14097232165527591 / 444629243429324800 : k) * b * c * d ^ 2 + (37953001842803 / 10420997892874800 : k) * b * f ^ 2 + (-85038809893104521 / 889258486858649600 : k) * c ^ 3 * d + (122966923042776971 / 333471932571993600 : k) * c * d * g + (1608046498037281 / 30315630233817600 : k) * d ^ 2 * f) * nuQuarticInnerABCDFG810 a b c d f g +
      ((7615634641849 / 156706735231200 : k) * a * b ^ 2 * g + (1396039010767 / 39176683807800 : k) * a * b * c * f + (-35384474641 / 593586118300 : k) * a * c * d ^ 2 + (2121291982 / 89037917745 : k) * a * f ^ 2 + (16703104693733 / 398889871497600 : k) * b ^ 3 * f + (-528086876564073 / 5557865542866560 : k) * b ^ 2 * d ^ 2 + (-907363129413981 / 1389466385716640 : k) * b * c ^ 2 * d + (-1929281670864703 / 5210498946437400 : k) * b * d * g + (-1862723246807 / 39176683807800 : k) * c ^ 4 + (-8342281181907 / 13058894602600 : k) * c ^ 2 * g + (9315444779119637 / 10420997892874800 : k) * c * d * f + (1428162017839 / 979417095195 : k) * g ^ 2) * xiQuarticInnerABCDFG810 a b c d f g +
      ((876483770191 / 288720287941120 : k) * a ^ 2 * b * c ^ 2 + (-13111824287 / 9313557675520 : k) * a ^ 2 * b * g + (-1159758490199 / 288720287941120 : k) * a ^ 2 * c * f + (-117097611737367 / 101629541355274240 : k) * a * b * d ^ 2 + (-258324452611 / 635184633470464 : k) * a * c ^ 2 * d + (-528726219473 / 9527769502056960 : k) * a * d * g + (4372128747697 / 232296094526341120 : k) * b ^ 5 + (-294067939355647 / 20325908271054848 : k) * b ^ 2 * c * d + (-48617654537491 / 50814770677637120 : k) * b * c ^ 3 + (105366400039 / 2849213367840 : k) * b * c * g + (219959290511867 / 12703692669409280 : k) * b * d * f + (3651121868557 / 182349655541760 : k) * c ^ 2 * f + (-1 / 2560 : k) * d ^ 3 + (-72452326907 / 2984890194880 : k) * f * g) * omicronQuarticInnerABCDFG810 a b c d f g +
      ((-1060645991 / 356151670980 : k) * a * d * f + (-97465503338573 / 23819423755142400 : k) * b ^ 3 * d + (-11553883108717 / 567129137027200 : k) * b ^ 2 * c ^ 2 + (8962114747907 / 744356992348200 : k) * b ^ 2 * g + (89312336837771 / 2977427969392800 : k) * b * c * f + (1060645991 / 178075835490 : k) * f ^ 2) * piQuarticInnerABCDFG810 a b c d f g +
      ((876483770191 / 288720287941120 : k) * a * b * c ^ 2 + (-13111824287 / 9313557675520 : k) * a * b * g + (-1159758490199 / 288720287941120 : k) * a * c * f + (-382943254258883 / 3048886240658227200 : k) * b ^ 3 * c + (203661567940141 / 254073853388185600 : k) * b ^ 2 * f + (753024774078149 / 254073853388185600 : k) * b * d ^ 2 + (-3207078402921 / 453703309621760 : k) * c ^ 2 * d + (-14194646334685 / 1905553900411392 : k) * d * g) * primitiveQuarticInnerABCDFG810 a b c d f g =
      d ^ 6 := by
  simp only [kappaQuarticInnerABCDFG810, muQuarticInnerABCDFG810, nuQuarticInnerABCDFG810, xiQuarticInnerABCDFG810, omicronQuarticInnerABCDFG810, piQuarticInnerABCDFG810, primitiveQuarticInnerABCDFG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)
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
theorem degreeZeroKappaQuartic810_eq_ABCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABCDFG810 A B C D E F G +
        degreeZeroKappaQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABCDFG810, degreeZeroKappaQuarticNoABCDFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoABCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroKappaQuarticNoABCDFG810]
  compute_degree
  omega

theorem kappaQuarticFaceABCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceABCDFG810 A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 512 : k) * kappaQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  simp only [kappaQuarticFaceABCDFG810, kappaQuarticInnerABCDFG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_CF : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    omega
  have hcf_CF : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_B2D, hcf_BC2, hcf_BG, hcf_CF]
  ring

set_option maxHeartbeats 16000000 in
def muQuarticFaceABCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoABCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * E)
  + (5 / 32 : k) • E ^ 2
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
theorem degreeZeroMuQuartic810_eq_ABCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceABCDFG810 A B C D E F G +
        degreeZeroMuQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceABCDFG810, degreeZeroMuQuarticNoABCDFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoABCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroMuQuarticNoABCDFG810]
  compute_degree
  omega

theorem muQuarticFaceABCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceABCDFG810 A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 2048 : k) * muQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  simp only [muQuarticFaceABCDFG810, muQuarticInnerABCDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABF : ((A * B * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    omega
  have hcf_ABF : ((A * B * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_BCD : ((B * C * D)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    omega
  have hcf_BCD : ((B * C * D)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CG : ((C * G)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne hGne]
    omega
  have hcf_CG : ((C * G)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_DF : ((D * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hDne hFne]
    omega
  have hcf_DF : ((D * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_DF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB2C, hcf_ABF, hcf_AD2, hcf_B4, hcf_BCD, hcf_C3, hcf_CG, hcf_DF]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceABCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoABCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D * E)
  - (15 / 64 : k) • (B * C * E)
  + (5 / 16 : k) • (E * F)
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
theorem degreeZeroNuQuartic810_eq_ABCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceABCDFG810 A B C D E F G +
        degreeZeroNuQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceABCDFG810, degreeZeroNuQuarticNoABCDFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoABCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroNuQuarticNoABCDFG810]
  compute_degree
  omega

theorem nuQuarticFaceABCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceABCDFG810 A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 4096 : k) * nuQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  simp only [nuQuarticFaceABCDFG810, nuQuarticInnerABCDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2D : ((A * B ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2D : ((A * B ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AB2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABC2 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC2 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_ABC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABG : ((A * B * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    omega
  have hcf_ABG : ((A * B * G)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ABG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ACF : ((A * C * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) hFne, natDegree_mul hAne hCne]
    omega
  have hcf_ACF : ((A * C * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ACF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
    omega
  have hcf_B3C : ((B ^ 3 * C)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2F : ((B ^ 2 * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hFne, natDegree_pow]
    omega
  have hcf_B2F : ((B ^ 2 * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DG : ((D * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hGne]
    omega
  have hcf_DG : ((D * G)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_DG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A2B3, hcf_AB2D, hcf_ABC2, hcf_ABG, hcf_ACF, hcf_B3C, hcf_B2F, hcf_BD2, hcf_C2D, hcf_DG]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceABCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoABCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
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
theorem degreeZeroXiQuartic810_eq_ABCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceABCDFG810 A B C D E F G +
        degreeZeroXiQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceABCDFG810, degreeZeroXiQuarticNoABCDFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoABCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G) :
    (degreeZeroXiQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroXiQuarticNoABCDFG810]
  compute_degree
  omega

theorem xiQuarticFaceABCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (xiQuarticFaceABCDFG810 A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) =
      (1 / 2048 : k) * xiQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  simp only [xiQuarticFaceABCDFG810, xiQuarticInnerABCDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB4 : ((A * B ^ 4)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 4 hBne), natDegree_pow]
  have hcf_AB4 : ((A * B ^ 4)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 4 := by
    rw [← hdeg_AB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCD : ((A * B * C * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCD : ((A * B * C * D)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_ABCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ADF : ((A * D * F)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    omega
  have hcf_ADF : ((A * D * F)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ADF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3D : ((B ^ 3 * D)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hDne, natDegree_pow]
    omega
  have hcf_B3D : ((B ^ 3 * D)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_B3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B2G : ((B ^ 2 * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hGne, natDegree_pow]
    omega
  have hcf_B2G : ((B ^ 2 * G)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_B2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCF : ((B * C * F)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hFne, natDegree_mul hBne hCne]
    omega
  have hcf_BCF : ((B * C * F)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BCF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CD2 : ((C * D ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_CD2 : ((C * D ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_CD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_F2 : (F ^ 2).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (A.natDegree + 4 * B.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB4, hcf_ABCD, hcf_ADF, hcf_B3D, hcf_B2C2, hcf_B2G, hcf_BCF, hcf_CD2, hcf_F2]
  ring

set_option maxHeartbeats 16000000 in
def omicronQuarticFaceABCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * C * F)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * D * G)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoABCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 2 * D * E)
  + (15 / 512 : k) • (A * B * C * E)
  + (5 / 128 : k) • (B ^ 3 * E)
  - (5 / 128 : k) • (A * E * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (25 / 128 : k) • (C * D * E)
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
theorem degreeZeroOmicronQuartic810_eq_ABCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceABCDFG810 A B C D E F G +
        degreeZeroOmicronQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceABCDFG810, degreeZeroOmicronQuarticNoABCDFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoABCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroOmicronQuarticNoABCDFG810]
  compute_degree
  omega

theorem omicronQuarticFaceABCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceABCDFG810 A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * omicronQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  simp only [omicronQuarticFaceABCDFG810, omicronQuarticInnerABCDFG810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_A2CF : ((A ^ 2 * C * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hCne, natDegree_pow]
    omega
  have hcf_A2CF : ((A ^ 2 * C * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A2CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB3C : ((A * B ^ 3 * C)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3C : ((A * B ^ 3 * C)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_AB3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2F : ((A * B ^ 2 * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hFne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2F : ((A * B ^ 2 * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_AB2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
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
  have hdeg_BDF : ((B * D * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hFne, natDegree_mul hBne hDne]
    omega
  have hcf_BDF : ((B * D * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2F : ((C ^ 2 * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hFne, natDegree_pow]
    omega
  have hcf_C2F : ((C ^ 2 * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_C2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D3 : (D ^ 3).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (3 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_FG : ((F * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hFne hGne]
    omega
  have hcf_FG : ((F * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_FG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A3B3, hcf_A2B2D, hcf_A2BC2, hcf_A2BG, hcf_A2CF, hcf_AB3C, hcf_AB2F, hcf_ABD2, hcf_AC2D, hcf_ADG, hcf_B5, hcf_B2CD, hcf_BC3, hcf_BCG, hcf_BDF, hcf_C2F, hcf_D3, hcf_FG]
  ring

set_option maxHeartbeats 16000000 in
def piQuarticFaceABCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoABCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (A * B * D * E)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
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
theorem degreeZeroPiQuartic810_eq_ABCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceABCDFG810 A B C D E F G +
        degreeZeroPiQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceABCDFG810, degreeZeroPiQuarticNoABCDFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoABCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G) :
    (degreeZeroPiQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroPiQuarticNoABCDFG810]
  compute_degree
  omega

theorem piQuarticFaceABCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceABCDFG810 A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) =
      (1 / 4096 : k) * piQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  simp only [piQuarticFaceABCDFG810, piQuarticInnerABCDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B4 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B4 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hdeg_A2B4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB3D : ((A * B ^ 3 * D)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3D : ((A * B ^ 3 * D)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_AB3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2C2 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_AB2C2 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_AB2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2G : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2G : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_AB2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCF : ((A * B * C * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCF : ((A * B * C * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABCF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ACD2 : ((A * C * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne, natDegree_pow]
    omega
  have hcf_ACD2 : ((A * C * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ACD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AF2 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne), natDegree_pow]
    omega
  have hcf_AF2 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_AF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4C : ((B ^ 4 * C)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hCne, natDegree_pow]
    omega
  have hcf_B4C : ((B ^ 4 * C)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 4 * C.leadingCoeff := by
    rw [← hdeg_B4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3F : ((B ^ 3 * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hFne, natDegree_pow]
    omega
  have hcf_B3F : ((B ^ 3 * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * F.leadingCoeff := by
    rw [← hdeg_B3F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D2 : ((B ^ 2 * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hDne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2D2 : ((B ^ 2 * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff ^ 2 := by
    rw [← hdeg_B2D2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_BC2D : ((B * C ^ 2 * D)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2D : ((B * C ^ 2 * D)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_BC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDG : ((B * D * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hGne, natDegree_mul hBne hDne]
    omega
  have hcf_BDG : ((B * D * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C4 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C2G : ((C ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow]
    omega
  have hcf_C2G : ((C ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_C2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDF : ((C * D * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hFne, natDegree_mul hCne hDne]
    omega
  have hcf_CDF : ((C * D * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_G2 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_G2 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A2B4, hcf_AB3D, hcf_AB2C2, hcf_AB2G, hcf_ABCF, hcf_ACD2, hcf_AF2, hcf_B4C, hcf_B3F, hcf_B2D2, hcf_BC2D, hcf_BDG, hcf_C4, hcf_C2G, hcf_CDF, hcf_G2]
  ring

set_option maxHeartbeats 16000000 in
def primitiveQuarticFaceABCDFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  + (5 / 128 : k) • (A * B * C * G)
  + (5 / 32 : k) • (A * B * D * F)
  + (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 16 : k) • (D ^ 2 * F)

set_option maxHeartbeats 32000000 in
def degreeZeroPrimitiveQuarticNoABCDFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 3 * D * E)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (15 / 128 : k) • (A * C * D * E)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D * E ^ 2)
  + (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (171 / 262144 * l : k) • (A ^ 5 * E)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (45 / 32768 * l : k) • (A ^ 4 * G)
  - (9 / 4096 * l : k) • (A ^ 3 * B * F)
  + (99 / 8192 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (9 / 4096 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (243 / 8192 * l : k) • (A * B ^ 3 * D)
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (27 / 1024 * l : k) • (A ^ 2 * C * G)
  - (9 / 512 * l : k) • (A ^ 2 * D * F)
  + (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)
  + (9 / 1024 * l : k) • (A * B ^ 2 * G)
  + (9 / 256 * l : k) • (A * B * C * F)
  + (45 / 512 * l : k) • (A * B * D * E)
  + (9 / 1024 * l : k) • (A * C ^ 2 * E)
  + (9 / 256 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  + (9 / 64 * l : k) • (A * E * G)
  - (9 / 64 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2
  + (25 / 1048576 * beta : k) • A ^ 7
  + (21 / 32768 * beta : k) • (A ^ 5 * C)
  - (119 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 16384 * beta : k) • (A ^ 4 * E)
  - (7 / 2048 * beta : k) • (A ^ 3 * B * D)
  + (21 / 4096 * beta : k) • (A ^ 3 * C ^ 2)
  - (21 / 8192 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (119 / 16384 * beta : k) • (A * B ^ 4)
  + (21 / 512 * beta : k) • (A ^ 2 * C * E)
  - (7 / 512 * beta : k) • (A ^ 2 * D ^ 2)
  - (21 / 512 * beta : k) • (A * B ^ 2 * E)
  - (7 / 128 * beta : k) • (A * B * C * D)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 64 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)
  + (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2
  + (3 / 2048 * gamma : k) • (A ^ 3 * B * C)
  + (3 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 3 * F)
  + (3 / 256 * gamma : k) • (A ^ 2 * B * E)
  + (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 128 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 128 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  - (3 / 32 * gamma : k) • (A * C * F)
  + (3 / 16 * gamma : k) • (A * D * E)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)
  + (25 / 262144 * delta : k) • A ^ 6
  + (35 / 16384 * delta : k) • (A ^ 4 * C)
  - (25 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  - (5 / 512 * delta : k) • (A ^ 2 * B * D)
  + (15 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (65 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (5 / 64 * delta : k) • (A * C * E)
  + (5 / 64 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2
  - (1 / 256 * epsilon : k) • (A ^ 3 * D)
  + (1 / 64 * epsilon : k) • (A ^ 2 * B * C)
  - (1 / 32 * epsilon : k) • (A * B ^ 3)
  - (1 / 32 * epsilon : k) • (A ^ 2 * F)
  + (1 / 8 * epsilon : k) • (A * B * E)
  + (1 / 16 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)
  + (3 / 8192 * zeta : k) • A ^ 5
  + (3 / 512 * zeta : k) • (A ^ 3 * C)
  - (3 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (3 / 32 * zeta : k) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2
  - (1 / 512 * eta : k) • (A ^ 3 * B)
  - (1 / 64 * eta : k) • (A ^ 2 * D)
  + (1 / 32 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • B ^ 3
  - (1 / 4 * eta : k) • (A * F)
  - (1 / 4 * eta : k) • (B * E)
  - (1 / 4 * eta : k) • (C * D)
  + (5 / 4096 * theta : k) • A ^ 4
  + (3 / 128 * theta : k) • (A ^ 2 * C)
  + (1 / 128 * theta : k) • (A * B ^ 2)
  + (1 / 8 * theta : k) • (A * E)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveQuartic810_eq_ABCDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticFaceABCDFG810 A B C D E F G +
        degreeZeroPrimitiveQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810,
    rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810, primitiveQuarticFaceABCDFG810, degreeZeroPrimitiveQuarticNoABCDFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveQuarticNoABCDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G) :
    (degreeZeroPrimitiveQuarticNoABCDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  simp only [degreeZeroPrimitiveQuarticNoABCDFG810]
  compute_degree
  omega

theorem primitiveQuarticFaceABCDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (primitiveQuarticFaceABCDFG810 A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * primitiveQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
  simp only [primitiveQuarticFaceABCDFG810, primitiveQuarticInnerABCDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A4B3 : ((A ^ 4 * B ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A4B3 : ((A ^ 4 * B ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A4B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3B2D : ((A ^ 3 * B ^ 2 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A3B2D : ((A ^ 3 * B ^ 2 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A3B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3BC2 : ((A ^ 3 * B * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 3 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A3BC2 : ((A ^ 3 * B * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A3BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3BG : ((A ^ 3 * B * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne, natDegree_pow]
    omega
  have hcf_A3BG : ((A ^ 3 * B * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A3BG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A3CF : ((A ^ 3 * C * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 3 hAne) hCne, natDegree_pow]
    omega
  have hcf_A3CF : ((A ^ 3 * C * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A3CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2B3C : ((A ^ 2 * B ^ 3 * C)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne)) hCne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B3C : ((A ^ 2 * B ^ 3 * C)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_A2B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2F : ((A ^ 2 * B ^ 2 * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hFne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B2F : ((A ^ 2 * B ^ 2 * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_A2B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BD2 : ((A ^ 2 * B * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hDne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BD2 : ((A ^ 2 * B * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2C2D : ((A ^ 2 * C ^ 2 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2C2D : ((A ^ 2 * C ^ 2 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2DG : ((A ^ 2 * D * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DG : ((A ^ 2 * D * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2DG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB5 : ((A * B ^ 5)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 5 hBne), natDegree_pow]
    omega
  have hcf_AB5 : ((A * B ^ 5)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 5 := by
    rw [← hdeg_AB5, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2CD : ((A * B ^ 2 * C * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne) hDne, natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2CD : ((A * B ^ 2 * C * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_AB2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABC3 : ((A * B * C ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 3 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC3 : ((A * B * C ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_ABC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCG : ((A * B * C * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hGne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCG : ((A * B * C * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ABCG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABDF : ((A * B * D * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne]
    omega
  have hcf_ABDF : ((A * B * D * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AD3 : ((A * D ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hDne), natDegree_pow]
    omega
  have hcf_AD3 : ((A * D ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 3 := by
    rw [← hdeg_AD3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AFG : ((A * F * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hFne) hGne, natDegree_mul hAne hFne]
    omega
  have hcf_AFG : ((A * F * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_AFG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B4D : ((B ^ 4 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hDne, natDegree_pow]
    omega
  have hcf_B4D : ((B ^ 4 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 4 * D.leadingCoeff := by
    rw [← hdeg_B4D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3C2 : ((B ^ 3 * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B3C2 : ((B ^ 3 * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B3C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B3G : ((B ^ 3 * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hGne, natDegree_pow]
    omega
  have hcf_B3G : ((B ^ 3 * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * G.leadingCoeff := by
    rw [← hdeg_B3G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CF : ((B ^ 2 * C * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CF : ((B ^ 2 * C * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_B2CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD2 : ((B * C * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) (pow_ne_zero 2 hDne), natDegree_mul hBne hCne, natDegree_pow]
    omega
  have hcf_BCD2 : ((B * C * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BCD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BF2 : ((B * F ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hFne), natDegree_pow]
    omega
  have hcf_BF2 : ((B * F ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_BF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3D : ((C ^ 3 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hCne) hDne, natDegree_pow]
    omega
  have hcf_C3D : ((C ^ 3 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_C3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDG : ((C * D * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hGne, natDegree_mul hCne hDne]
    omega
  have hcf_CDG : ((C * D * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D2F : ((D ^ 2 * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hFne, natDegree_pow]
    omega
  have hcf_D2F : ((D ^ 2 * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_D2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A4B3, hcf_A3B2D, hcf_A3BC2, hcf_A3BG, hcf_A3CF, hcf_A2B3C, hcf_A2B2F, hcf_A2BD2, hcf_A2C2D, hcf_A2DG, hcf_AB5, hcf_AB2CD, hcf_ABC3, hcf_ABCG, hcf_ABDF, hcf_AD3, hcf_AFG, hcf_B4D, hcf_B3C2, hcf_B3G, hcf_B2CF, hcf_BCD2, hcf_BF2, hcf_C3D, hcf_CDG, hcf_D2F]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_ABCDFG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDFG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoABCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceABCDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ABCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoABCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceABCDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ABCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoABCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceABCDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ABCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoABCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceABCDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_ABCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoABCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceABCDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_ABCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoABCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceABCDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_ABCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveQuarticInnerABCDFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveQuarticNoABCDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := primitiveQuarticFaceABCDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hFpos, hGpos, hAB, hAC, hAD, hAF, hAG, hElt⟩
      omega
    rw [degreeZeroPrimitiveQuartic810_eq_ABCDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_ABCDFG_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff
  have hpow : D.leadingCoeff ^ 6 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact hlc ((pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hpow)


def kappaQuarticInnerABCEFG810 (a b c e f g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b * c ^ 2 + 160 * b * g + 160 * c * f

def muQuarticInnerABCEFG810 (a b c e f g : k) : k :=
  60 * a * b ^ 2 * c + (-160 : k) * a * b * f + 35 * b ^ 4 + (-240 : k) * b ^ 2 * e + (-80 : k) * c ^ 3 + 640 * c * g + 320 * e ^ 2

def nuQuarticInnerABCEFG810 (a b c e f g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 60 * a * b * c ^ 2 + (-160 : k) * a * b * g + (-160 : k) * a * c * f + 280 * b ^ 3 * c + (-480 : k) * b ^ 2 * f + (-960 : k) * b * c * e + 1280 * e * f

def xiQuarticInnerABCEFG810 (a b c e f g : k) : k :=
  (-15 : k) * a * b ^ 4 + 60 * a * b ^ 2 * e + 180 * b ^ 2 * c ^ 2 + (-160 : k) * b ^ 2 * g + (-400 : k) * b * c * f + (-240 : k) * c ^ 2 * e + 640 * e * g + 320 * f ^ 2

def omicronQuarticInnerABCEFG810 (a b c e f g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * b * g + (-160 : k) * a ^ 2 * c * f + (-1120 : k) * a * b ^ 3 * c + 1600 * a * b ^ 2 * f + 1920 * a * b * c * e + (-2560 : k) * a * e * f + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + 2880 * b * c ^ 3 + (-7680 : k) * b * c * g + (-5120 : k) * b * e ^ 2 + (-5120 : k) * c ^ 2 * f + 20480 * f * g

def piQuarticInnerABCEFG810 (a b c e f g : k) : k :=
  15 * a ^ 2 * b ^ 4 + (-360 : k) * a * b ^ 2 * c ^ 2 + 320 * a * b ^ 2 * g + 640 * a * b * c * f + (-1280 : k) * a * f ^ 2 + (-560 : k) * b ^ 4 * c + 800 * b ^ 3 * f + 2880 * b ^ 2 * c * e + (-3840 : k) * b * e * f + 240 * c ^ 4 + (-1280 : k) * c ^ 2 * g + (-2560 : k) * c * e ^ 2 + 5120 * g ^ 2

def primitiveQuarticInnerABCEFG810 (a b c e f g : k) : k :=
  (-5 : k) * a ^ 4 * b ^ 3 + 60 * a ^ 3 * b * c ^ 2 + (-160 : k) * a ^ 3 * b * g + (-160 : k) * a ^ 3 * c * f + 120 * a ^ 2 * b ^ 3 * c + (-160 : k) * a ^ 2 * b ^ 2 * f + 960 * a ^ 2 * b * c * e + (-1280 : k) * a ^ 2 * e * f + 520 * a * b ^ 5 + (-3200 : k) * a * b ^ 3 * e + (-960 : k) * a * b * c ^ 3 + 2560 * a * b * c * g + 5120 * a * b * e ^ 2 + (-20480 : k) * a * f * g + (-8480 : k) * b ^ 3 * c ^ 2 + 3840 * b ^ 3 * g + 21760 * b ^ 2 * c * f + 23040 * b * c ^ 2 * e + (-20480 : k) * b * e * g + (-20480 : k) * b * f ^ 2 + (-40960 : k) * c * e * f

set_option maxHeartbeats 64000000 in
theorem quarticInner_ABCEFG_identity
    (a b c e f g : k) :
    ((3 / 655360 : k) * a ^ 4 * e * f * g + (-56989354636119 / 27346599116181340160 : k) * a ^ 3 * b * c ^ 5 + (-103082899173780311 / 2262931076864005898240 : k) * a ^ 3 * b * c ^ 3 * g + (414608019111129 / 282866384608000737280 : k) * a ^ 3 * b * c ^ 2 * e ^ 2 + (23961456757473121 / 282866384608000737280 : k) * a ^ 3 * b * c * g ^ 2 + (-640895078702771 / 28286638460800073728 : k) * a ^ 3 * b * e ^ 2 * g + (6408852198322605 / 452586215372801179648 : k) * a ^ 3 * c ^ 4 * f + (6220182581767349 / 51430251746909224960 : k) * a ^ 3 * c ^ 2 * f * g + (-51533079622450791 / 1131465538432002949120 : k) * a ^ 3 * c * e ^ 2 * f + (19 / 655360 : k) * a ^ 3 * f * g ^ 2 + (-3 / 163840 : k) * a ^ 2 * b ^ 3 * g ^ 2 + (-5517444397422729 / 17679149038000046080 : k) * a ^ 2 * b ^ 2 * c * f * g + (2374167061901616973 / 36206897229824094371840 : k) * a ^ 2 * b * c ^ 4 * e + (53302011639263244667 / 47521552614144123863040 : k) * a ^ 2 * b * c ^ 2 * e * g + (-5739269784201860943 / 126724140304384330301440 : k) * a ^ 2 * b * c ^ 2 * f ^ 2 + (-5075495466190697 / 24597076922434846720 : k) * a ^ 2 * b * c * e ^ 3 + (-3628918144084783397 / 3394396615296008847360 : k) * a ^ 2 * b * e * g ^ 2 + (-32501677550374507 / 2262931076864005898240 : k) * a ^ 2 * b * f ^ 2 * g + (-264385747798202591 / 5760188195653833195520 : k) * a ^ 2 * c ^ 3 * e * f + (-21354708922773867943 / 7920258769024020643840 : k) * a ^ 2 * c * e * f * g + (443040232851336821 / 31681035076096082575360 : k) * a ^ 2 * c * f ^ 3 + (19221821880687971 / 56573276921600147456 : k) * a ^ 2 * e ^ 3 * f + (-3209138585083892881 / 2172413833789445662310400 : k) * a * b ^ 5 * c ^ 3 + (40057955713983264877 / 789968666832525695385600 : k) * a * b ^ 5 * c * g + (427898561568687411 / 5793103556771855099494400 : k) * a * b ^ 5 * e ^ 2 + (-6809808644246157083 / 2896551778385927549747200 : k) * a * b ^ 4 * c ^ 2 * f + (32003672774575470157 / 543103458447361415577600 : k) * a * b ^ 4 * f * g + (16103903524805110941 / 362068972298240943718400 : k) * a * b ^ 3 * c ^ 3 * e + (619045567594421123263 / 3801724209131529909043200 : k) * a * b ^ 3 * c * e * g + (-6259708814295207739 / 1086206916894722831155200 : k) * a * b ^ 3 * c * f ^ 2 + (-182477314780590068313 / 2534482806087686606028800 : k) * a * b ^ 3 * e ^ 3 + (113654874230182063151 / 3801724209131529909043200 : k) * a * b ^ 2 * c ^ 2 * e * f + (-92515396378280877011 / 237607763070720619315200 : k) * a * b ^ 2 * e * f * g + (-1271161192515843 / 491941538448696934400 : k) * a * b ^ 2 * f ^ 3 + (-332790132131941991 / 8485991538240022118400 : k) * a * b * c ^ 6 + (90935839570540307157 / 158405175380480412876800 : k) * a * b * c ^ 4 * g + (23981099760996451 / 265187235570000691200 : k) * a * b * c ^ 3 * e ^ 2 + (43044990667467391517 / 11314655384320029491200 : k) * a * b * c ^ 2 * g ^ 2 + (-9038876797962059011771 / 950431052282882477260800 : k) * a * b * c * e ^ 2 * g + (2158631432329372703 / 39601293845120103219200 : k) * a * b * c * e * f ^ 2 + (18836291318599539321 / 57601881956538331955200 : k) * a * b * e ^ 4 + (-39236884294734983 / 4821586101272739840 : k) * a * b * g ^ 3 + (7699498317983910683 / 67887932305920176947200 : k) * a * c ^ 5 * f + (-9553187953139430739 / 4242995769120011059200 : k) * a * c ^ 3 * f * g + (-74499705872346521549 / 86402822934807497932800 : k) * a * c ^ 2 * e ^ 2 * f + (-406084292698804917581 / 59401940767680154828800 : k) * a * c * f * g ^ 2 + (723719793479131801129 / 39601293845120103219200 : k) * a * e ^ 2 * f * g + (-7593916019022592613 / 59401940767680154828800 : k) * a * e * f ^ 3 + (-2374152805951617103 / 2828663846080007372800 : k) * b ^ 5 * e * g + (-3702591441552067441 / 11314655384320029491200 : k) * b ^ 3 * c ^ 5 + (-42145848947236570753 / 90517243074560235929600 : k) * b ^ 3 * c ^ 3 * g + (1232208736556349361407 / 1267241403043843303014400 : k) * b ^ 3 * c ^ 2 * e ^ 2 + (13632611675358897473 / 707165961520001843200 : k) * b ^ 3 * c * g ^ 2 + (7585728324527695099 / 1414331923040003686400 : k) * b ^ 3 * e ^ 2 * g + (-28353859424960451799 / 316810350760960825753600 : k) * b ^ 3 * e * f ^ 2 + (148867360065733113419 / 1900862104565764954521600 : k) * b ^ 2 * c ^ 4 * f + (1213973677415910278237 / 67887932305920176947200 : k) * b ^ 2 * c ^ 2 * f * g + (-20932477702993810381 / 12672414030438433030144 : k) * b ^ 2 * c * e ^ 2 * f + (-72466810766392489 / 2008994208863641600 : k) * b ^ 2 * f * g ^ 2 + (5991278941459031967 / 5657327692160014745600 : k) * b * c ^ 5 * e + (-332549421201453473387 / 47521552614144123863040 : k) * b * c ^ 3 * e * g + (182844983271486359851 / 158405175380480412876800 : k) * b * c ^ 3 * f ^ 2 + (-476530797224981005587 / 158405175380480412876800 : k) * b * c ^ 2 * e ^ 3 + (-808823309323625749 / 9223903845913067520 : k) * b * c * e * g ^ 2 + (-43546087972631211823 / 1080035286685093724160 : k) * b * c * f ^ 2 * g + (-506973307104750177 / 88395745190000230400 : k) * b * e ^ 3 * g + (3819654579208171717 / 5657327692160014745600 : k) * b * e ^ 2 * f ^ 2 + (-1975359933463338363 / 3443590769140878540800 : k) * c ^ 4 * e * f + (53677244930666933651 / 59401940767680154828800 : k) * c ^ 2 * e * f * g + (-1609337079315090527 / 1350044108356367155200 : k) * c ^ 2 * f ^ 3 + (126812030160469858051 / 39601293845120103219200 : k) * c * e ^ 3 * f + (15090957581837012201 / 132593617785000345600 : k) * e * f * g ^ 2 + (576510237277031377 / 22098936297500057600 : k) * f ^ 3 * g) * kappaQuarticInnerABCEFG810 a b c e f g +
      ((-81948791364153 / 9838830768973938688 : k) * a ^ 2 * b ^ 2 * c ^ 3 * e + (-816341113229379 / 12857562936727306240 : k) * a ^ 2 * b ^ 2 * c * e * g + (374616509467839 / 565732769216001474560 : k) * a ^ 2 * b ^ 2 * c * f ^ 2 + (11555715503564031 / 1131465538432002949120 : k) * a ^ 2 * b ^ 2 * e ^ 3 + (-1123849528403517 / 282866384608000737280 : k) * a ^ 2 * b * c ^ 2 * e * f + (1 / 163840 : k) * a ^ 2 * b * e * f * g + (591413969273409 / 14143319230400036864 : k) * a * b ^ 2 * c ^ 5 + (3774731460933031 / 56573276921600147456 : k) * a * b ^ 2 * c ^ 3 * g + (-920604513621923 / 25715125873454612480 : k) * a * b ^ 2 * c ^ 2 * e ^ 2 + (-3448140610361679 / 7071659615200018432 : k) * a * b ^ 2 * c * g ^ 2 + (35435282441712757 / 56573276921600147456 : k) * a * b ^ 2 * e ^ 2 * g + (-91369400498588293 / 28800940978269165977600 : k) * a * b ^ 2 * e * f ^ 2 + (-54511081979149899 / 565732769216001474560 : k) * a * b * c ^ 4 * f + (-14431441961035293 / 35358298076000092160 : k) * a * b * c ^ 2 * f * g + (1453169847543985 / 14143319230400036864 : k) * a * b * c * e ^ 2 * f + (13 / 163840 : k) * a * b * f * g ^ 2 + (-2681013836456493 / 141433192304000368640 : k) * a * c ^ 5 * e + (133092155575549 / 768658653826088960 : k) * a * c ^ 3 * e * g + (-374616509467839 / 17679149038000046080 : k) * a * c ^ 3 * f ^ 2 + (-3786558211474167 / 282866384608000737280 : k) * a * c ^ 2 * e ^ 3 + (-3213645953062139 / 8839574519000023040 : k) * a * c * e * g ^ 2 + (-143638250238289 / 768658653826088960 : k) * a * c * f ^ 2 * g + (3851905167854677 / 35358298076000092160 : k) * a * e ^ 3 * g + (3209138585083892881 / 271551729223680707788800 : k) * b ^ 4 * c ^ 4 + (-40057955713983264877 / 98746083354065711923200 : k) * b ^ 4 * c ^ 2 * g + (-427898561568687411 / 724137944596481887436800 : k) * b ^ 4 * c * e ^ 2 + (-105073052903405329 / 72413794459648188743680 : k) * b ^ 3 * c ^ 3 * f + (85161940174666915309 / 380172420913152990904320 : k) * b ^ 3 * c * f * g + (1283695684706062233 / 1267241403043843303014400 : k) * b ^ 3 * e ^ 2 * f + (2561542486403017267 / 45258621537280117964800 : k) * b ^ 2 * c ^ 4 * e + (717348840613327777333 / 950431052282882477260800 : k) * b ^ 2 * c ^ 2 * e * g + (-145577237980942180393 / 1900862104565764954521600 : k) * b ^ 2 * c ^ 2 * f ^ 2 + (1283695684706062233 / 633620701521921651507200 : k) * b ^ 2 * c * e ^ 3 + (2765387809536504083 / 1060748942280002764800 : k) * b ^ 2 * e * g ^ 2 + (3791912992301793283 / 5657327692160014745600 : k) * b ^ 2 * f ^ 2 * g + (3094541474253632133 / 45258621537280117964800 : k) * b * c ^ 3 * e * f + (13567787930481697221 / 7200235244567291494400 : k) * b * c * e * f * g + (-5920368883218428299 / 79202587690240206438400 : k) * b * c * f ^ 3 + (-80779307530043001 / 14400470489134582988800 : k) * b * e ^ 3 * f + (97322769253311 / 35358298076000092160 : k) * c ^ 7 + (-2132609932014691 / 70716596152000184320 : k) * c ^ 5 * g + (-36513629855832241 / 70716596152000184320 : k) * c ^ 4 * e ^ 2 + (925006811055719 / 8839574519000023040 : k) * c ^ 3 * g ^ 2 + (-273693930397847411 / 212149788456000552960 : k) * c ^ 2 * e ^ 2 * g + (177603302754230307 / 1584051753804804128768 : k) * c ^ 2 * e * f ^ 2 + (1713816299337 / 883957451900002304 : k) * c * e ^ 4 + (43672836878279 / 276236703718750720 : k) * c * g ^ 3 + (207854548247454241 / 26518723557000069120 : k) * e ^ 2 * g ^ 2 + (1270054023041744267 / 9900323461280025804800 : k) * e * f ^ 2 * g + (-3813483577547529 / 353582980760000921600 : k) * f ^ 4) * muQuarticInnerABCEFG810 a b c e f g +
      ((1 / 327680 : k) * a ^ 3 * e * f * g + (-15856374728279211 / 4525862153728011796480 : k) * a ^ 2 * b * c ^ 5 + (-44209855891872321 / 1131465538432002949120 : k) * a ^ 2 * b * c ^ 3 * g + (414608019111129 / 282866384608000737280 : k) * a ^ 2 * b * c ^ 2 * e ^ 2 + (11690406684127639 / 141433192304000368640 : k) * a ^ 2 * b * c * g ^ 2 + (-640895078702771 / 28286638460800073728 : k) * a ^ 2 * b * e ^ 2 * g + (20249969597298423 / 1131465538432002949120 : k) * a ^ 2 * c ^ 4 * f + (31964152607957841 / 282866384608000737280 : k) * a ^ 2 * c ^ 2 * f * g + (-24234073768852129 / 565732769216001474560 : k) * a ^ 2 * c * e ^ 2 * f + (1 / 65536 : k) * a ^ 2 * f * g ^ 2 + (-88816188795700613 / 3620689722982409437184 : k) * a * b * c ^ 4 * e + (8813210320447697987 / 23760776307072061931520 : k) * a * b * c ^ 2 * e * g + (-403643055649849 / 5492551157436907520 : k) * a * b * c * e ^ 3 + (-1885290716549172319 / 1697198307648004423680 : k) * a * b * e * g ^ 2 + (195897535609465743 / 1377436307656351416320 : k) * a * c ^ 3 * e * f + (-8050793215128828757 / 3960129384512010321920 : k) * a * c * e * f * g + (3749076189894457 / 282866384608000737280 : k) * a * e ^ 3 * f + (-3209138585083892881 / 2172413833789445662310400 : k) * b ^ 5 * c ^ 3 + (40057955713983264877 / 789968666832525695385600 : k) * b ^ 5 * c * g + (427898561568687411 / 5793103556771855099494400 : k) * b ^ 5 * e ^ 2 + (-6809808644246157083 / 2896551778385927549747200 : k) * b ^ 4 * c ^ 2 * f + (32003672774575470157 / 543103458447361415577600 : k) * b ^ 4 * f * g + (-5006105130600701859 / 362068972298240943718400 : k) * b ^ 3 * c ^ 3 * e + (-1070584614923218355777 / 3801724209131529909043200 : k) * b ^ 3 * c * e * g + (-1224862927047451579 / 1086206916894722831155200 : k) * b ^ 3 * c * f ^ 2 + (-1283695684706062233 / 2534482806087686606028800 : k) * b ^ 3 * e ^ 3 + (344483069477355817 / 165292356918762169958400 : k) * b ^ 2 * c ^ 2 * e * f + (-21345554956922120311 / 47521552614144123863040 : k) * b ^ 2 * e * f * g + (16525095502705959 / 11314655384320029491200 : k) * b ^ 2 * f ^ 3 + (-71922451314993277 / 1060748942280002764800 : k) * b * c ^ 6 + (138582816547753901557 / 158405175380480412876800 : k) * b * c ^ 4 * g + (857001925330747771 / 4242995769120011059200 : k) * b * c ^ 3 * e ^ 2 + (13071708169704755357 / 11314655384320029491200 : k) * b * c ^ 2 * g ^ 2 + (-392888291499529882171 / 950431052282882477260800 : k) * b * c * e ^ 2 * g + (-115207461449500001 / 11314655384320029491200 : k) * b * c * e * f ^ 2 + (581456501989282611 / 633620701521921651507200 : k) * b * e ^ 4 + (-36882594206222903 / 4821586101272739840 : k) * b * g ^ 3 + (1535985903646886833 / 6171630209629106995200 : k) * c ^ 5 * f + (-12975717353854570219 / 4242995769120011059200 : k) * c ^ 3 * f * g + (-214568778996688657999 / 950431052282882477260800 : k) * c ^ 2 * e ^ 2 * f + (-388266063682746883661 / 59401940767680154828800 : k) * c * f * g ^ 2 + (35442334622731017129 / 39601293845120103219200 : k) * e ^ 2 * f * g + (-62541423444630611 / 2376077630707206193152 : k) * e * f ^ 3) * nuQuarticInnerABCEFG810 a b c e f g +
      ((-1 / 163840 : k) * a ^ 2 * b ^ 2 * g ^ 2 + (-1839148132474243 / 17679149038000046080 : k) * a ^ 2 * b * c * f * g + (-374616509467839 / 35358298076000092160 : k) * a ^ 2 * c ^ 2 * f ^ 2 + (893671278818831 / 141433192304000368640 : k) * a * c ^ 6 + (-1616154045291763 / 17679149038000046080 : k) * a * c ^ 4 * g + (-2458019749274013 / 141433192304000368640 : k) * a * c ^ 3 * e ^ 2 + (1552870495336001 / 4419787259500011520 : k) * a * c ^ 2 * g ^ 2 + (41634018437507 / 441978725950001152 : k) * a * c * e ^ 2 * g + (-3851905167854677 / 70716596152000184320 : k) * a * e ^ 4 + (-1 / 10240 : k) * a * g ^ 3 + (-2374152805951617103 / 8485991538240022118400 : k) * b ^ 4 * e * g + (53822856349085851 / 13577586461184035389440 : k) * b ^ 2 * c ^ 5 + (-25068232608386666183 / 16971983076480044236800 : k) * b ^ 2 * c ^ 3 * g + (56603195859024272981 / 237607763070720619315200 : k) * b ^ 2 * c ^ 2 * e ^ 2 + (11121365158717124549 / 2121497884560005529600 : k) * b ^ 2 * c * g ^ 2 + (376608214163508057 / 176791490380000460800 : k) * b ^ 2 * e ^ 2 * g + (-294910860527931253 / 7920258769024020643840 : k) * b ^ 2 * e * f ^ 2 + (-14665335620887567367 / 59401940767680154828800 : k) * b * c ^ 4 * f + (1696590838954423537 / 168755513544545894400 : k) * b * c ^ 2 * f * g + (-14246467591079864759 / 59401940767680154828800 : k) * b * c * e ^ 2 * f + (-97606638406081841 / 8035976835454566400 : k) * b * f * g ^ 2 + (28576377964633615 / 169719830764800442368 : k) * c ^ 5 * e + (-27530214532807969 / 70716596152000184320 : k) * c ^ 3 * e * g + (14198536435612037683 / 29700970383840077414400 : k) * c ^ 3 * f ^ 2 + (-15152132515389323 / 21214978845600055296 : k) * c ^ 2 * e ^ 3 + (-17745650658500153 / 2410793050636369920 : k) * c * e * g ^ 2 + (-31089821756852938371 / 2475080865320006451200 : k) * c * f ^ 2 * g + (-207957377225414461 / 53037447114000138240 : k) * e ^ 3 * g + (1723701896372761493 / 14850485191920038707200 : k) * e ^ 2 * f ^ 2) * xiQuarticInnerABCEFG810 a b c e f g +
      ((1 / 655360 : k) * a ^ 2 * e * f * g + (12849273072003033 / 9051724307456023592960 : k) * a * b * c ^ 5 + (-14663187390035669 / 2262931076864005898240 : k) * a * b * c ^ 3 * g + (580643389217843 / 282866384608000737280 : k) * a * b * c * g ^ 2 + (-367638182738427 / 98388307689739386880 : k) * a * c ^ 4 * f + (4493703183525157 / 565732769216001474560 : k) * a * c ^ 2 * f * g + (-3064932084746533 / 1131465538432002949120 : k) * a * c * e ^ 2 * f + (9 / 655360 : k) * a * f * g ^ 2 + (-15501290294885799 / 1574212923035830190080 : k) * b * c ^ 4 * e + (-3216788215645871 / 288009409782691659776 : k) * b * c ^ 2 * e * g + (-704423896954104783 / 126724140304384330301440 : k) * b * c ^ 2 * f ^ 2 + (5785590780041139 / 1131465538432002949120 : k) * b * e * g ^ 2 + (-32501677550374507 / 2262931076864005898240 : k) * b * f ^ 2 * g + (389513905632068773 / 12672414030438433030144 : k) * c ^ 3 * e * f + (35574080173455207 / 1584051753804804128768 : k) * c * e * f * g + (-228272552115030667 / 31681035076096082575360 : k) * c * f ^ 3 + (-8569081496685 / 28286638460800073728 : k) * e ^ 3 * f) * omicronQuarticInnerABCEFG810 a b c e f g +
      ((9 / 2621440 : k) * a * c * e ^ 3 + (1 / 81920 : k) * a * e * g ^ 2 + (3813483577547529 / 2828663846080007372800 : k) * b * f ^ 3 + (32440923084437 / 35358298076000092160 : k) * c ^ 6 + (-883888233788561 / 70716596152000184320 : k) * c ^ 4 * g + (672639364449677 / 282866384608000737280 : k) * c ^ 3 * e ^ 2 + (32116062755929 / 1104946814875002880 : k) * c ^ 2 * g ^ 2 + (994844267466059 / 35358298076000092160 : k) * c * e ^ 2 * g + (76059907974711 / 44197872595000115200 : k) * c * e * f ^ 2 + (1713816299337 / 7071659615200018432 : k) * e ^ 4 + (1 / 5120 : k) * g ^ 3) * piQuarticInnerABCEFG810 a b c e f g =
      g ^ 5 := by
  simp only [kappaQuarticInnerABCEFG810, muQuarticInnerABCEFG810, nuQuarticInnerABCEFG810, xiQuarticInnerABCEFG810, omicronQuarticInnerABCEFG810, piQuarticInnerABCEFG810, primitiveQuarticInnerABCEFG810]
  ring

set_option maxHeartbeats 16000000 in
def kappaQuarticFaceABCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 16000000 in
def degreeZeroKappaQuarticNoABCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (D * E)
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
theorem degreeZeroKappaQuartic810_eq_ABCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceABCEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticFaceABCEFG810, degreeZeroKappaQuarticNoABCEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuarticNoABCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroKappaQuarticNoABCEFG810]
  compute_degree
  omega

theorem kappaQuarticFaceABCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (kappaQuarticFaceABCEFG810 A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 512 : k) * kappaQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  simp only [kappaQuarticFaceABCEFG810, kappaQuarticInnerABCEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
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
  have hdeg_CF : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    omega
  have hcf_CF : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_AB3, hcf_BC2, hcf_BG, hcf_CF]
  ring

set_option maxHeartbeats 16000000 in
def muQuarticFaceABCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 16000000 in
def degreeZeroMuQuarticNoABCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  - (15 / 64 : k) • (B * C * D)
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

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuartic810_eq_ABCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticFaceABCEFG810 A B C D E F G +
        degreeZeroMuQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticFaceABCEFG810, degreeZeroMuQuarticNoABCEFG810]
  all_goals module

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuQuarticNoABCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G) :
    (degreeZeroMuQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroMuQuarticNoABCEFG810]
  compute_degree
  omega

theorem muQuarticFaceABCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (muQuarticFaceABCEFG810 A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 2048 : k) * muQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  simp only [muQuarticFaceABCEFG810, muQuarticInnerABCEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABF : ((A * B * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    omega
  have hcf_ABF : ((A * B * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B4 : (B ^ 4).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B4 : (B ^ 4).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_CG : ((C * G)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne hGne]
    omega
  have hcf_CG : ((C * G)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_ABF, hcf_B4, hcf_B2E, hcf_C3, hcf_CG, hcf_E2]
  ring

set_option maxHeartbeats 16000000 in
def nuQuarticFaceABCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 32000000 in
def degreeZeroNuQuarticNoABCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (A * B ^ 2 * D)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
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
theorem degreeZeroNuQuartic810_eq_ABCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      nuQuarticFaceABCEFG810 A B C D E F G +
        degreeZeroNuQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticFaceABCEFG810, degreeZeroNuQuarticNoABCEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroNuQuarticNoABCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G) :
    (degreeZeroNuQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroNuQuarticNoABCEFG810]
  compute_degree
  omega

theorem nuQuarticFaceABCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (nuQuarticFaceABCEFG810 A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 4096 : k) * nuQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  simp only [nuQuarticFaceABCEFG810, nuQuarticInnerABCEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_ABC2 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC2 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_ABC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABG : ((A * B * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    omega
  have hcf_ABG : ((A * B * G)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ABG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ACF : ((A * C * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) hFne, natDegree_mul hAne hCne]
    omega
  have hcf_ACF : ((A * C * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ACF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
    omega
  have hcf_B3C : ((B ^ 3 * C)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2F : ((B ^ 2 * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hFne, natDegree_pow]
    omega
  have hcf_B2F : ((B ^ 2 * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_EF : ((E * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hEne hFne]
    omega
  have hcf_EF : ((E * F)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_EF, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A2B3, hcf_ABC2, hcf_ABG, hcf_ACF, hcf_B3C, hcf_B2F, hcf_BCE, hcf_EF]
  ring

set_option maxHeartbeats 16000000 in
def xiQuarticFaceABCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroXiQuarticNoABCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
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
theorem degreeZeroXiQuartic810_eq_ABCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticFaceABCEFG810 A B C D E F G +
        degreeZeroXiQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticFaceABCEFG810, degreeZeroXiQuarticNoABCEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroXiQuarticNoABCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G) :
    (degreeZeroXiQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroXiQuarticNoABCEFG810]
  compute_degree
  omega

theorem xiQuarticFaceABCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (xiQuarticFaceABCEFG810 A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) =
      (1 / 2048 : k) * xiQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  simp only [xiQuarticFaceABCEFG810, xiQuarticInnerABCEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB4 : ((A * B ^ 4)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 4 hBne), natDegree_pow]
  have hcf_AB4 : ((A * B ^ 4)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 4 := by
    rw [← hdeg_AB4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2C2 : ((B ^ 2 * C ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2C2 : ((B ^ 2 * C ^ 2)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B2G : ((B ^ 2 * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hGne, natDegree_pow]
    omega
  have hcf_B2G : ((B ^ 2 * G)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_B2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCF : ((B * C * F)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hFne, natDegree_mul hBne hCne]
    omega
  have hcf_BCF : ((B * C * F)).coeff (A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BCF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_EG : ((E * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hEne hGne]
    omega
  have hcf_EG : ((E * G)).coeff (A.natDegree + 4 * B.natDegree) =
      E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_EG, coeff_natDegree, leadingCoeff_mul]
  have hdeg_F2 : (F ^ 2).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_F2 : (F ^ 2).coeff (A.natDegree + 4 * B.natDegree) =
      F.leadingCoeff ^ 2 := by
    rw [← hdeg_F2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB4, hcf_AB2E, hcf_B2C2, hcf_B2G, hcf_BCF, hcf_C2E, hcf_EG, hcf_F2]
  ring

set_option maxHeartbeats 16000000 in
def omicronQuarticFaceABCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * C * F)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 32000000 in
def degreeZeroOmicronQuarticNoABCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 16384 : k)) • (A ^ 2 * B ^ 2 * D)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  - (5 / 128 : k) • (A * D * G)
  - (5 / 32 : k) • (B * D * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
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
theorem degreeZeroOmicronQuartic810_eq_ABCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticFaceABCEFG810 A B C D E F G +
        degreeZeroOmicronQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticFaceABCEFG810, degreeZeroOmicronQuarticNoABCEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronQuarticNoABCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroOmicronQuarticNoABCEFG810]
  compute_degree
  omega

theorem omicronQuarticFaceABCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (omicronQuarticFaceABCEFG810 A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * omicronQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  simp only [omicronQuarticFaceABCEFG810, omicronQuarticInnerABCEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
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
  have hdeg_A2CF : ((A ^ 2 * C * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hCne, natDegree_pow]
    omega
  have hcf_A2CF : ((A ^ 2 * C * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A2CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB3C : ((A * B ^ 3 * C)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3C : ((A * B ^ 3 * C)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_AB3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2F : ((A * B ^ 2 * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hFne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2F : ((A * B ^ 2 * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_AB2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCE : ((A * B * C * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCE : ((A * B * C * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ABCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AEF : ((A * E * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hEne) hFne, natDegree_mul hAne hEne]
    omega
  have hcf_AEF : ((A * E * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_AEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
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
  have hdeg_C2F : ((C ^ 2 * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hFne, natDegree_pow]
    omega
  have hcf_C2F : ((C ^ 2 * F)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_C2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_FG : ((F * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hFne hGne]
    omega
  have hcf_FG : ((F * G)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_FG, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_A3B3, hcf_A2BC2, hcf_A2BG, hcf_A2CF, hcf_AB3C, hcf_AB2F, hcf_ABCE, hcf_AEF, hcf_B5, hcf_B3E, hcf_BC3, hcf_BCG, hcf_BE2, hcf_C2F, hcf_FG]
  ring

set_option maxHeartbeats 16000000 in
def piQuarticFaceABCEFG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (C * E ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 32000000 in
def degreeZeroPiQuarticNoABCEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)
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
theorem degreeZeroPiQuartic810_eq_ABCEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceABCEFG810 A B C D E F G +
        degreeZeroPiQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceABCEFG810, degreeZeroPiQuarticNoABCEFG810]
  all_goals module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoABCEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G) :
    (degreeZeroPiQuarticNoABCEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  simp only [degreeZeroPiQuarticNoABCEFG810]
  compute_degree
  omega

theorem piQuarticFaceABCEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceABCEFG810 A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) =
      (1 / 4096 : k) * piQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
  simp only [piQuarticFaceABCEFG810, piQuarticInnerABCEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B4 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B4 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hdeg_A2B4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2C2 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_AB2C2 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_AB2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2G : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2G : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_AB2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCF : ((A * B * C * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCF : ((A * B * C * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABCF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AF2 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne), natDegree_pow]
    omega
  have hcf_AF2 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_AF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4C : ((B ^ 4 * C)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hCne, natDegree_pow]
    omega
  have hcf_B4C : ((B ^ 4 * C)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 4 * C.leadingCoeff := by
    rw [← hdeg_B4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3F : ((B ^ 3 * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hFne, natDegree_pow]
    omega
  have hcf_B3F : ((B ^ 3 * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * F.leadingCoeff := by
    rw [← hdeg_B3F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CE : ((B ^ 2 * C * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CE : ((B ^ 2 * C * E)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2CE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BEF : ((B * E * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hEne) hFne, natDegree_mul hBne hEne]
    omega
  have hcf_BEF : ((B * E * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C4 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C2G : ((C ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow]
    omega
  have hcf_C2G : ((C ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_C2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CE2 : ((C * E ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_CE2 : ((C * E ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_CE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_G2 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_G2 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A2B4, hcf_AB2C2, hcf_AB2G, hcf_ABCF, hcf_AF2, hcf_B4C, hcf_B3F, hcf_B2CE, hcf_BEF, hcf_C4, hcf_C2G, hcf_CE2, hcf_G2]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_ABCEFG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCEFG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoABCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceABCEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ABCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoABCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceABCEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ABCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoABCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceABCEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ABCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoABCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceABCEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_ABCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoABCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceABCEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_ABCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerABCEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoABCEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceABCEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hEpos, hFpos, hGpos, hAB, hAC, hAE, hAF, hAG, hDlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_ABCEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_ABCEFG_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff
  have hpow : G.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner] at hid
    simpa using hid.symm
  have hlc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)



end QuarticKills810

end Max11DegreeRoutes
