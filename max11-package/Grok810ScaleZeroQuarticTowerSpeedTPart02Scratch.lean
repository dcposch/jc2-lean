import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]



/-! ## Family (b) — the 19 deep-rescue scalar certificates -/

section QuarticRescueCertificates810

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEF1Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 16 * e ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEF1Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 3410 : k) * b ^ 2 * c * e * f + (-9 / 1364 : k) * b ^ 2 * d * e ^ 2
  + (-681 / 13640 : k) * b * c ^ 2 * d * f + (-27 / 1705 : k) * b * c * d ^ 2 * e
  + (-16 / 1705 : k) * b * e * f ^ 2 + (-9 / 1705 : k) * c ^ 2 * d ^ 3 + (1143 / 27280 : k) * c * d * f ^ 2
  + (3369 / 54560 : k) * d ^ 2 * e * f

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEF1Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-8 : k) * a * d * f + (-12 : k) * c ^ 2 * e

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEF1Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 2728 : k) * b ^ 3 * e ^ 2 + (1059 / 109120 : k) * b ^ 2 * c ^ 2 * f
  + (3 / 682 : k) * b ^ 2 * c * d * e + (9 / 2728 : k) * b * c ^ 2 * d ^ 2
  + (-549 / 13640 : k) * b * c * f ^ 2 + (-189 / 109120 : k) * b * d * e * f
  + (131 / 109120 : k) * c * d ^ 2 * f + (-3 / 682 : k) * d ^ 3 * e + (131 / 6820 : k) * f ^ 3

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEF1Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 128 * a * b * c * f + 256 * a * b * d * e
  + 128 * a * c * d ^ 2 + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-512 : k) * c * e ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEF1Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 27280 : k) * b ^ 2 * e * f + (-741 / 436480 : k) * b * c * d * f + (-27 / 54560 : k) * b * d ^ 2 * e
  + (-9 / 54560 : k) * c * d ^ 3 + (-131 / 218240 : k) * d * f ^ 2

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEF1Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * c * f + 32 * d * e

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEF1Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (9 / 27280 : k) * a * b ^ 3 * e * f + (435 / 87296 : k) * a * b ^ 2 * c * d * f + (27 / 6820 : k) * a * b ^ 2 * d ^ 2 * e + (117 / 54560 : k) * a * b * c * d ^ 3 + (921 / 54560 : k) * a * b * d * f ^ 2 + (2889 / 436480 : k) * a * d ^ 3 * f + (9 / 2728 : k) * b ^ 2 * e ^ 3 + (-645 / 21824 : k) * b * c ^ 2 * e * f + (-9 / 2728 : k) * b * c * d * e ^ 2 + (-9 / 2728 : k) * c ^ 2 * d ^ 2 * e

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEF1Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (643 / 27280 : k) * c * e * f ^ 2 + (-2889 / 109120 : k) * d * e ^ 2 * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEF1Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_kappaQuarticCostChamberBCDEF1Cofactor810_chunk02 a b c d e f g (towerSpeedT_kappaQuarticCostChamberBCDEF1Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEF1Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-24 : k) * b * c * e + (-12 : k) * c ^ 2 * d + 32 * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEF1Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (1 / 27280 : k) * a * b ^ 3 * c * f + (-9 / 10912 : k) * a * b ^ 3 * d * e + (-3 / 5456 : k) * a * b ^ 2 * c * d ^ 2 + (-1097 / 218240 : k) * a * b ^ 2 * f ^ 2 + (-963 / 436480 : k) * a * b * d ^ 2 * f + (-3 / 2728 : k) * b ^ 2 * c * e ^ 2 + (215 / 21824 : k) * b * c ^ 3 * f + (3 / 2728 : k) * b * c ^ 2 * d * e + (8 / 1705 : k) * b * e ^ 2 * f + (3 / 2728 : k) * c ^ 3 * d ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEF1Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-893 / 54560 : k) * c ^ 2 * f ^ 2 + (-3017 / 109120 : k) * c * d * e * f + (-3 / 682 : k) * d ^ 2 * e ^ 2

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEF1Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_n2QuarticCostChamberBCDEF1Cofactor810_chunk02 a b c d e f g (towerSpeedT_n2QuarticCostChamberBCDEF1Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial1_chunk01 (a b c d e f g : k) : k :=
  (-9 / 2728 : k) * a * b ^ 5 * e ^ 3 + (2889 / 109120 : k) * a * b ^ 4 * c ^ 2 * e * f + (-9 / 682 : k) * a * b ^ 4 * c * d * e ^ 2 + (-999 / 10912 : k) * a * b ^ 3 * c ^ 3 * d * f + (-153 / 13640 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e + (-387 / 2728 : k) * a * b ^ 3 * c * e * f ^ 2 + (6153 / 109120 : k) * a * b ^ 3 * d * e ^ 2 * f + (27 / 6820 : k) * a * b ^ 2 * c ^ 3 * d ^ 3 + (5619 / 27280 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2 + (29841 / 109120 : k) * a * b ^ 2 * c * d ^ 2 * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial1_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (9 / 682 : k) * a * b ^ 2 * d ^ 3 * e ^ 2 + (181 / 1364 : k) * a * b ^ 2 * e * f ^ 3 + (12153 / 54560 : k) * a * b * c ^ 2 * d ^ 3 * f + (63 / 1705 : k) * a * b * c * d ^ 4 * e + (174 / 1705 : k) * a * b * c * d * f ^ 3 + (-6037 / 13640 : k) * a * b * d ^ 2 * e * f ^ 2 + (36 / 1705 : k) * a * c ^ 2 * d ^ 5 + (-2417 / 13640 : k) * a * c * d ^ 3 * f ^ 2 + (-2889 / 13640 : k) * a * d ^ 4 * e * f + (-262 / 1705 : k) * a * d * f ^ 4

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial1_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (9 / 682 : k) * b ^ 3 * c ^ 2 * e ^ 3 + (-3081 / 27280 : k) * b ^ 2 * c ^ 4 * e * f + (-9 / 341 : k) * b ^ 2 * c ^ 3 * d * e ^ 2 + (-24 / 1705 : k) * b ^ 2 * c * e ^ 3 * f + (-36 / 341 : k) * b ^ 2 * d * e ^ 4 + (681 / 3410 : k) * b * c ^ 5 * d * f + (81 / 3410 : k) * b * c ^ 4 * d ^ 2 * e + (355 / 682 : k) * b * c ^ 3 * e * f ^ 2 + (-4245 / 5456 : k) * b * c ^ 2 * d * e ^ 2 * f + (-432 / 1705 : k) * b * c * d ^ 2 * e ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial1_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-256 / 1705 : k) * b * e ^ 3 * f ^ 2 + (36 / 1705 : k) * c ^ 5 * d ^ 3 + (-1143 / 6820 : k) * c ^ 4 * d * f ^ 2 + (-7131 / 27280 : k) * c ^ 3 * d ^ 2 * e * f + (-54 / 1705 : k) * c ^ 2 * d ^ 3 * e ^ 2 + (-393 / 1705 : k) * c ^ 2 * e * f ^ 3 + (1143 / 1705 : k) * c * d * e ^ 2 * f ^ 2 + (3369 / 3410 : k) * d ^ 2 * e ^ 3 * f

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEF1810_identityPartial1 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEF1810_identityPartial1_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEF1810_identityPartial1_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEF1810_identityPartial1_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEF1810_identityPartial1_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial2_chunk01 (a b c d e f g : k) : k :=
  (-3 / 27280 : k) * a ^ 2 * b ^ 5 * c * d * f + (27 / 10912 : k) * a ^ 2 * b ^ 5 * d ^ 2 * e + (9 / 5456 : k) * a ^ 2 * b ^ 4 * c * d ^ 3 + (3291 / 218240 : k) * a ^ 2 * b ^ 4 * d * f ^ 2 + (2889 / 436480 : k) * a ^ 2 * b ^ 3 * d ^ 3 * f + (9 / 2728 : k) * a * b ^ 5 * e ^ 3 + (-2793 / 109120 : k) * a * b ^ 4 * c ^ 2 * e * f + (-9 / 2728 : k) * a * b ^ 4 * c * d * e ^ 2 + (6813 / 109120 : k) * a * b ^ 3 * c ^ 3 * d * f + (-207 / 13640 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial2_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (547 / 27280 : k) * a * b ^ 3 * c * e * f ^ 2 + (-4809 / 109120 : k) * a * b ^ 3 * d * e ^ 2 * f + (-189 / 13640 : k) * a * b ^ 2 * c ^ 3 * d ^ 3 + (-1185 / 5456 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2 + (-3081 / 13640 : k) * a * b ^ 2 * c * d ^ 2 * e * f + (48 / 1705 : k) * a * b ^ 2 * e * f ^ 3 + (-5439 / 21824 : k) * a * b * c ^ 2 * d ^ 3 * f + (-63 / 1705 : k) * a * b * c * d ^ 4 * e + (1531 / 1705 : k) * a * b * c * d * f ^ 3 + (175 / 341 : k) * a * b * d ^ 2 * e * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial2_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-36 / 1705 : k) * a * c ^ 2 * d ^ 5 + (2417 / 13640 : k) * a * c * d ^ 3 * f ^ 2 + (2889 / 13640 : k) * a * d ^ 4 * e * f + (262 / 1705 : k) * a * d * f ^ 4 + (-27 / 682 : k) * b ^ 3 * c ^ 2 * e ^ 3 + (9531 / 27280 : k) * b ^ 2 * c ^ 4 * e * f + (27 / 682 : k) * b ^ 2 * c ^ 3 * d * e ^ 2 + (276 / 1705 : k) * b ^ 2 * c * e ^ 3 * f + (36 / 341 : k) * b ^ 2 * d * e ^ 4 + (-2223 / 27280 : k) * b * c ^ 5 * d * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial2_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (27 / 1705 : k) * b * c ^ 4 * d ^ 2 * e + (-8379 / 6820 : k) * b * c ^ 3 * e * f ^ 2 + (3699 / 27280 : k) * b * c ^ 2 * d * e ^ 2 * f + (252 / 1705 : k) * b * c * d ^ 2 * e ^ 3 + (-27 / 3410 : k) * c ^ 5 * d ^ 3 + (-393 / 13640 : k) * c ^ 4 * d * f ^ 2 + (-36 / 341 : k) * c ^ 3 * d ^ 2 * e * f + (-36 / 1705 : k) * c ^ 2 * d ^ 3 * e ^ 2 + (1286 / 1705 : k) * c ^ 2 * e * f ^ 3 + (731 / 3410 : k) * c * d * e ^ 2 * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial2_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (-2889 / 3410 : k) * d ^ 2 * e ^ 3 * f

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEF1810_identityPartial2 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEF1810_identityPartial2_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCDEF1810_identityPartial2_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEF1810_identityPartial2_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEF1810_identityPartial2_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEF1810_identityPartial2_chunk01 a b c d e f g))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial3_chunk01 (a b c d e f g : k) : k :=
  (3 / 27280 : k) * a ^ 2 * b ^ 5 * c * d * f + (-27 / 10912 : k) * a ^ 2 * b ^ 5 * d ^ 2 * e + (-9 / 5456 : k) * a ^ 2 * b ^ 4 * c * d ^ 3 + (-3291 / 218240 : k) * a ^ 2 * b ^ 4 * d * f ^ 2 + (-2889 / 436480 : k) * a ^ 2 * b ^ 3 * d ^ 3 * f + (-3 / 3410 : k) * a * b ^ 4 * c ^ 2 * e * f + (45 / 2728 : k) * a * b ^ 4 * c * d * e ^ 2 + (3177 / 109120 : k) * a * b ^ 3 * c ^ 3 * d * f + (9 / 341 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e + (3323 / 27280 : k) * a * b ^ 3 * c * e * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial3_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-21 / 1705 : k) * a * b ^ 3 * d * e ^ 2 * f + (27 / 2728 : k) * a * b ^ 2 * c ^ 3 * d ^ 3 + (153 / 13640 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2 + (-5193 / 109120 : k) * a * b ^ 2 * c * d ^ 2 * e * f + (-9 / 682 : k) * a * b ^ 2 * d ^ 3 * e ^ 2 + (-1097 / 6820 : k) * a * b ^ 2 * e * f ^ 3 + (2889 / 109120 : k) * a * b * c ^ 2 * d ^ 3 * f + (-963 / 13640 : k) * a * b * d ^ 2 * e * f ^ 2 + (9 / 341 : k) * b ^ 3 * c ^ 2 * e ^ 3 + (-645 / 2728 : k) * b ^ 2 * c ^ 4 * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial3_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-9 / 682 : k) * b ^ 2 * c ^ 3 * d * e ^ 2 + (-252 / 1705 : k) * b ^ 2 * c * e ^ 3 * f + (-645 / 5456 : k) * b * c ^ 5 * d * f + (-27 / 682 : k) * b * c ^ 4 * d ^ 2 * e + (439 / 620 : k) * b * c ^ 3 * e * f ^ 2 + (8763 / 13640 : k) * b * c ^ 2 * d * e ^ 2 * f + (36 / 341 : k) * b * c * d ^ 2 * e ^ 3 + (256 / 1705 : k) * b * e ^ 3 * f ^ 2 + (-9 / 682 : k) * c ^ 5 * d ^ 3 + (2679 / 13640 : k) * c ^ 4 * d * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEF1810_identityPartial3_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (10011 / 27280 : k) * c ^ 3 * d ^ 2 * e * f + (18 / 341 : k) * c ^ 2 * d ^ 3 * e ^ 2 + (-893 / 1705 : k) * c ^ 2 * e * f ^ 3 + (-3017 / 3410 : k) * c * d * e ^ 2 * f ^ 2 + (-48 / 341 : k) * d ^ 2 * e ^ 3 * f

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEF1810_identityPartial3 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEF1810_identityPartial3_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEF1810_identityPartial3_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEF1810_identityPartial3_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEF1810_identityPartial3_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #1: `BCDEF` / `BF·CF·DD·DE·EE·BBB·BBC·BCC·CCC`, target `a*b*c*d*f^3`, 47 cofactor terms. -/
theorem quarticCostChamberBCDEF1810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * muQuarticCostChamberBCDEF1Face810 a b c d e f g + xiQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEF1Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * piQuarticCostChamberBCDEF1Face810 a b c d e f g + kappaQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEF1Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEF1Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEF1Face810 a b c d e f g)) =
      a * b * c * d * f ^ 3 := by
  have h1 : muQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * muQuarticCostChamberBCDEF1Face810 a b c d e f g + xiQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEF1Face810 a b c d e f g = quarticCostChamberBCDEF1810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEF1Cofactor810, muQuarticCostChamberBCDEF1Face810, xiQuarticCostChamberBCDEF1Cofactor810, xiQuarticCostChamberBCDEF1Face810, quarticCostChamberBCDEF1810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * piQuarticCostChamberBCDEF1Face810 a b c d e f g + kappaQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEF1Face810 a b c d e f g = quarticCostChamberBCDEF1810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEF1Cofactor810, piQuarticCostChamberBCDEF1Face810, kappaQuarticCostChamberBCDEF1Cofactor810, kappaQuarticCostChamberBCDEF1Face810, quarticCostChamberBCDEF1810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEF1Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEF1Face810 a b c d e f g = quarticCostChamberBCDEF1810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEF1Cofactor810, n2QuarticCostChamberBCDEF1Face810, quarticCostChamberBCDEF1810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEF1810_identityPartial1, quarticCostChamberBCDEF1810_identityPartial2, quarticCostChamberBCDEF1810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEF1810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEF1Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEF1Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEF1Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEF1Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEF1Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEF1810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * c * d * f ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact (hc hRll).elim
    ·
      exact (hd hRl).elim
  ·
    exact hf ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG2Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticCostChamberBCDEFG2Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (-69 / 917504 : k) * a ^ 2 * b ^ 3 * c * d + (347 / 229376 : k) * a ^ 2 * b ^ 2 * d * f + (-87 / 458752 : k) * a * b ^ 2 * c ^ 2 * e + (-577 / 28672 : k) * a * b ^ 2 * e * g + (2253 / 458752 : k) * a * b * c ^ 3 * d + (719 / 57344 : k) * a * b * c * d * g + (-1047 / 114688 : k) * a * b * c * e * f + (297 / 114688 : k) * a * c ^ 2 * d * f + (143 / 6144 : k) * a * d * f * g + (-81 / 2048 : k) * a * e * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticCostChamberBCDEFG2Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (7 / 2048 : k) * c ^ 2 * e * g + (13 / 384 : k) * e * g ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG2Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_muQuarticCostChamberBCDEFG2Cofactor810_chunk02 a b c d e f g (towerSpeedT_muQuarticCostChamberBCDEFG2Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG2Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-8 : k) * a * d * f + (-12 : k) * c ^ 2 * e + 32 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG2Cofactor810 (a b c d e f g : k) : k :=
  (69 / 917504 : k) * a ^ 2 * b ^ 4 * c + (127 / 65536 : k) * a ^ 2 * b ^ 3 * f
  + (-275 / 229376 : k) * a * b ^ 2 * c ^ 3 + (543 / 57344 : k) * a * b ^ 2 * c * g
  + (-1921 / 114688 : k) * a * b * c ^ 2 * f + (433 / 10752 : k) * a * b * f * g
  + (331 / 3584 : k) * a * c * f ^ 2 + (-5 / 768 : k) * c ^ 3 * g + (7 / 768 : k) * c * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG2Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG2Cofactor810 (a b c d e f g : k) : k :=
  (63 / 262144 : k) * a * b ^ 2 * c * e + (1 / 262144 : k) * a * b * c ^ 2 * d
  + (1 / 512 : k) * a * b * d * g + (65 / 65536 : k) * a * b * e * f + (85 / 65536 : k) * a * c * d * f
  + (-11 / 8192 : k) * c * e * g

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG2Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEFG2Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (-1737 / 1835008 : k) * a ^ 2 * b ^ 3 * c * e + (1581 / 1835008 : k) * a ^ 2 * b ^ 2 * c ^ 2 * d + (-9 / 1024 : k) * a ^ 2 * b ^ 2 * e * f + (-6513 / 458752 : k) * a ^ 2 * b * c * d * f + (1919 / 57344 : k) * a ^ 2 * d * f ^ 2 + (255 / 114688 : k) * a * b * c ^ 3 * e + (93 / 57344 : k) * a * b * c * e * g + (-93 / 57344 : k) * a * c ^ 4 * d + (65 / 7168 : k) * a * c ^ 2 * d * g + (3405 / 114688 : k) * a * c ^ 2 * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEFG2Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-1 / 16 : k) * a * d * g ^ 2 + (-911 / 14336 : k) * a * e * f * g

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG2Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_kappaQuarticCostChamberBCDEFG2Cofactor810_chunk02 a b c d e f g (towerSpeedT_kappaQuarticCostChamberBCDEFG2Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def n4QuarticCostChamberBCDEFG2Face810 (a b c d e f g : k) : k :=
  3 * a ^ 3 * b ^ 2 * d + (-24 : k) * a ^ 2 * b * c * e + (-12 : k) * a ^ 2 * c ^ 2 * d + 32 * a ^ 2 * d * g
  + 32 * a ^ 2 * e * f

set_option maxHeartbeats 64000000 in
def n4QuarticCostChamberBCDEFG2Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 8192 : k) * b ^ 3 * c ^ 2 + (-1 / 512 : k) * b ^ 3 * g + (-1 / 512 : k) * b ^ 2 * c * f
  + (-1 / 512 : k) * b * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial1_chunk01 (a b c d e f g : k) : k :=
  (207 / 917504 : k) * a ^ 3 * b ^ 6 * c * e + (207 / 917504 : k) * a ^ 3 * b ^ 5 * c ^ 2 * d + (381 / 65536 : k) * a ^ 3 * b ^ 5 * e * f + (927 / 57344 : k) * a ^ 3 * b ^ 4 * c * d * f + (-1583 / 57344 : k) * a ^ 3 * b ^ 3 * d * f ^ 2 + (-2325 / 458752 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e + (-1695 / 57344 : k) * a ^ 2 * b ^ 4 * c * e * g + (3597 / 458752 : k) * a ^ 2 * b ^ 3 * c ^ 4 * d + (5277 / 57344 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d * g + (-11397 / 114688 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial1_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (4929 / 14336 : k) * a ^ 2 * b ^ 3 * e * f * g + (-2105 / 16384 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d * f + (2635 / 14336 : k) * a ^ 2 * b ^ 2 * c * d * f * g + (237 / 1024 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2 + (299 / 448 : k) * a ^ 2 * b * c ^ 2 * d * f ^ 2 + (-911 / 1792 : k) * a ^ 2 * b * d * f ^ 2 * g + (81 / 256 : k) * a ^ 2 * b * e * f ^ 3 + (-331 / 448 : k) * a ^ 2 * c * d * f ^ 3 + (1737 / 114688 : k) * a * b ^ 2 * c ^ 5 * e + (-1245 / 14336 : k) * a * b ^ 2 * c ^ 3 * e * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial1_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-95 / 448 : k) * a * b ^ 2 * c * e * g ^ 2 + (-2253 / 114688 : k) * a * b * c ^ 6 * d + (487 / 7168 : k) * a * b * c ^ 4 * d * g + (3405 / 14336 : k) * a * b * c ^ 4 * e * f + (817 / 1792 : k) * a * b * c ^ 2 * d * g ^ 2 + (-2399 / 1792 : k) * a * b * c ^ 2 * e * f * g + (57 / 56 : k) * a * b * e * f * g ^ 2 + (-297 / 28672 : k) * a * c ^ 5 * d * f + (75 / 1792 : k) * a * c ^ 3 * d * f * g + (-3405 / 3584 : k) * a * c ^ 3 * e * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial1_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (43 / 64 : k) * a * c * d * f * g ^ 2 + (757 / 448 : k) * a * c * e * f ^ 2 * g + (33 / 512 : k) * c ^ 5 * e * g + (-11 / 32 : k) * c ^ 3 * e * g ^ 2 + (11 / 8 : k) * c * e * g ^ 3

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG2810_identityPartial1 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial1_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial1_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial1_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial1_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial2_chunk01 (a b c d e f g : k) : k :=
  (-207 / 917504 : k) * a ^ 3 * b ^ 6 * c * e + (801 / 917504 : k) * a ^ 3 * b ^ 5 * c ^ 2 * d + (3 / 512 : k) * a ^ 3 * b ^ 5 * d * g + (-381 / 65536 : k) * a ^ 3 * b ^ 5 * e * f + (-591 / 57344 : k) * a ^ 3 * b ^ 4 * c * d * f + (1919 / 57344 : k) * a ^ 3 * b ^ 3 * d * f ^ 2 + (-1707 / 458752 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e + (-993 / 57344 : k) * a ^ 2 * b ^ 4 * c * e * g + (-5613 / 458752 : k) * a ^ 2 * b ^ 3 * c ^ 4 * d + (-5949 / 57344 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial2_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (7365 / 114688 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f + (1 / 16 : k) * a ^ 2 * b ^ 3 * d * g ^ 2 + (-4033 / 14336 : k) * a ^ 2 * b ^ 3 * e * f * g + (1721 / 16384 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d * f + (-1739 / 14336 : k) * a ^ 2 * b ^ 2 * c * d * f * g + (-221 / 1024 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2 + (-619 / 896 : k) * a ^ 2 * b * c ^ 2 * d * f ^ 2 + (1023 / 1792 : k) * a ^ 2 * b * d * f ^ 2 * g + (-65 / 256 : k) * a ^ 2 * b * e * f ^ 3 + (331 / 448 : k) * a ^ 2 * c * d * f ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial2_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-1737 / 114688 : k) * a * b ^ 2 * c ^ 5 * e + (1245 / 14336 : k) * a * b ^ 2 * c ^ 3 * e * g + (95 / 448 : k) * a * b ^ 2 * c * e * g ^ 2 + (2253 / 114688 : k) * a * b * c ^ 6 * d + (-487 / 7168 : k) * a * b * c ^ 4 * d * g + (-3405 / 14336 : k) * a * b * c ^ 4 * e * f + (975 / 1792 : k) * a * b * c ^ 2 * d * g ^ 2 + (2399 / 1792 : k) * a * b * c ^ 2 * e * f * g + (-57 / 56 : k) * a * b * e * f * g ^ 2 + (297 / 28672 : k) * a * c ^ 5 * d * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial2_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-75 / 1792 : k) * a * c ^ 3 * d * f * g + (3405 / 3584 : k) * a * c ^ 3 * e * f ^ 2 + (-43 / 64 : k) * a * c * d * f * g ^ 2 + (-757 / 448 : k) * a * c * e * f ^ 2 * g + (-33 / 512 : k) * c ^ 5 * e * g + (11 / 32 : k) * c ^ 3 * e * g ^ 2 + (-11 / 8 : k) * c * e * g ^ 3

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG2810_identityPartial2 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial2_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial2_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial2_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial2_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial3_chunk01 (a b c d e f g : k) : k :=
  (-9 / 8192 : k) * a ^ 3 * b ^ 5 * c ^ 2 * d + (-3 / 512 : k) * a ^ 3 * b ^ 5 * d * g + (-3 / 512 : k) * a ^ 3 * b ^ 4 * c * d * f + (-3 / 512 : k) * a ^ 3 * b ^ 3 * d * f ^ 2 + (9 / 1024 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e + (3 / 64 : k) * a ^ 2 * b ^ 4 * c * e * g + (9 / 2048 : k) * a ^ 2 * b ^ 3 * c ^ 4 * d + (3 / 256 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d * g + (9 / 256 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f + (-1 / 16 : k) * a ^ 2 * b ^ 3 * d * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial3_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-1 / 16 : k) * a ^ 2 * b ^ 3 * e * f * g + (3 / 128 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d * f + (-1 / 16 : k) * a ^ 2 * b ^ 2 * c * d * f * g + (-1 / 64 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2 + (3 / 128 : k) * a ^ 2 * b * c ^ 2 * d * f ^ 2 + (-1 / 16 : k) * a ^ 2 * b * d * f ^ 2 * g + (-1 / 16 : k) * a ^ 2 * b * e * f ^ 3

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG2810_identityPartial3 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial3_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG2810_identityPartial3_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #2: `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`, target `a*b*c^2*d*g^2`, 43 cofactor terms. -/
theorem quarticCostChamberBCDEFG2810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG2Face810 a b c d e f g + xiQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG2Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG2Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG2Face810 a b c d e f g)) +
      (n4QuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * n4QuarticCostChamberBCDEFG2Face810 a b c d e f g)) =
      a * b * c ^ 2 * d * g ^ 2 := by
  have h1 : muQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG2Face810 a b c d e f g + xiQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG2Face810 a b c d e f g = quarticCostChamberBCDEFG2810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEFG2Cofactor810, muQuarticCostChamberBCDEFG2Face810, xiQuarticCostChamberBCDEFG2Cofactor810, xiQuarticCostChamberBCDEFG2Face810, quarticCostChamberBCDEFG2810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG2Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG2Face810 a b c d e f g = quarticCostChamberBCDEFG2810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEFG2Cofactor810, piQuarticCostChamberBCDEFG2Face810, kappaQuarticCostChamberBCDEFG2Cofactor810, kappaQuarticCostChamberBCDEFG2Face810, quarticCostChamberBCDEFG2810_identityPartial2]
    ring
  have h3 : n4QuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * n4QuarticCostChamberBCDEFG2Face810 a b c d e f g = quarticCostChamberBCDEFG2810_identityPartial3 a b c d e f g := by
    simp only [n4QuarticCostChamberBCDEFG2Cofactor810, n4QuarticCostChamberBCDEFG2Face810, quarticCostChamberBCDEFG2810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEFG2810_identityPartial1, quarticCostChamberBCDEFG2810_identityPartial2, quarticCostChamberBCDEFG2810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG2810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG2Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG2Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG2Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG2Face810 a b c d e f g = 0)
    (hn4 : n4QuarticCostChamberBCDEFG2Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG2810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn4] at hid
  have hz : a * b * c ^ 2 * d * g ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRll)
    ·
      exact (hd hRl).elim
  ·
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG3Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticCostChamberBCDEFG3Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (306375 / 10621952 : k) * a ^ 2 * b ^ 2 * d ^ 2 + (-8489786204025 / 236733513191538688 : k) * a * b ^ 6 + (24203652502940644395439437237 / 86501963629035729667428343808 : k) * a * b ^ 3 * c * d + (-86627058343584314136045208013 / 86501963629035729667428343808 : k) * a * b ^ 2 * d * f + (-41925 / 2655488 : k) * a * c ^ 2 * d ^ 2 + (102125 / 331936 : k) * a * d ^ 2 * g + (1818424565942034485326844391 / 1704472189734694180638982144 : k) * b ^ 4 * c ^ 2 + (-57356709145669456587333265 / 168949147712960409506695984 : k) * b ^ 4 * g + (-104626839732757891739784367 / 24135592530422915643813712 : k) * b ^ 3 * c * f + (83918472870072414063667556095 / 21625490907258932416857085952 : k) * b ^ 2 * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticCostChamberBCDEFG3Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-6517147829218703765241 / 12672278815014380097536 : k) * b * c ^ 3 * d + (60104648120576522411393 / 36432801593166342780416 : k) * b * c * d * g + (1509161155411064241 / 1613482895744591872 : k) * c ^ 2 * d * f + (-3535662523195187727 / 311695559405205248 : k) * d * f * g

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG3Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_muQuarticCostChamberBCDEFG3Cofactor810_chunk02 a b c d e f g (towerSpeedT_muQuarticCostChamberBCDEFG3Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG3Face810 (a b c d e f g : k) : k :=
  (-3 : k) * a * b ^ 4 + 24 * a * b * c * d + (-32 : k) * a * d * f + 36 * b ^ 2 * c ^ 2
  + (-32 : k) * b ^ 2 * g + (-80 : k) * b * c * f + 64 * f ^ 2

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG3Cofactor810 (a b c d e f g : k) : k :=
  (71741522324055 / 236733513191538688 : k) * a * b ^ 4 * c
  + (-7304570789997530201916654721 / 216254909072589324168570859520 : k) * a * b ^ 3 * f
  + (-1075 / 230912 : k) * a * b * c ^ 2 * d + (-50525 / 663872 : k) * a * b * d * g
  + (-63425 / 1327744 : k) * a * c * d * f
  + (10161435150145635422189704895 / 43250981814517864833714171904 : k) * b ^ 2 * c ^ 3
  + (-5756361821531483068344382367 / 10812745453629466208428542976 : k) * b ^ 2 * c * g
  + (-85363223735078739635607699 / 93535860325514413567720960 : k) * b * c ^ 2 * f
  + (12662968548288402181 / 17143255767286288640 : k) * b * f * g
  + (12662968548288402181 / 17143255767286288640 : k) * c * f ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG3Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG3Cofactor810 (a b c d e f g : k) : k :=
  (-134758511175 / 13925500775972864 : k) * a * b ^ 3 * d + (-1075 / 129536 : k) * a * c * d ^ 2
  + (6827421669225 / 55702003103891456 : k) * b ^ 4 * c
  + (-95296593996145079 / 24662061874247942144 : k) * b ^ 3 * f
  + (-776567937635417 / 536131779874955264 : k) * b * c ^ 2 * d
  + (-29795570675430877 / 1541378867140496384 : k) * b * d * g
  + (-2058412336941 / 130741665646592 : k) * c * d * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG3Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEFG3Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (-404275533525 / 13925500775972864 : k) * a ^ 2 * b ^ 4 * d + (80625 / 1327744 : k) * a ^ 2 * b * c * d ^ 2 + (-151575 / 1327744 : k) * a ^ 2 * d ^ 2 * f + (37406699582145 / 72841080982011904 : k) * a * b ^ 5 * c + (-77674561570759903607185217187 / 865019636290357296674283438080 : k) * a * b ^ 4 * f + (119961310791003313144938941 / 172486467854507935528271872 : k) * a * b ^ 2 * c ^ 2 * d + (709924630645330306640845 / 1369595275155422342995968 : k) * a * b ^ 2 * d * g + (-338277241374667905607843859 / 165206194860648834353377280 : k) * a * b * c * d * f + (3035389292883998949 / 4285813941821572160 : k) * a * d * f ^ 2 + (2202913219370688464780866053 / 4739833623508807105064566784 : k) * b ^ 3 * c ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEFG3Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (10104958976132890659839897 / 9978479861846648498970624 : k) * b ^ 3 * c * g + (-1303312252875391504269272559 / 620530585574144402205368320 : k) * b ^ 2 * c ^ 2 * f + (-1494851127721140434183 / 1234314415244612782080 : k) * b ^ 2 * f * g + (152547741673630055616892297 / 48926450016422924020038656 : k) * b * c * f ^ 2 + (-22575 / 713728 : k) * c ^ 4 * d + (28936180369735246397 / 246862883048922556416 : k) * c ^ 2 * d * g + (33476795979037137983 / 5445504773137997568 : k) * d * g ^ 2 + (-12662968548288402181 / 8571627883643144320 : k) * f ^ 3

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG3Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_kappaQuarticCostChamberBCDEFG3Cofactor810_chunk02 a b c d e f g (towerSpeedT_kappaQuarticCostChamberBCDEFG3Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG3Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + 7 * b ^ 3 * c + (-12 : k) * b ^ 2 * f + (-12 : k) * c ^ 2 * d + 32 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEFG3Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (134758511175 / 6962750387986432 : k) * a ^ 2 * b ^ 5 + (-433225 / 10621952 : k) * a ^ 2 * b ^ 2 * c * d + (76325 / 663872 : k) * a ^ 2 * b * d * f + (-148217539479813251853480729 / 350920744945378213660966912 : k) * a * b ^ 3 * c ^ 2 + (-15964966090082343775487 / 69640437719767237779456 : k) * a * b ^ 3 * g + (393184403423561718068756079 / 175460372472689106830483456 : k) * a * b ^ 2 * c * f + (-53411281163041567780899 / 19022156599380865874944 : k) * a * b * f ^ 2 + (-3225 / 115456 : k) * a * c ^ 3 * d + (-13975 / 331936 : k) * a * c * d * g + (357111649996001035995 / 1810325545002054299648 : k) * b * c ^ 4

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEFG3Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-648744782492956030092913907 / 394785838063550490368587776 : k) * b * c ^ 2 * g + (-709924630645330306640845 / 128399557045820844655872 : k) * b * g ^ 2 + (-12592848312077406207 / 27429209227658061824 : k) * c ^ 3 * f + (131906475228771548681 / 23143395285836489664 : k) * c * f * g

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG3Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_n2QuarticCostChamberBCDEFG3Cofactor810_chunk02 a b c d e f g (towerSpeedT_n2QuarticCostChamberBCDEFG3Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial1_chunk01 (a b c d e f g : k) : k :=
  (919125 / 10621952 : k) * a ^ 3 * b ^ 4 * c * d ^ 2 + (-306375 / 1327744 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f + (-15043370349015 / 14795844574471168 : k) * a ^ 2 * b ^ 8 * c + (21975755396139435971852270913 / 216254909072589324168570859520 : k) * a ^ 2 * b ^ 7 * f + (398118802790466194565788913 / 462577345609816736189456384 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d + (151575 / 663872 : k) * a ^ 2 * b ^ 5 * d * g + (-20273364047907900355616031 / 3424653924961626126049280 : k) * a ^ 2 * b ^ 4 * c * d * f + (15207242368958553231 / 1672512757784028160 : k) * a ^ 2 * b ^ 3 * d * f ^ 2 + (-364425 / 1327744 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2 + (3225 / 165968 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial1_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-289175 / 331936 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f + (-1075 / 41492 : k) * a ^ 2 * b * d ^ 2 * f * g + (63425 / 41492 : k) * a ^ 2 * c * d ^ 2 * f ^ 2 + (45651084107159531250336307461 / 18210939711375943087879651328 : k) * a * b ^ 6 * c ^ 3 + (87142350193274227539 / 153477295770989425664 : k) * a * b ^ 6 * c * g + (-105712157500132227807472458537 / 5274509977380227418745630720 : k) * a * b ^ 5 * c ^ 2 * f + (21366563471104860432053675553 / 13515931817036832760535678720 : k) * a * b ^ 5 * f * g + (389482770919523749602714308541 / 8317496502791897083406571520 : k) * a * b ^ 4 * c * f ^ 2 + (7146387902934472338125782377 / 2544175400853992049042010112 : k) * a * b ^ 3 * c ^ 4 * d + (-66545120632391553582681257 / 45431703586678429447178752 : k) * a * b ^ 3 * c ^ 2 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial1_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (50525 / 20746 : k) * a * b ^ 3 * d * g ^ 2 + (-81322818830239985319 / 2449036538183755520 : k) * a * b ^ 3 * f ^ 3 + (-5736622049976496092151038979 / 289110841006135460118410240 : k) * a * b ^ 2 * c ^ 3 * d * f + (-9480398995258144761969591 / 256966649245918718592640 : k) * a * b ^ 2 * c * d * f * g + (34165560315753049348025344349 / 795054812766872515325628160 : k) * a * b * c ^ 2 * d * f ^ 2 + (133371853726969312261 / 2142906970910786080 : k) * a * b * d * f ^ 2 * g + (41925 / 663872 : k) * a * c ^ 5 * d ^ 2 + (-72025 / 41492 : k) * a * c ^ 3 * d ^ 2 * g + (102125 / 10373 : k) * a * c * d ^ 2 * g ^ 2 + (-1300072803345640971 / 48702431157063320 : k) * a * c * d * f ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial1_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (362483143924252749876309341067 / 86501963629035729667428343808 : k) * b ^ 4 * c ^ 5 + (95302997651225907569791322841 / 10812745453629466208428542976 : k) * b ^ 4 * c ^ 3 * g + (29602276306665925073 / 4796165492843419552 : k) * b ^ 4 * c * g ^ 2 + (-66247321088877544520293841499 / 1930847402433833251505096960 : k) * b ^ 3 * c ^ 4 * f + (-4466366059525506282488141 / 110735496960713383697120 : k) * b ^ 3 * c ^ 2 * f * g + (-12662968548288402181 / 535726742727696520 : k) * b ^ 3 * f * g ^ 2 + (22514989088246482852509668739 / 227158517933392147235893760 : k) * b ^ 2 * c ^ 3 * f ^ 2 + (34095289019550827906752641 / 4622411702132979740265280 : k) * b ^ 2 * c * f ^ 2 * g + (6517147829218703765241 / 3168069703753595024384 : k) * b * c ^ 6 * d + (-6562470256018959656623 / 284631262446612052972 : k) * b * c ^ 4 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial1_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (60104648120576522411393 / 1138525049786448211888 : k) * b * c ^ 2 * d * g ^ 2 + (-5838709603278819518951144461 / 49690925797929532207851760 : k) * b * c ^ 2 * f ^ 3 + (12662968548288402181 / 267863371363848260 : k) * b * f ^ 3 * g + (-1509161155411064241 / 403370723936147968 : k) * c ^ 5 * d * f + (32274013698567578547 / 428581394182157216 : k) * c ^ 3 * d * f * g + (-3535662523195187727 / 9740486231412664 : k) * c * d * f * g ^ 2 + (12662968548288402181 / 267863371363848260 : k) * c * f ^ 4

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG3810_identityPartial1 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial1_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial1_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial1_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial1_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial1_chunk01 a b c d e f g))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial2_chunk01 (a b c d e f g : k) : k :=
  (-404275533525 / 6962750387986432 : k) * a ^ 3 * b ^ 7 * d + (190275 / 5310976 : k) * a ^ 3 * b ^ 4 * c * d ^ 2 + (-151575 / 1327744 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f + (104310699962295 / 118366756595769344 : k) * a ^ 2 * b ^ 8 * c + (-21925530089258656389769451163 / 216254909072589324168570859520 : k) * a ^ 2 * b ^ 7 * f + (7044131506046122708369531537 / 10176701603415968196168040448 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d + (628379294481695956874533 / 1369595275155422342995968 : k) * a ^ 2 * b ^ 5 * d * g + (-3810822752374450789365119719 / 1817268143467137177887150080 : k) * a ^ 2 * b ^ 4 * c * d * f + (1056202824840943267347 / 1486105984326630146480 : k) * a ^ 2 * b ^ 3 * d * f ^ 2 + (-87075 / 663872 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial2_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (117175 / 82984 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g + (747125 / 331936 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f + (-151575 / 41492 : k) * a ^ 2 * b * d ^ 2 * f * g + (-63425 / 41492 : k) * a ^ 2 * c * d ^ 2 * f ^ 2 + (155626859453639970536334149799 / 346007854516142918669713375232 : k) * a * b ^ 6 * c ^ 3 + (10347213948186673629137837 / 9978479861846648498970624 : k) * a * b ^ 6 * c * g + (-44019624995593251425232075003 / 61787116877882664048163102720 : k) * a * b ^ 5 * c ^ 2 * f + (-4215502734257277845144973117101 / 973147090826651958758568867840 : k) * a * b ^ 5 * f * g + (-661758235232847097126742823 / 2350596837745536132267074560 : k) * a * b ^ 4 * c * f ^ 2 + (-513401819752361576574050265 / 62053058557414440220536832 : k) * a * b ^ 3 * c ^ 4 * d

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial2_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (49956985392305014269906269557 / 2862197325960741055172261376 : k) * a * b ^ 3 * c ^ 2 * d * g + (689750356046346517189867 / 32099889261455211163968 : k) * a * b ^ 3 * d * g ^ 2 + (-5802984711411749625657 / 11888847874613041171840 : k) * a * b ^ 3 * f ^ 3 + (151934614432978587766505530199 / 3180219251067490061302512640 : k) * a * b ^ 2 * c ^ 3 * d * f + (-5138060070301936480675711793 / 98020456368518529286721280 : k) * a * b ^ 2 * c * d * f * g + (-30079600313357745180524257067 / 397527406383436257662814080 : k) * a * b * c ^ 2 * d * f ^ 2 + (446030677695116319557 / 16153325916593805940 : k) * a * b * d * f ^ 2 * g + (-3225 / 8096 : k) * a * c ^ 5 * d ^ 2 + (1075 / 506 : k) * a * c ^ 3 * d ^ 2 * g + (-2150 / 253 : k) * a * c * d ^ 2 * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial2_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (1300072803345640971 / 48702431157063320 : k) * a * c * d * f ^ 3 + (-481929070825741485105660543957 / 86501963629035729667428343808 : k) * b ^ 4 * c ^ 5 + (47578571514647720326763825629 / 17693583469575490159246706688 : k) * b ^ 4 * c ^ 3 * g + (10144097124616423428348197 / 311827495682707765592832 : k) * b ^ 4 * c * g ^ 2 + (616185350475785252973327994947 / 15446779219470666012040775680 : k) * b ^ 3 * c ^ 4 * f + (-14073502449611371011668000966051 / 729860318119988969068926650880 : k) * b ^ 3 * c ^ 2 * f * g + (-175772958624644502907757 / 4115370418135283482560 : k) * b ^ 3 * f * g ^ 2 + (-1808317652048889402615960279 / 17283800277540706854904960 : k) * b ^ 2 * c ^ 3 * f ^ 2 + (109153969120539636339947328713 / 1788873328725463159482663360 : k) * b ^ 2 * c * f ^ 2 * g + (425930971681404159 / 1373837685929572864 : k) * b * c ^ 6 * d

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial2_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (-4994646827546302311415 / 1678425582298311694848 : k) * b * c ^ 4 * d * g + (-356067772626052476285271 / 5349981543575868527328 : k) * b * c ^ 2 * d * g ^ 2 + (5838709603278819518951144461 / 49690925797929532207851760 : k) * b * c ^ 2 * f ^ 3 + (709924630645330306640845 / 4012486157681901395496 : k) * b * d * g ^ 3 + (-12662968548288402181 / 267863371363848260 : k) * b * f ^ 3 * g + (-10068775161332331 / 5695433809729664 : k) * c ^ 5 * d * f + (60029289149566436741 / 7714465095278829888 : k) * c ^ 3 * d * f * g + (30733286380816738835 / 170172024160562424 : k) * c * d * f * g ^ 2 + (-12662968548288402181 / 267863371363848260 : k) * c * f ^ 4

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG3810_identityPartial2 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial2_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial2_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial2_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial2_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial2_chunk01 a b c d e f g))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial3_chunk01 (a b c d e f g : k) : k :=
  (404275533525 / 6962750387986432 : k) * a ^ 3 * b ^ 7 * d + (-1299675 / 10621952 : k) * a ^ 3 * b ^ 4 * c * d ^ 2 + (228975 / 663872 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f + (943309578225 / 6962750387986432 : k) * a ^ 2 * b ^ 8 * c + (-404275533525 / 1740687596996608 : k) * a ^ 2 * b ^ 7 * f + (-544922247152978585821271987 / 350920744945378213660966912 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d + (-941084761547159090791333 / 1369595275155422342995968 : k) * a ^ 2 * b ^ 5 * d * g + (1406636827897586915813677037 / 175460372472689106830483456 : k) * a ^ 2 * b ^ 4 * c * d * f + (-186477446517077283139497 / 19022156599380865874944 : k) * a ^ 2 * b ^ 3 * d * f ^ 2 + (538575 / 1327744 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial3_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-237575 / 165968 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g + (-228975 / 165968 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f + (76325 / 20746 : k) * a ^ 2 * b * d ^ 2 * f * g + (-148217539479813251853480729 / 50131534992196887665852416 : k) * a * b ^ 6 * c ^ 3 + (-15964966090082343775487 / 9948633959966748254208 : k) * a * b ^ 6 * c * g + (3641596060843811537602176927 / 175460372472689106830483456 : k) * a * b ^ 5 * c ^ 2 * f + (15964966090082343775487 / 5803369809980603148288 : k) * a * b ^ 5 * f * g + (-2041718110804502141325539895 / 43865093118172276707620864 : k) * a * b ^ 4 * c * f ^ 2 + (59927097874622208195733959 / 10966273279543069176905216 : k) * a * b ^ 3 * c ^ 4 * d + (-789045565387316317141333627 / 49348229757943811296073472 : k) * a * b ^ 3 * c ^ 2 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial3_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-767926722812712300669067 / 32099889261455211163968 : k) * a * b ^ 3 * d * g ^ 2 + (160233843489124703342697 / 4755539149845216468736 : k) * a * b ^ 3 * f ^ 3 + (-1902586675588715586910347 / 68113498630702293024256 : k) * a * b ^ 2 * c ^ 3 * d * f + (4407376383131032152628497875 / 49348229757943811296073472 : k) * a * b ^ 2 * c * d * f * g + (160233843489124703342697 / 4755539149845216468736 : k) * a * b * c ^ 2 * d * f ^ 2 + (-53411281163041567780899 / 594442393730652058592 : k) * a * b * d * f ^ 2 * g + (9675 / 28864 : k) * a * c ^ 5 * d ^ 2 + (-16125 / 41492 : k) * a * c ^ 3 * d ^ 2 * g + (-13975 / 10373 : k) * a * c * d ^ 2 * g ^ 2 + (2499781549972007251965 / 1810325545002054299648 : k) * b ^ 4 * c ^ 5

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial3_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-648744782492956030092913907 / 56397976866221498624083968 : k) * b ^ 4 * c ^ 3 * g + (-709924630645330306640845 / 18342793863688692093696 : k) * b ^ 4 * c * g ^ 2 + (-34972325259539511890862987 / 6266441874024610958231552 : k) * b ^ 3 * c ^ 4 * f + (1357822697479463614657454143 / 22776106042127912905880064 : k) * b ^ 3 * c ^ 2 * f * g + (709924630645330306640845 / 10699963087151737054656 : k) * b ^ 3 * f * g ^ 2 + (37778544936232218621 / 6857302306914515456 : k) * b ^ 2 * c ^ 3 * f ^ 2 + (-131906475228771548681 / 1928616273819707472 : k) * b ^ 2 * c * f ^ 2 * g + (-1071334949988003107985 / 452581386250513574912 : k) * b * c ^ 6 * d + (856416634538430504557158247 / 32898819838629207530715648 : k) * b * c ^ 4 * d * g + (84899158320554906731990189 / 6168528719742976412009184 : k) * b * c ^ 2 * d * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial3_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (-709924630645330306640845 / 4012486157681901395496 : k) * b * d * g ^ 3 + (37778544936232218621 / 6857302306914515456 : k) * c ^ 5 * d * f + (-640961535723782850587 / 7714465095278829888 : k) * c ^ 3 * d * f * g + (131906475228771548681 / 723231102682390302 : k) * c * d * f * g ^ 2

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG3810_identityPartial3 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial3_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial3_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial3_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial3_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG3810_identityPartial3_chunk01 a b c d e f g))))

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #3: `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`, target `a*b*c^2*d*f^2`, 63 cofactor terms. -/
theorem quarticCostChamberBCDEFG3810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG3Face810 a b c d e f g + xiQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG3Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG3Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG3Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG3Face810 a b c d e f g)) =
      a * b * c ^ 2 * d * f ^ 2 := by
  have h1 : muQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG3Face810 a b c d e f g + xiQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG3Face810 a b c d e f g = quarticCostChamberBCDEFG3810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEFG3Cofactor810, muQuarticCostChamberBCDEFG3Face810, xiQuarticCostChamberBCDEFG3Cofactor810, xiQuarticCostChamberBCDEFG3Face810, quarticCostChamberBCDEFG3810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG3Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG3Face810 a b c d e f g = quarticCostChamberBCDEFG3810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEFG3Cofactor810, piQuarticCostChamberBCDEFG3Face810, kappaQuarticCostChamberBCDEFG3Cofactor810, kappaQuarticCostChamberBCDEFG3Face810, quarticCostChamberBCDEFG3810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG3Face810 a b c d e f g = quarticCostChamberBCDEFG3810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEFG3Cofactor810, n2QuarticCostChamberBCDEFG3Face810, quarticCostChamberBCDEFG3810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEFG3810_identityPartial1, quarticCostChamberBCDEFG3810_identityPartial2, quarticCostChamberBCDEFG3810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG3810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG3Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG3Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG3Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG3Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG3Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG3810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * c ^ 2 * d * f ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRll)
    ·
      exact (hd hRl).elim
  ·
    exact hf ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG4Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticCostChamberBCDEFG4Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (19327 / 678912 : k) * a * b ^ 4 * e + (553 / 3328 : k) * a * b ^ 2 * e ^ 2 + (35 / 2048 : k) * b ^ 4 * g + (-11741171 / 88833024 : k) * b ^ 3 * c * f + (-312863 / 1584128 : k) * b ^ 2 * c ^ 2 * e + (7657 / 4352 : k) * b ^ 2 * e * g + (223531 / 2115072 : k) * b ^ 2 * f ^ 2 + (37859449 / 24058944 : k) * b * c * e * f + (-291 / 208 : k) * c ^ 2 * e ^ 2 + (74 / 39 : k) * e ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticCostChamberBCDEFG4Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (866251 / 1288872 : k) * e * f ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG4Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_muQuarticCostChamberBCDEFG4Cofactor810_chunk02 a b c d e f g (towerSpeedT_muQuarticCostChamberBCDEFG4Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG4Face810 (a b c d e f g : k) : k :=
  (-3 : k) * a * b ^ 4 + 12 * a * b ^ 2 * e + 36 * b ^ 2 * c ^ 2 + (-32 : k) * b ^ 2 * g
  + (-80 : k) * b * c * f + (-48 : k) * c ^ 2 * e + 128 * e * g + 64 * f ^ 2

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG4Cofactor810 (a b c d e f g : k) : k :=
  (1985773 / 157925376 : k) * a * b ^ 3 * f + (-1023 / 23296 : k) * a * b ^ 2 * c * e
  + (7531 / 104832 : k) * a * b * e * f + (281 / 4608 : k) * b ^ 2 * c * g
  + (-172531 / 1880064 : k) * b * c ^ 2 * f + (7495 / 705024 : k) * b * f * g + (217 / 1248 : k) * c ^ 3 * e
  + (-97 / 104 : k) * c * e * g + (7495 / 705024 : k) * c * f ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG4Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG4Cofactor810 (a b c d e f g : k) : k :=
  (667 / 86016 : k) * b ^ 3 * f + (-1375 / 86016 : k) * b ^ 2 * c * e + (-131 / 5376 : k) * b * e * f
  + (11 / 192 : k) * c * e ^ 2

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG4Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEFG4Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (761161 / 52641792 : k) * a * b ^ 4 * f + (-551023 / 19009536 : k) * a * b ^ 3 * c * e + (21407735 / 171085824 : k) * a * b ^ 2 * e * f + (-2077 / 3328 : k) * a * b * c * e ^ 2 + (461 / 416 : k) * a * e ^ 2 * f + (713615 / 2506752 : k) * b ^ 3 * c * g + (-41495 / 626688 : k) * b ^ 2 * c ^ 2 * f + (-25674133 / 39481344 : k) * b ^ 2 * f * g + (29619 / 56576 : k) * b * c ^ 3 * e + (-92673097 / 28514304 : k) * b * c * e * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEFG4Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (285029 / 1410048 : k) * b * c * f ^ 2 + (-224453 / 470016 : k) * c ^ 2 * e * f + (9070715 / 4935168 : k) * e * f * g + (-7495 / 352512 : k) * f ^ 3

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG4Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_kappaQuarticCostChamberBCDEFG4Cofactor810_chunk02 a b c d e f g (towerSpeedT_kappaQuarticCostChamberBCDEFG4Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG4Face810 (a b c d e f g : k) : k :=
  7 * b ^ 3 * c + (-12 : k) * b ^ 2 * f + (-24 : k) * b * c * e + 32 * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEFG4Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (-5599 / 279552 : k) * a ^ 2 * b ^ 3 * e + (-383543 / 17547264 : k) * a * b ^ 3 * g + (1973693 / 29611008 : k) * a * b ^ 2 * c * f + (7853 / 69888 : k) * a * b * c ^ 2 * e + (-12071 / 13104 : k) * a * b * e * g + (-947143 / 5552064 : k) * a * b * f ^ 2 + (-811 / 1248 : k) * a * c * e * f + (269303 / 1462272 : k) * b * c ^ 2 * g + (-201197 / 182784 : k) * b * g ^ 2 + (728893 / 3172608 : k) * c ^ 3 * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEFG4Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-30523639 / 44416512 : k) * c * f * g

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG4Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_n2QuarticCostChamberBCDEFG4Cofactor810_chunk02 a b c d e f g (towerSpeedT_n2QuarticCostChamberBCDEFG4Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial1_chunk01 (a b c d e f g : k) : k :=
  (-1985773 / 52641792 : k) * a ^ 2 * b ^ 7 * f + (343981 / 1584128 : k) * a ^ 2 * b ^ 6 * c * e + (-50019959 / 171085824 : k) * a ^ 2 * b ^ 5 * e * f + (-51 / 1792 : k) * a ^ 2 * b ^ 4 * c * e ^ 2 + (-157 / 336 : k) * a ^ 2 * b ^ 3 * e ^ 2 * f + (-809 / 6144 : k) * a * b ^ 6 * c * g + (19629773 / 59222016 : k) * a * b ^ 5 * c ^ 2 * f + (-1408949 / 2467584 : k) * a * b ^ 5 * f * g + (-13348843 / 4752384 : k) * a * b ^ 4 * c ^ 3 * e + (13216729 / 1188096 : k) * a * b ^ 4 * c * e * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial1_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (29901379 / 88833024 : k) * a * b ^ 4 * c * f ^ 2 + (343089769 / 32078592 : k) * a * b ^ 3 * c ^ 2 * e * f + (-58692395 / 4009824 : k) * a * b ^ 3 * e * f * g + (-301549 / 7402752 : k) * a * b ^ 3 * f ^ 3 + (-299 / 448 : k) * a * b ^ 2 * c ^ 3 * e ^ 2 + (-325 / 56 : k) * a * b ^ 2 * c * e ^ 2 * g + (-304787801 / 16039296 : k) * a * b ^ 2 * c * e * f ^ 2 + (1301 / 168 : k) * a * b * c ^ 2 * e ^ 2 * f + (-377 / 63 : k) * a * b * e ^ 2 * f * g + (-135179 / 173502 : k) * a * b * e * f ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial1_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (1089 / 512 : k) * b ^ 4 * c ^ 3 * g + (-809 / 576 : k) * b ^ 4 * c * g ^ 2 + (-246510547 / 88833024 : k) * b ^ 3 * c ^ 4 * f + (-4017365 / 694008 : k) * b ^ 3 * c ^ 2 * f * g + (-7495 / 22032 : k) * b ^ 3 * f * g ^ 2 + (2791871 / 396032 : k) * b ^ 2 * c ^ 5 * e + (-16462777 / 297024 : k) * b ^ 2 * c ^ 3 * e * g + (7721563 / 1057536 : k) * b ^ 2 * c ^ 3 * f ^ 2 + (1494983 / 15912 : k) * b ^ 2 * c * e * g ^ 2 + (805583 / 132192 : k) * b ^ 2 * c * f ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial1_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-1520506837 / 96235776 : k) * b * c ^ 4 * e * f + (677946785 / 6014736 : k) * b * c ^ 2 * e * f * g + (-592543 / 88128 : k) * b * c ^ 2 * f ^ 3 + (7495 / 5508 : k) * b * e * f * g ^ 2 + (7495 / 11016 : k) * b * f ^ 3 * g + (-11 / 4 : k) * c ^ 5 * e ^ 2 + (44 / 3 : k) * c ^ 3 * e ^ 2 * g + (3144659 / 396576 : k) * c ^ 3 * e * f ^ 2 + (-176 / 3 : k) * c * e ^ 2 * g ^ 2 + (-1825457 / 49572 : k) * c * e * f ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial1_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (7495 / 11016 : k) * c * f ^ 4

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG4810_identityPartial1 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial1_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial1_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial1_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial1_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial1_chunk01 a b c d e f g))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial2_chunk01 (a b c d e f g : k) : k :=
  (1985773 / 52641792 : k) * a ^ 2 * b ^ 7 * f + (-182831 / 2376192 : k) * a ^ 2 * b ^ 6 * c * e + (8900903 / 171085824 : k) * a ^ 2 * b ^ 5 * e * f + (-1505 / 3328 : k) * a ^ 2 * b ^ 4 * c * e ^ 2 + (461 / 416 : k) * a ^ 2 * b ^ 3 * e ^ 2 * f + (713615 / 2506752 : k) * a * b ^ 6 * c * g + (-583475 / 731136 : k) * a * b ^ 5 * c ^ 2 * f + (12187523 / 39481344 : k) * a * b ^ 5 * f * g + (3203605 / 1584128 : k) * a * b ^ 4 * c ^ 3 * e + (-148294201 / 28514304 : k) * a * b ^ 4 * c * e * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial2_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (16359065 / 9870336 : k) * a * b ^ 4 * c * f ^ 2 + (-34199273 / 10692864 : k) * a * b ^ 3 * c ^ 2 * e * f + (274757459 / 64157184 : k) * a * b ^ 3 * e * f * g + (-4950913 / 2467584 : k) * a * b ^ 3 * f ^ 3 + (2799 / 832 : k) * a * b ^ 2 * c ^ 3 * e ^ 2 + (-5087 / 312 : k) * a * b ^ 2 * c * e ^ 2 * g + (26610959 / 5346432 : k) * a * b ^ 2 * c * e * f ^ 2 + (-2023 / 78 : k) * a * b * c ^ 2 * e ^ 2 * f + (461 / 13 : k) * a * b * e ^ 2 * f * g + (131 / 21 : k) * a * b * e * f ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial2_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (811 / 39 : k) * a * c * e ^ 2 * f ^ 2 + (-713615 / 208896 : k) * b ^ 4 * c ^ 3 * g + (713615 / 78336 : k) * b ^ 4 * c * g ^ 2 + (426533 / 365568 : k) * b ^ 3 * c ^ 4 * f + (42143539 / 3290112 : k) * b ^ 3 * c ^ 2 * f * g + (-15877237 / 1233792 : k) * b ^ 3 * f * g ^ 2 + (-2791871 / 396032 : k) * b ^ 2 * c ^ 5 * e + (142205033 / 2376192 : k) * b ^ 2 * c ^ 3 * e * g + (-533999 / 117504 : k) * b ^ 2 * c ^ 3 * f ^ 2 + (-107259097 / 891072 : k) * b ^ 2 * c * e * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial2_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-17693321 / 1233792 : k) * b ^ 2 * c * f ^ 2 * g + (75968183 / 3564288 : k) * b * c ^ 4 * e * f + (-722307217 / 5346432 : k) * b * c ^ 2 * e * f * g + (592543 / 88128 : k) * b * c ^ 2 * f ^ 3 + (5222459 / 154224 : k) * b * e * f * g ^ 2 + (-7495 / 11016 : k) * b * f ^ 3 * g + (11 / 4 : k) * c ^ 5 * e ^ 2 + (-44 / 3 : k) * c ^ 3 * e ^ 2 * g + (-224453 / 14688 : k) * c ^ 3 * e * f ^ 2 + (176 / 3 : k) * c * e ^ 2 * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial2_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (9070715 / 154224 : k) * c * e * f ^ 2 * g + (-7495 / 11016 : k) * c * f ^ 4

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG4810_identityPartial2 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial2_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial2_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial2_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial2_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial2_chunk01 a b c d e f g))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial3_chunk01 (a b c d e f g : k) : k :=
  (-5599 / 39936 : k) * a ^ 2 * b ^ 6 * c * e + (5599 / 23296 : k) * a ^ 2 * b ^ 5 * e * f + (5599 / 11648 : k) * a ^ 2 * b ^ 4 * c * e ^ 2 + (-5599 / 8736 : k) * a ^ 2 * b ^ 3 * e ^ 2 * f + (-383543 / 2506752 : k) * a * b ^ 6 * c * g + (1973693 / 4230144 : k) * a * b ^ 5 * c ^ 2 * f + (383543 / 1462272 : k) * a * b ^ 5 * f * g + (7853 / 9984 : k) * a * b ^ 4 * c ^ 3 * e + (-168907295 / 28514304 : k) * a * b ^ 4 * c * e * g + (-44283241 / 22208256 : k) * a * b ^ 4 * c * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial3_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-120245975 / 16039296 : k) * a * b ^ 3 * c ^ 2 * e * f + (73813429 / 7128576 : k) * a * b ^ 3 * e * f * g + (947143 / 462672 : k) * a * b ^ 3 * f ^ 3 + (-7853 / 2912 : k) * a * b ^ 2 * c ^ 3 * e ^ 2 + (12071 / 546 : k) * a * b ^ 2 * c * e ^ 2 * g + (56238731 / 4009824 : k) * a * b ^ 2 * c * e * f ^ 2 + (41915 / 2184 : k) * a * b * c ^ 2 * e ^ 2 * f + (-24142 / 819 : k) * a * b * e ^ 2 * f * g + (-947143 / 173502 : k) * a * b * e * f ^ 3 + (-811 / 39 : k) * a * c * e ^ 2 * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial3_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (269303 / 208896 : k) * b ^ 4 * c ^ 3 * g + (-201197 / 26112 : k) * b ^ 4 * c * g ^ 2 + (5102251 / 3172608 : k) * b ^ 3 * c ^ 4 * f + (-623652833 / 88833024 : k) * b ^ 3 * c ^ 2 * f * g + (201197 / 15232 : k) * b ^ 3 * f * g ^ 2 + (-269303 / 60928 : k) * b ^ 2 * c ^ 3 * e * g + (-728893 / 264384 : k) * b ^ 2 * c ^ 3 * f ^ 2 + (201197 / 7616 : k) * b ^ 2 * c * e * g ^ 2 + (30523639 / 3701376 : k) * b ^ 2 * c * f ^ 2 * g + (-728893 / 132192 : k) * b * c ^ 4 * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial3_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (82860821 / 3701376 : k) * b * c ^ 2 * e * f * g + (-201197 / 5712 : k) * b * e * f * g ^ 2 + (728893 / 99144 : k) * c ^ 3 * e * f ^ 2 + (-30523639 / 1388016 : k) * c * e * f ^ 2 * g

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG4810_identityPartial3 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial3_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial3_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial3_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG4810_identityPartial3_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #4: `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`, target `a*b*c^2*e^2*f`, 49 cofactor terms. -/
theorem quarticCostChamberBCDEFG4810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG4Face810 a b c d e f g + xiQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG4Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG4Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG4Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG4Face810 a b c d e f g)) =
      a * b * c ^ 2 * e ^ 2 * f := by
  have h1 : muQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG4Face810 a b c d e f g + xiQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG4Face810 a b c d e f g = quarticCostChamberBCDEFG4810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEFG4Cofactor810, muQuarticCostChamberBCDEFG4Face810, xiQuarticCostChamberBCDEFG4Cofactor810, xiQuarticCostChamberBCDEFG4Face810, quarticCostChamberBCDEFG4810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG4Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG4Face810 a b c d e f g = quarticCostChamberBCDEFG4810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEFG4Cofactor810, piQuarticCostChamberBCDEFG4Face810, kappaQuarticCostChamberBCDEFG4Cofactor810, kappaQuarticCostChamberBCDEFG4Face810, quarticCostChamberBCDEFG4810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG4Face810 a b c d e f g = quarticCostChamberBCDEFG4810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEFG4Cofactor810, n2QuarticCostChamberBCDEFG4Face810, quarticCostChamberBCDEFG4810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEFG4810_identityPartial1, quarticCostChamberBCDEFG4810_identityPartial2, quarticCostChamberBCDEFG4810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG4810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG4Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG4Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG4Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG4Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG4Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG4810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * c ^ 2 * e ^ 2 * f = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRll)
    ·
      exact he ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRl)
  ·
    exact (hf hR).elim

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG5Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 32 * c * g

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG5Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 44 : k) * c * d

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG5Face810 (a b c d e f g : k) : k :=
  3 * a * b * c * d + (-4 : k) * a * d * f

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG5Cofactor810 (a b c d e f g : k) : k :=
  (2 / 11 : k) * b * c + (-4 / 11 : k) * f

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG5Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + 128 * a * c * d ^ 2 + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG5Cofactor810 (a b c d e f g : k) : k :=
  (1 / 176 : k) * d

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG5Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG5Cofactor810 (a b c d e f g : k) : k :=
  (3 / 176 : k) * a * b * d

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG5Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-12 : k) * c ^ 2 * d + 32 * d * g

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG5Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 88 : k) * a * b ^ 2 + (1 / 22 : k) * c ^ 2 + (-2 / 11 : k) * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #5: `BCDEFG` / `BF·BG·CF·CG·DD·BBB·BBC·BCC·CCC`, target `a*c*d^3`, 8 cofactor terms. -/
theorem quarticCostChamberBCDEFG5810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDEFG5Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG5Face810 a b c d e f g +
      xiQuarticCostChamberBCDEFG5Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG5Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG5Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG5Face810 a b c d e f g +
      kappaQuarticCostChamberBCDEFG5Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG5Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG5Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG5Face810 a b c d e f g =
      a * c * d ^ 3 := by
  simp only [muQuarticCostChamberBCDEFG5Face810, xiQuarticCostChamberBCDEFG5Face810, piQuarticCostChamberBCDEFG5Face810, kappaQuarticCostChamberBCDEFG5Face810, n2QuarticCostChamberBCDEFG5Face810, muQuarticCostChamberBCDEFG5Cofactor810, xiQuarticCostChamberBCDEFG5Cofactor810, piQuarticCostChamberBCDEFG5Cofactor810, kappaQuarticCostChamberBCDEFG5Cofactor810, n2QuarticCostChamberBCDEFG5Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG5810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG5Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG5Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG5Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG5Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG5Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG5810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * c * d ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      exact (ha hLl).elim
    ·
      exact (hc hRl).elim
  ·
    exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG6Face810 (a b c d e f g : k) : k :=
  -a * d * f + 4 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG6Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 2 : k) * f

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG6Face810 (a b c d e f g : k) : k :=
  -a * f ^ 2 + 4 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG6Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 2 : k) * d

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG6Face810 (a b c d e f g : k) : k :=
  d * g + e * f

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG6Cofactor810 (a b c d e f g : k) : k :=
  2 * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #6: `BCDEFG` / `BF·BG·CF·CG·DD·DE·EE`, target `a*d*f^2`, 3 cofactor terms. -/
theorem quarticCostChamberBCDEFG6810_identity
    (a b c d e f g : k) :
    xiQuarticCostChamberBCDEFG6Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG6Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG6Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG6Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG6Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG6Face810 a b c d e f g =
      a * d * f ^ 2 := by
  simp only [xiQuarticCostChamberBCDEFG6Face810, piQuarticCostChamberBCDEFG6Face810, n2QuarticCostChamberBCDEFG6Face810, xiQuarticCostChamberBCDEFG6Cofactor810, piQuarticCostChamberBCDEFG6Cofactor810, n2QuarticCostChamberBCDEFG6Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG6810_impossible
    (a b c d e f g : k)
    (hxi : xiQuarticCostChamberBCDEFG6Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG6Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG6Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG6810_identity a b c d e f g
  rw [hxi, hpi, hn2] at hid
  have hz : a * d * f ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      exact (ha hLl).elim
    ·
      exact (hd hRl).elim
  ·
    exact hf ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG7Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g + 16 * e ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG7Cofactor810 (a b c d e f g : k) : k :=
  (3 / 176 : k) * c * e

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG7Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + (-12 : k) * c ^ 2 * e + 32 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG7Cofactor810 (a b c d e f g : k) : k :=
  (1 / 352 : k) * a * b ^ 2 + (-1 / 88 : k) * c ^ 2 + (1 / 22 : k) * g

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG7Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + (-512 : k) * c * e ^ 2 + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG7Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 704 : k) * e

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG7Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG7Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 704 : k) * a * b * e

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG7Face810 (a b c d e f g : k) : k :=
  (-3 : k) * b * c * e + 4 * e * f

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG7Cofactor810 (a b c d e f g : k) : k :=
  (1 / 22 : k) * a * b * c + (-1 / 11 : k) * a * f

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #7: `BCDEFG` / `BF·BG·CF·CG·EE·BBB·BBC·BCC·CCC`, target `c*e^3`, 8 cofactor terms. -/
theorem quarticCostChamberBCDEFG7810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDEFG7Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG7Face810 a b c d e f g +
      xiQuarticCostChamberBCDEFG7Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG7Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG7Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG7Face810 a b c d e f g +
      kappaQuarticCostChamberBCDEFG7Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG7Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG7Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG7Face810 a b c d e f g =
      c * e ^ 3 := by
  simp only [muQuarticCostChamberBCDEFG7Face810, xiQuarticCostChamberBCDEFG7Face810, piQuarticCostChamberBCDEFG7Face810, kappaQuarticCostChamberBCDEFG7Face810, n2QuarticCostChamberBCDEFG7Face810, muQuarticCostChamberBCDEFG7Cofactor810, xiQuarticCostChamberBCDEFG7Cofactor810, piQuarticCostChamberBCDEFG7Cofactor810, kappaQuarticCostChamberBCDEFG7Cofactor810, n2QuarticCostChamberBCDEFG7Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG7810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG7Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG7Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG7Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG7Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG7Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG7810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : c * e ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    exact (hc hL).elim
  ·
    exact he ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG8Face810 (a b c d e f g : k) : k :=
  (-2 : k) * a * b * f - a * d ^ 2 + 4 * e ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG8Cofactor810 (a b c d e f g : k) : k :=
  (1 / 256 : k) * a * b ^ 4 + (1 / 24 : k) * b ^ 2 * g + (-1 / 3 : k) * f ^ 2

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG8Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + (-8 : k) * a * d * f + 32 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG8Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 192 : k) * b ^ 2 * e + (1 / 24 : k) * d * f

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG8Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + 64 * a * b ^ 2 * g + 256 * a * b * d * e + (-256 : k) * a * f ^ 2 + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG8Cofactor810 (a b c d e f g : k) : k :=
  (1 / 384 : k) * b * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG8Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + 32 * b * g + 32 * d * e

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG8Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 12 : k) * f * g

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG8Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + 32 * d * g + 32 * e * f

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG8Cofactor810 (a b c d e f g : k) : k :=
  (1 / 768 : k) * a * b ^ 2 * d + (1 / 24 : k) * e * f

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #8: `BCDEFG` / `BF·BG·DD·DE·EE·BBB`, target `a*b^2*d*e*f`, 9 cofactor terms. -/
theorem quarticCostChamberBCDEFG8810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDEFG8Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG8Face810 a b c d e f g +
      xiQuarticCostChamberBCDEFG8Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG8Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG8Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG8Face810 a b c d e f g +
      kappaQuarticCostChamberBCDEFG8Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG8Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG8Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG8Face810 a b c d e f g =
      a * b ^ 2 * d * e * f := by
  simp only [muQuarticCostChamberBCDEFG8Face810, xiQuarticCostChamberBCDEFG8Face810, piQuarticCostChamberBCDEFG8Face810, kappaQuarticCostChamberBCDEFG8Face810, n2QuarticCostChamberBCDEFG8Face810, muQuarticCostChamberBCDEFG8Cofactor810, xiQuarticCostChamberBCDEFG8Cofactor810, piQuarticCostChamberBCDEFG8Cofactor810, kappaQuarticCostChamberBCDEFG8Cofactor810, n2QuarticCostChamberBCDEFG8Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG8810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG8Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG8Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG8Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG8Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG8Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG8810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b ^ 2 * d * e * f = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRlll)
      ·
        exact (hd hRll).elim
    ·
      exact (he hRl).elim
  ·
    exact (hf hR).elim

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG9Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 16 * e ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG9Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 3410 : k) * b ^ 2 * c * e * f + (-9 / 1364 : k) * b ^ 2 * d * e ^ 2
  + (-681 / 13640 : k) * b * c ^ 2 * d * f + (-27 / 1705 : k) * b * c * d ^ 2 * e
  + (-16 / 1705 : k) * b * e * f ^ 2 + (-9 / 1705 : k) * c ^ 2 * d ^ 3 + (1143 / 27280 : k) * c * d * f ^ 2
  + (3369 / 54560 : k) * d ^ 2 * e * f

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG9Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-8 : k) * a * d * f + (-12 : k) * c ^ 2 * e

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG9Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 2728 : k) * b ^ 3 * e ^ 2 + (1059 / 109120 : k) * b ^ 2 * c ^ 2 * f
  + (3 / 682 : k) * b ^ 2 * c * d * e + (9 / 2728 : k) * b * c ^ 2 * d ^ 2
  + (-549 / 13640 : k) * b * c * f ^ 2 + (-189 / 109120 : k) * b * d * e * f
  + (131 / 109120 : k) * c * d ^ 2 * f + (-3 / 682 : k) * d ^ 3 * e + (131 / 6820 : k) * f ^ 3

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG9Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 128 * a * b * c * f + 256 * a * b * d * e
  + 128 * a * c * d ^ 2 + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-512 : k) * c * e ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG9Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 27280 : k) * b ^ 2 * e * f + (-741 / 436480 : k) * b * c * d * f + (-27 / 54560 : k) * b * d ^ 2 * e
  + (-9 / 54560 : k) * c * d ^ 3 + (-131 / 218240 : k) * d * f ^ 2

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG9Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * c * f + 32 * d * e

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEFG9Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (9 / 27280 : k) * a * b ^ 3 * e * f + (435 / 87296 : k) * a * b ^ 2 * c * d * f + (27 / 6820 : k) * a * b ^ 2 * d ^ 2 * e + (117 / 54560 : k) * a * b * c * d ^ 3 + (921 / 54560 : k) * a * b * d * f ^ 2 + (2889 / 436480 : k) * a * d ^ 3 * f + (9 / 2728 : k) * b ^ 2 * e ^ 3 + (-645 / 21824 : k) * b * c ^ 2 * e * f + (-9 / 2728 : k) * b * c * d * e ^ 2 + (-9 / 2728 : k) * c ^ 2 * d ^ 2 * e

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEFG9Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (643 / 27280 : k) * c * e * f ^ 2 + (-2889 / 109120 : k) * d * e ^ 2 * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG9Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_kappaQuarticCostChamberBCDEFG9Cofactor810_chunk02 a b c d e f g (towerSpeedT_kappaQuarticCostChamberBCDEFG9Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG9Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-24 : k) * b * c * e + (-12 : k) * c ^ 2 * d + 32 * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEFG9Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (1 / 27280 : k) * a * b ^ 3 * c * f + (-9 / 10912 : k) * a * b ^ 3 * d * e + (-3 / 5456 : k) * a * b ^ 2 * c * d ^ 2 + (-1097 / 218240 : k) * a * b ^ 2 * f ^ 2 + (-963 / 436480 : k) * a * b * d ^ 2 * f + (-3 / 2728 : k) * b ^ 2 * c * e ^ 2 + (215 / 21824 : k) * b * c ^ 3 * f + (3 / 2728 : k) * b * c ^ 2 * d * e + (8 / 1705 : k) * b * e ^ 2 * f + (3 / 2728 : k) * c ^ 3 * d ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEFG9Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-893 / 54560 : k) * c ^ 2 * f ^ 2 + (-3017 / 109120 : k) * c * d * e * f + (-3 / 682 : k) * d ^ 2 * e ^ 2

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG9Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_n2QuarticCostChamberBCDEFG9Cofactor810_chunk02 a b c d e f g (towerSpeedT_n2QuarticCostChamberBCDEFG9Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial1_chunk01 (a b c d e f g : k) : k :=
  (-9 / 2728 : k) * a * b ^ 5 * e ^ 3 + (2889 / 109120 : k) * a * b ^ 4 * c ^ 2 * e * f + (-9 / 682 : k) * a * b ^ 4 * c * d * e ^ 2 + (-999 / 10912 : k) * a * b ^ 3 * c ^ 3 * d * f + (-153 / 13640 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e + (-387 / 2728 : k) * a * b ^ 3 * c * e * f ^ 2 + (6153 / 109120 : k) * a * b ^ 3 * d * e ^ 2 * f + (27 / 6820 : k) * a * b ^ 2 * c ^ 3 * d ^ 3 + (5619 / 27280 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2 + (29841 / 109120 : k) * a * b ^ 2 * c * d ^ 2 * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial1_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (9 / 682 : k) * a * b ^ 2 * d ^ 3 * e ^ 2 + (181 / 1364 : k) * a * b ^ 2 * e * f ^ 3 + (12153 / 54560 : k) * a * b * c ^ 2 * d ^ 3 * f + (63 / 1705 : k) * a * b * c * d ^ 4 * e + (174 / 1705 : k) * a * b * c * d * f ^ 3 + (-6037 / 13640 : k) * a * b * d ^ 2 * e * f ^ 2 + (36 / 1705 : k) * a * c ^ 2 * d ^ 5 + (-2417 / 13640 : k) * a * c * d ^ 3 * f ^ 2 + (-2889 / 13640 : k) * a * d ^ 4 * e * f + (-262 / 1705 : k) * a * d * f ^ 4

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial1_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (9 / 682 : k) * b ^ 3 * c ^ 2 * e ^ 3 + (-3081 / 27280 : k) * b ^ 2 * c ^ 4 * e * f + (-9 / 341 : k) * b ^ 2 * c ^ 3 * d * e ^ 2 + (-24 / 1705 : k) * b ^ 2 * c * e ^ 3 * f + (-36 / 341 : k) * b ^ 2 * d * e ^ 4 + (681 / 3410 : k) * b * c ^ 5 * d * f + (81 / 3410 : k) * b * c ^ 4 * d ^ 2 * e + (355 / 682 : k) * b * c ^ 3 * e * f ^ 2 + (-4245 / 5456 : k) * b * c ^ 2 * d * e ^ 2 * f + (-432 / 1705 : k) * b * c * d ^ 2 * e ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial1_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-256 / 1705 : k) * b * e ^ 3 * f ^ 2 + (36 / 1705 : k) * c ^ 5 * d ^ 3 + (-1143 / 6820 : k) * c ^ 4 * d * f ^ 2 + (-7131 / 27280 : k) * c ^ 3 * d ^ 2 * e * f + (-54 / 1705 : k) * c ^ 2 * d ^ 3 * e ^ 2 + (-393 / 1705 : k) * c ^ 2 * e * f ^ 3 + (1143 / 1705 : k) * c * d * e ^ 2 * f ^ 2 + (3369 / 3410 : k) * d ^ 2 * e ^ 3 * f

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG9810_identityPartial1 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial1_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial1_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial1_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial1_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial2_chunk01 (a b c d e f g : k) : k :=
  (-3 / 27280 : k) * a ^ 2 * b ^ 5 * c * d * f + (27 / 10912 : k) * a ^ 2 * b ^ 5 * d ^ 2 * e + (9 / 5456 : k) * a ^ 2 * b ^ 4 * c * d ^ 3 + (3291 / 218240 : k) * a ^ 2 * b ^ 4 * d * f ^ 2 + (2889 / 436480 : k) * a ^ 2 * b ^ 3 * d ^ 3 * f + (9 / 2728 : k) * a * b ^ 5 * e ^ 3 + (-2793 / 109120 : k) * a * b ^ 4 * c ^ 2 * e * f + (-9 / 2728 : k) * a * b ^ 4 * c * d * e ^ 2 + (6813 / 109120 : k) * a * b ^ 3 * c ^ 3 * d * f + (-207 / 13640 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial2_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (547 / 27280 : k) * a * b ^ 3 * c * e * f ^ 2 + (-4809 / 109120 : k) * a * b ^ 3 * d * e ^ 2 * f + (-189 / 13640 : k) * a * b ^ 2 * c ^ 3 * d ^ 3 + (-1185 / 5456 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2 + (-3081 / 13640 : k) * a * b ^ 2 * c * d ^ 2 * e * f + (48 / 1705 : k) * a * b ^ 2 * e * f ^ 3 + (-5439 / 21824 : k) * a * b * c ^ 2 * d ^ 3 * f + (-63 / 1705 : k) * a * b * c * d ^ 4 * e + (1531 / 1705 : k) * a * b * c * d * f ^ 3 + (175 / 341 : k) * a * b * d ^ 2 * e * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial2_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-36 / 1705 : k) * a * c ^ 2 * d ^ 5 + (2417 / 13640 : k) * a * c * d ^ 3 * f ^ 2 + (2889 / 13640 : k) * a * d ^ 4 * e * f + (262 / 1705 : k) * a * d * f ^ 4 + (-27 / 682 : k) * b ^ 3 * c ^ 2 * e ^ 3 + (9531 / 27280 : k) * b ^ 2 * c ^ 4 * e * f + (27 / 682 : k) * b ^ 2 * c ^ 3 * d * e ^ 2 + (276 / 1705 : k) * b ^ 2 * c * e ^ 3 * f + (36 / 341 : k) * b ^ 2 * d * e ^ 4 + (-2223 / 27280 : k) * b * c ^ 5 * d * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial2_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (27 / 1705 : k) * b * c ^ 4 * d ^ 2 * e + (-8379 / 6820 : k) * b * c ^ 3 * e * f ^ 2 + (3699 / 27280 : k) * b * c ^ 2 * d * e ^ 2 * f + (252 / 1705 : k) * b * c * d ^ 2 * e ^ 3 + (-27 / 3410 : k) * c ^ 5 * d ^ 3 + (-393 / 13640 : k) * c ^ 4 * d * f ^ 2 + (-36 / 341 : k) * c ^ 3 * d ^ 2 * e * f + (-36 / 1705 : k) * c ^ 2 * d ^ 3 * e ^ 2 + (1286 / 1705 : k) * c ^ 2 * e * f ^ 3 + (731 / 3410 : k) * c * d * e ^ 2 * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial2_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (-2889 / 3410 : k) * d ^ 2 * e ^ 3 * f

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG9810_identityPartial2 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial2_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial2_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial2_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial2_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial2_chunk01 a b c d e f g))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial3_chunk01 (a b c d e f g : k) : k :=
  (3 / 27280 : k) * a ^ 2 * b ^ 5 * c * d * f + (-27 / 10912 : k) * a ^ 2 * b ^ 5 * d ^ 2 * e + (-9 / 5456 : k) * a ^ 2 * b ^ 4 * c * d ^ 3 + (-3291 / 218240 : k) * a ^ 2 * b ^ 4 * d * f ^ 2 + (-2889 / 436480 : k) * a ^ 2 * b ^ 3 * d ^ 3 * f + (-3 / 3410 : k) * a * b ^ 4 * c ^ 2 * e * f + (45 / 2728 : k) * a * b ^ 4 * c * d * e ^ 2 + (3177 / 109120 : k) * a * b ^ 3 * c ^ 3 * d * f + (9 / 341 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e + (3323 / 27280 : k) * a * b ^ 3 * c * e * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial3_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-21 / 1705 : k) * a * b ^ 3 * d * e ^ 2 * f + (27 / 2728 : k) * a * b ^ 2 * c ^ 3 * d ^ 3 + (153 / 13640 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2 + (-5193 / 109120 : k) * a * b ^ 2 * c * d ^ 2 * e * f + (-9 / 682 : k) * a * b ^ 2 * d ^ 3 * e ^ 2 + (-1097 / 6820 : k) * a * b ^ 2 * e * f ^ 3 + (2889 / 109120 : k) * a * b * c ^ 2 * d ^ 3 * f + (-963 / 13640 : k) * a * b * d ^ 2 * e * f ^ 2 + (9 / 341 : k) * b ^ 3 * c ^ 2 * e ^ 3 + (-645 / 2728 : k) * b ^ 2 * c ^ 4 * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial3_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-9 / 682 : k) * b ^ 2 * c ^ 3 * d * e ^ 2 + (-252 / 1705 : k) * b ^ 2 * c * e ^ 3 * f + (-645 / 5456 : k) * b * c ^ 5 * d * f + (-27 / 682 : k) * b * c ^ 4 * d ^ 2 * e + (439 / 620 : k) * b * c ^ 3 * e * f ^ 2 + (8763 / 13640 : k) * b * c ^ 2 * d * e ^ 2 * f + (36 / 341 : k) * b * c * d ^ 2 * e ^ 3 + (256 / 1705 : k) * b * e ^ 3 * f ^ 2 + (-9 / 682 : k) * c ^ 5 * d ^ 3 + (2679 / 13640 : k) * c ^ 4 * d * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial3_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (10011 / 27280 : k) * c ^ 3 * d ^ 2 * e * f + (18 / 341 : k) * c ^ 2 * d ^ 3 * e ^ 2 + (-893 / 1705 : k) * c ^ 2 * e * f ^ 3 + (-3017 / 3410 : k) * c * d * e ^ 2 * f ^ 2 + (-48 / 341 : k) * d ^ 2 * e ^ 3 * f

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG9810_identityPartial3 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial3_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial3_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial3_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG9810_identityPartial3_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #9: `BCDEFG` / `BF·CF·DD·DE·EE·BBB·BBC·BCC·CCC`, target `a*b*c*d*f^3`, 47 cofactor terms. -/
theorem quarticCostChamberBCDEFG9810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG9Face810 a b c d e f g + xiQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG9Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG9Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG9Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG9Face810 a b c d e f g)) =
      a * b * c * d * f ^ 3 := by
  have h1 : muQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG9Face810 a b c d e f g + xiQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG9Face810 a b c d e f g = quarticCostChamberBCDEFG9810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEFG9Cofactor810, muQuarticCostChamberBCDEFG9Face810, xiQuarticCostChamberBCDEFG9Cofactor810, xiQuarticCostChamberBCDEFG9Face810, quarticCostChamberBCDEFG9810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG9Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG9Face810 a b c d e f g = quarticCostChamberBCDEFG9810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEFG9Cofactor810, piQuarticCostChamberBCDEFG9Face810, kappaQuarticCostChamberBCDEFG9Cofactor810, kappaQuarticCostChamberBCDEFG9Face810, quarticCostChamberBCDEFG9810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG9Face810 a b c d e f g = quarticCostChamberBCDEFG9810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEFG9Cofactor810, n2QuarticCostChamberBCDEFG9Face810, quarticCostChamberBCDEFG9810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEFG9810_identityPartial1, quarticCostChamberBCDEFG9810_identityPartial2, quarticCostChamberBCDEFG9810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG9810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG9Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG9Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG9Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG9Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG9Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG9810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * c * d * f ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact (hc hRll).elim
    ·
      exact (hd hRl).elim
  ·
    exact hf ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG10Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 32 * c * g + 16 * e ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG10Cofactor810 (a b c d e f g : k) : k :=
  (4473 / 436480 : k) * a * b * c * d ^ 3 + (-249 / 39680 : k) * b ^ 2 * c * e * g
  + (489 / 19840 : k) * b * c ^ 2 * d * g + (34299 / 872960 : k) * b * c * d * e ^ 2
  + (-223 / 2480 : k) * b * d * g ^ 2 + (-297 / 79360 : k) * c ^ 2 * d ^ 2 * e
  + (-15 / 248 : k) * d ^ 2 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG10Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-12 : k) * c ^ 2 * e + 32 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG10Cofactor810 (a b c d e f g : k) : k :=
  (1491 / 698368 : k) * a * b ^ 3 * d * e + (-1491 / 349184 : k) * a * b ^ 2 * c * d ^ 2
  + (-21 / 39680 : k) * b ^ 2 * c ^ 2 * g + (-9 / 31744 : k) * b ^ 2 * c * e ^ 2
  + (51 / 2480 : k) * b ^ 2 * g ^ 2 + (-1293 / 174592 : k) * b * c ^ 2 * d * e
  + (3491 / 109120 : k) * b * d * e * g + (9 / 31744 : k) * c ^ 3 * d ^ 2
  + (-209 / 19840 : k) * c * d ^ 2 * g

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG10Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 256 * a * b * d * e
  + 128 * a * c * d ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + (-512 : k) * c * e ^ 2 + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG10Cofactor810 (a b c d e f g : k) : k :=
  (4473 / 13967360 : k) * a * b * d ^ 3 + (51 / 79360 : k) * b ^ 2 * e * g + (3 / 3968 : k) * b * c * d * g
  + (4473 / 3491840 : k) * b * d * e ^ 2 + (-27 / 158720 : k) * c * d ^ 2 * e

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG10Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * d * e

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEFG10Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (-4473 / 1745920 : k) * a ^ 2 * b ^ 2 * d ^ 3 + (-153 / 79360 : k) * a * b ^ 3 * e * g + (193 / 158720 : k) * a * b ^ 2 * c * d * g + (-4473 / 436480 : k) * a * b ^ 2 * d * e ^ 2 + (729 / 634880 : k) * a * b * c * d ^ 2 * e + (27 / 126976 : k) * a * c ^ 2 * d ^ 3 + (-15 / 1984 : k) * a * d ^ 3 * g + (311 / 19840 : k) * b * c ^ 2 * e * g + (27 / 31744 : k) * b * c * e ^ 3 + (-51 / 1240 : k) * b * e * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEFG10Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (1 / 19840 : k) * c ^ 3 * d * g + (-27 / 31744 : k) * c ^ 2 * d * e ^ 2 + (751 / 14880 : k) * c * d * g ^ 2 + (15 / 496 : k) * d * e ^ 2 * g

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG10Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_kappaQuarticCostChamberBCDEFG10Cofactor810_chunk02 a b c d e f g (towerSpeedT_kappaQuarticCostChamberBCDEFG10Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG10Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-24 : k) * b * c * e + (-12 : k) * c ^ 2 * d + 32 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEFG10Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (1491 / 2793472 : k) * a ^ 2 * b ^ 3 * d ^ 2 + (-553 / 476160 : k) * a * b ^ 3 * c * g + (5667 / 1396736 : k) * a * b ^ 2 * c * d * e + (-3081 / 1396736 : k) * a * b * c ^ 2 * d ^ 2 + (7561 / 436480 : k) * a * b * d ^ 2 * g + (-13 / 2480 : k) * b * c ^ 3 * g + (-9 / 31744 : k) * b * c ^ 2 * e ^ 2 + (227 / 14880 : k) * b * c * g ^ 2 + (-17 / 992 : k) * b * e ^ 2 * g + (9 / 31744 : k) * c ^ 3 * d * e

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEFG10Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (1547 / 59520 : k) * c * d * e * g

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG10Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_n2QuarticCostChamberBCDEFG10Cofactor810_chunk02 a b c d e f g (towerSpeedT_n2QuarticCostChamberBCDEFG10Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial1_chunk01 (a b c d e f g : k) : k :=
  (4473 / 698368 : k) * a ^ 2 * b ^ 5 * d * e ^ 2 + (4473 / 872960 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3 + (-4473 / 109120 : k) * a ^ 2 * b * c * d ^ 5 + (-81 / 3968 : k) * a * b ^ 4 * c ^ 2 * e * g + (-27 / 31744 : k) * a * b ^ 4 * c * e ^ 3 + (153 / 2480 : k) * a * b ^ 4 * e * g ^ 2 + (351 / 4960 : k) * a * b ^ 3 * c ^ 3 * d * g + (14913 / 218240 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (-363 / 2480 : k) * a * b ^ 3 * c * d * g ^ 2 + (2241 / 13640 : k) * a * b ^ 3 * d * e ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial1_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-567 / 158720 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e + (-28947 / 218240 : k) * a * b ^ 2 * c * d ^ 2 * e * g + (-34299 / 872960 : k) * a * b * c ^ 4 * d ^ 3 + (18129 / 109120 : k) * a * b * c ^ 2 * d ^ 3 * g + (27 / 3968 : k) * a * b * c * d ^ 3 * e ^ 2 + (223 / 620 : k) * a * b * d ^ 3 * g ^ 2 + (297 / 19840 : k) * a * c ^ 2 * d ^ 4 * e + (15 / 62 : k) * a * d ^ 4 * e * g + (39 / 1240 : k) * b ^ 2 * c ^ 4 * e * g + (27 / 7936 : k) * b ^ 2 * c ^ 3 * e ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial1_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-72 / 155 : k) * b ^ 2 * c ^ 2 * e * g ^ 2 + (-543 / 4960 : k) * b ^ 2 * c * e ^ 3 * g + (102 / 155 : k) * b ^ 2 * e * g ^ 3 + (-489 / 4960 : k) * b * c ^ 5 * d * g + (-1863 / 27280 : k) * b * c ^ 4 * d * e ^ 2 + (178 / 155 : k) * b * c ^ 3 * d * g ^ 2 + (28119 / 27280 : k) * b * c ^ 2 * d * e ^ 2 * g + (34299 / 54560 : k) * b * c * d * e ^ 4 + (-446 / 155 : k) * b * c * d * g ^ 3 + (-283 / 682 : k) * b * d * e ^ 2 * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial1_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (459 / 39680 : k) * c ^ 5 * d ^ 2 * e + (639 / 2480 : k) * c ^ 3 * d ^ 2 * e * g + (-297 / 4960 : k) * c ^ 2 * d ^ 2 * e ^ 3 + (-1409 / 620 : k) * c * d ^ 2 * e * g ^ 2 + (-30 / 31 : k) * d ^ 2 * e ^ 3 * g

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG10810_identityPartial1 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial1_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial1_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial1_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial1_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial2_chunk01 (a b c d e f g : k) : k :=
  (-4473 / 2793472 : k) * a ^ 3 * b ^ 5 * d ^ 3 + (553 / 158720 : k) * a ^ 2 * b ^ 5 * c * d * g + (-4473 / 698368 : k) * a ^ 2 * b ^ 5 * d * e ^ 2 + (81 / 126976 : k) * a ^ 2 * b ^ 4 * c * d ^ 2 * e + (55161 / 6983680 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3 + (-15069 / 218240 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g + (4473 / 109120 : k) * a ^ 2 * b * c * d ^ 5 + (-37 / 4960 : k) * a * b ^ 4 * c ^ 2 * e * g + (27 / 31744 : k) * a * b ^ 4 * c * e ^ 3 + (-153 / 2480 : k) * a * b ^ 4 * e * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial2_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-2737 / 39680 : k) * a * b ^ 3 * c ^ 3 * d * g + (52191 / 1745920 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (205 / 1488 : k) * a * b ^ 3 * c * d * g ^ 2 + (-6159 / 54560 : k) * a * b ^ 3 * d * e ^ 2 * g + (-243 / 158720 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e + (6757 / 19840 : k) * a * b ^ 2 * c * d ^ 2 * e * g + (22383 / 1745920 : k) * a * b * c ^ 4 * d ^ 3 + (24513 / 218240 : k) * a * b * c ^ 2 * d ^ 3 * g + (-27 / 3968 : k) * a * b * c * d ^ 3 * e ^ 2 + (1173 / 13640 : k) * a * b * d ^ 3 * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial2_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-297 / 19840 : k) * a * c ^ 2 * d ^ 4 * e + (-15 / 62 : k) * a * d ^ 4 * e * g + (-39 / 248 : k) * b ^ 2 * c ^ 4 * e * g + (-81 / 7936 : k) * b ^ 2 * c ^ 3 * e ^ 3 + (103 / 124 : k) * b ^ 2 * c ^ 2 * e * g ^ 2 + (-1497 / 4960 : k) * b ^ 2 * c * e ^ 3 * g + (-102 / 155 : k) * b ^ 2 * e * g ^ 3 + (177 / 4960 : k) * b * c ^ 5 * d * g + (31293 / 436480 : k) * b * c ^ 4 * d * e ^ 2 + (-989 / 1240 : k) * b * c ^ 3 * d * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial2_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-32929 / 54560 : k) * b * c ^ 2 * d * e ^ 2 * g + (-34299 / 54560 : k) * b * c * d * e ^ 4 + (1111 / 465 : k) * b * c * d * g ^ 3 + (657 / 682 : k) * b * d * e ^ 2 * g ^ 2 + (-81 / 9920 : k) * c ^ 5 * d ^ 2 * e + (7 / 155 : k) * c ^ 3 * d ^ 2 * e * g + (297 / 4960 : k) * c ^ 2 * d ^ 2 * e ^ 3 + (134 / 93 : k) * c * d ^ 2 * e * g ^ 2 + (30 / 31 : k) * d ^ 2 * e ^ 3 * g

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG10810_identityPartial2 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial2_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial2_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial2_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial2_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial3_chunk01 (a b c d e f g : k) : k :=
  (4473 / 2793472 : k) * a ^ 3 * b ^ 5 * d ^ 3 + (-553 / 158720 : k) * a ^ 2 * b ^ 5 * c * d * g + (-81 / 126976 : k) * a ^ 2 * b ^ 4 * c * d ^ 2 * e + (-18189 / 1396736 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3 + (15069 / 218240 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g + (553 / 19840 : k) * a * b ^ 4 * c ^ 2 * e * g + (-71 / 39680 : k) * a * b ^ 3 * c ^ 3 * d * g + (-34299 / 349184 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (4 / 465 : k) * a * b ^ 3 * c * d * g ^ 2 + (-51 / 992 : k) * a * b ^ 3 * d * e ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial3_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (81 / 15872 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e + (-2269 / 10912 : k) * a * b ^ 2 * c * d ^ 2 * e * g + (9243 / 349184 : k) * a * b * c ^ 4 * d ^ 3 + (-60771 / 218240 : k) * a * b * c ^ 2 * d ^ 3 * g + (7561 / 13640 : k) * a * b * d ^ 3 * g ^ 2 + (39 / 310 : k) * b ^ 2 * c ^ 4 * e * g + (27 / 3968 : k) * b ^ 2 * c ^ 3 * e ^ 3 + (-227 / 620 : k) * b ^ 2 * c ^ 2 * e * g ^ 2 + (51 / 124 : k) * b ^ 2 * c * e ^ 3 * g + (39 / 620 : k) * b * c ^ 5 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial3_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-27 / 7936 : k) * b * c ^ 4 * d * e ^ 2 + (-87 / 248 : k) * b * c ^ 3 * d * g ^ 2 + (-2119 / 4960 : k) * b * c ^ 2 * d * e ^ 2 * g + (227 / 465 : k) * b * c * d * g ^ 3 + (-17 / 31 : k) * b * d * e ^ 2 * g ^ 2 + (-27 / 7936 : k) * c ^ 5 * d ^ 2 * e + (-751 / 2480 : k) * c ^ 3 * d ^ 2 * e * g + (1547 / 1860 : k) * c * d ^ 2 * e * g ^ 2

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEFG10810_identityPartial3 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial3_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial3_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEFG10810_identityPartial3_chunk01 a b c d e f g))

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #10: `BCDEFG` / `BG·CG·DD·DE·EE·BBB·BBC·BCC·CCC`, target `a*b*d^3*g^2`, 46 cofactor terms. -/
theorem quarticCostChamberBCDEFG10810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG10Face810 a b c d e f g + xiQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG10Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG10Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG10Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG10Face810 a b c d e f g)) =
      a * b * d ^ 3 * g ^ 2 := by
  have h1 : muQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG10Face810 a b c d e f g + xiQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG10Face810 a b c d e f g = quarticCostChamberBCDEFG10810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEFG10Cofactor810, muQuarticCostChamberBCDEFG10Face810, xiQuarticCostChamberBCDEFG10Cofactor810, xiQuarticCostChamberBCDEFG10Face810, quarticCostChamberBCDEFG10810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG10Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG10Face810 a b c d e f g = quarticCostChamberBCDEFG10810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEFG10Cofactor810, piQuarticCostChamberBCDEFG10Face810, kappaQuarticCostChamberBCDEFG10Cofactor810, kappaQuarticCostChamberBCDEFG10Face810, quarticCostChamberBCDEFG10810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG10Face810 a b c d e f g = quarticCostChamberBCDEFG10810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEFG10Cofactor810, n2QuarticCostChamberBCDEFG10Face810, quarticCostChamberBCDEFG10810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEFG10810_identityPartial1, quarticCostChamberBCDEFG10810_identityPartial2, quarticCostChamberBCDEFG10810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG10810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG10Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG10Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG10Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG10Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG10Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG10810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * d ^ 3 * g ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        exact (ha hLll).elim
      ·
        exact (hb hRll).elim
    ·
      exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hRl)
  ·
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG11Face810 (a b c d e f g : k) : k :=
  -a * d ^ 2 - c ^ 3 + 8 * c * g + 4 * e ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG11Cofactor810 (a b c d e f g : k) : k :=
  (1 / 3 : k) * f * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG11Face810 (a b c d e f g : k) : k :=
  (-2 : k) * a * d * f + (-3 : k) * c ^ 2 * e + 8 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEFG11Cofactor810 (a b c d e f g : k) : k :=
  (1 / 48 : k) * c ^ 2 * d + (2 / 3 : k) * d * g + (1 / 2 : k) * e * f

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG11Face810 (a b c d e f g : k) : k :=
  8 * a * c * d ^ 2 + (-16 : k) * a * f ^ 2 + 3 * c ^ 4 + (-16 : k) * c ^ 2 * g + (-32 : k) * c * e ^ 2
  + 64 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG11Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 24 : k) * c * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG11Face810 (a b c d e f g : k) : k :=
  c * f + d * e

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEFG11Cofactor810 (a b c d e f g : k) : k :=
  a * c * d ^ 2 + (-2 / 3 : k) * a * f ^ 2 + (1 / 8 : k) * c ^ 4 + (-1 / 3 : k) * c ^ 2 * g

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG11Face810 (a b c d e f g : k) : k :=
  (-3 : k) * c ^ 2 * d + 8 * d * g + 8 * e * f

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG11Cofactor810 (a b c d e f g : k) : k :=
  (5 / 24 : k) * a * d * f + (1 / 48 : k) * c ^ 2 * e + (-2 / 3 : k) * e * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #11: `BCDEFG` / `CF·CG·DD·DE·EE·CCC`, target `a*c*d^3*e`, 12 cofactor terms. -/
theorem quarticCostChamberBCDEFG11810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDEFG11Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG11Face810 a b c d e f g +
      xiQuarticCostChamberBCDEFG11Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG11Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG11Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG11Face810 a b c d e f g +
      kappaQuarticCostChamberBCDEFG11Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG11Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG11Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG11Face810 a b c d e f g =
      a * c * d ^ 3 * e := by
  simp only [muQuarticCostChamberBCDEFG11Face810, xiQuarticCostChamberBCDEFG11Face810, piQuarticCostChamberBCDEFG11Face810, kappaQuarticCostChamberBCDEFG11Face810, n2QuarticCostChamberBCDEFG11Face810, muQuarticCostChamberBCDEFG11Cofactor810, xiQuarticCostChamberBCDEFG11Cofactor810, piQuarticCostChamberBCDEFG11Cofactor810, kappaQuarticCostChamberBCDEFG11Cofactor810, n2QuarticCostChamberBCDEFG11Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG11810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG11Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG11Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG11Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG11Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG11Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG11810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * c * d ^ 3 * e = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        exact (ha hLll).elim
      ·
        exact (hc hRll).elim
    ·
      exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hRl)
  ·
    exact (he hR).elim

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG12Face810 (a b c d e f g : k) : k :=
  -a * d ^ 2 - c ^ 3 + 8 * c * g

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEFG12Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 11 : k) * c * d

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG12Face810 (a b c d e f g : k) : k :=
  8 * a * c * d ^ 2 + 3 * c ^ 4 + (-16 : k) * c ^ 2 * g + 64 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEFG12Cofactor810 (a b c d e f g : k) : k :=
  (1 / 11 : k) * d

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG12Face810 (a b c d e f g : k) : k :=
  (-3 : k) * c ^ 2 * d + 8 * d * g

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEFG12Cofactor810 (a b c d e f g : k) : k :=
  (2 / 11 : k) * c ^ 2 + (-8 / 11 : k) * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #12: `BCDEFG` / `CG·DD·CCC`, target `a*c*d^3`, 4 cofactor terms. -/
theorem quarticCostChamberBCDEFG12810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDEFG12Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG12Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG12Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG12Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG12Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG12Face810 a b c d e f g =
      a * c * d ^ 3 := by
  simp only [muQuarticCostChamberBCDEFG12Face810, piQuarticCostChamberBCDEFG12Face810, n2QuarticCostChamberBCDEFG12Face810, muQuarticCostChamberBCDEFG12Cofactor810, piQuarticCostChamberBCDEFG12Cofactor810, n2QuarticCostChamberBCDEFG12Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG12810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG12Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG12Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG12Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG12810_identity a b c d e f g
  rw [hmu, hpi, hn2] at hid
  have hz : a * c * d ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      exact (ha hLl).elim
    ·
      exact (hc hRl).elim
  ·
    exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEG13Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 32 * c * g + 16 * e ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDEG13Cofactor810 (a b c d e f g : k) : k :=
  (4473 / 436480 : k) * a * b * c * d ^ 3 + (-249 / 39680 : k) * b ^ 2 * c * e * g
  + (489 / 19840 : k) * b * c ^ 2 * d * g + (34299 / 872960 : k) * b * c * d * e ^ 2
  + (-223 / 2480 : k) * b * d * g ^ 2 + (-297 / 79360 : k) * c ^ 2 * d ^ 2 * e
  + (-15 / 248 : k) * d ^ 2 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEG13Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-12 : k) * c ^ 2 * e + 32 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDEG13Cofactor810 (a b c d e f g : k) : k :=
  (1491 / 698368 : k) * a * b ^ 3 * d * e + (-1491 / 349184 : k) * a * b ^ 2 * c * d ^ 2
  + (-21 / 39680 : k) * b ^ 2 * c ^ 2 * g + (-9 / 31744 : k) * b ^ 2 * c * e ^ 2
  + (51 / 2480 : k) * b ^ 2 * g ^ 2 + (-1293 / 174592 : k) * b * c ^ 2 * d * e
  + (3491 / 109120 : k) * b * d * e * g + (9 / 31744 : k) * c ^ 3 * d ^ 2
  + (-209 / 19840 : k) * c * d ^ 2 * g

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEG13Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 256 * a * b * d * e
  + 128 * a * c * d ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + (-512 : k) * c * e ^ 2 + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDEG13Cofactor810 (a b c d e f g : k) : k :=
  (4473 / 13967360 : k) * a * b * d ^ 3 + (51 / 79360 : k) * b ^ 2 * e * g + (3 / 3968 : k) * b * c * d * g
  + (4473 / 3491840 : k) * b * d * e ^ 2 + (-27 / 158720 : k) * c * d ^ 2 * e

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEG13Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * d * e

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEG13Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (-4473 / 1745920 : k) * a ^ 2 * b ^ 2 * d ^ 3 + (-153 / 79360 : k) * a * b ^ 3 * e * g + (193 / 158720 : k) * a * b ^ 2 * c * d * g + (-4473 / 436480 : k) * a * b ^ 2 * d * e ^ 2 + (729 / 634880 : k) * a * b * c * d ^ 2 * e + (27 / 126976 : k) * a * c ^ 2 * d ^ 3 + (-15 / 1984 : k) * a * d ^ 3 * g + (311 / 19840 : k) * b * c ^ 2 * e * g + (27 / 31744 : k) * b * c * e ^ 3 + (-51 / 1240 : k) * b * e * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDEG13Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (1 / 19840 : k) * c ^ 3 * d * g + (-27 / 31744 : k) * c ^ 2 * d * e ^ 2 + (751 / 14880 : k) * c * d * g ^ 2 + (15 / 496 : k) * d * e ^ 2 * g

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDEG13Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_kappaQuarticCostChamberBCDEG13Cofactor810_chunk02 a b c d e f g (towerSpeedT_kappaQuarticCostChamberBCDEG13Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEG13Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-24 : k) * b * c * e + (-12 : k) * c ^ 2 * d + 32 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEG13Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (1491 / 2793472 : k) * a ^ 2 * b ^ 3 * d ^ 2 + (-553 / 476160 : k) * a * b ^ 3 * c * g + (5667 / 1396736 : k) * a * b ^ 2 * c * d * e + (-3081 / 1396736 : k) * a * b * c ^ 2 * d ^ 2 + (7561 / 436480 : k) * a * b * d ^ 2 * g + (-13 / 2480 : k) * b * c ^ 3 * g + (-9 / 31744 : k) * b * c ^ 2 * e ^ 2 + (227 / 14880 : k) * b * c * g ^ 2 + (-17 / 992 : k) * b * e ^ 2 * g + (9 / 31744 : k) * c ^ 3 * d * e

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDEG13Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (1547 / 59520 : k) * c * d * e * g

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDEG13Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_n2QuarticCostChamberBCDEG13Cofactor810_chunk02 a b c d e f g (towerSpeedT_n2QuarticCostChamberBCDEG13Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEG13810_identityPartial1_chunk01 (a b c d e f g : k) : k :=
  (4473 / 698368 : k) * a ^ 2 * b ^ 5 * d * e ^ 2 + (4473 / 872960 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3 + (-4473 / 109120 : k) * a ^ 2 * b * c * d ^ 5 + (-81 / 3968 : k) * a * b ^ 4 * c ^ 2 * e * g + (-27 / 31744 : k) * a * b ^ 4 * c * e ^ 3 + (153 / 2480 : k) * a * b ^ 4 * e * g ^ 2 + (351 / 4960 : k) * a * b ^ 3 * c ^ 3 * d * g + (14913 / 218240 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (-363 / 2480 : k) * a * b ^ 3 * c * d * g ^ 2 + (2241 / 13640 : k) * a * b ^ 3 * d * e ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEG13810_identityPartial1_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-567 / 158720 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e + (-28947 / 218240 : k) * a * b ^ 2 * c * d ^ 2 * e * g + (-34299 / 872960 : k) * a * b * c ^ 4 * d ^ 3 + (18129 / 109120 : k) * a * b * c ^ 2 * d ^ 3 * g + (27 / 3968 : k) * a * b * c * d ^ 3 * e ^ 2 + (223 / 620 : k) * a * b * d ^ 3 * g ^ 2 + (297 / 19840 : k) * a * c ^ 2 * d ^ 4 * e + (15 / 62 : k) * a * d ^ 4 * e * g + (39 / 1240 : k) * b ^ 2 * c ^ 4 * e * g + (27 / 7936 : k) * b ^ 2 * c ^ 3 * e ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEG13810_identityPartial1_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-72 / 155 : k) * b ^ 2 * c ^ 2 * e * g ^ 2 + (-543 / 4960 : k) * b ^ 2 * c * e ^ 3 * g + (102 / 155 : k) * b ^ 2 * e * g ^ 3 + (-489 / 4960 : k) * b * c ^ 5 * d * g + (-1863 / 27280 : k) * b * c ^ 4 * d * e ^ 2 + (178 / 155 : k) * b * c ^ 3 * d * g ^ 2 + (28119 / 27280 : k) * b * c ^ 2 * d * e ^ 2 * g + (34299 / 54560 : k) * b * c * d * e ^ 4 + (-446 / 155 : k) * b * c * d * g ^ 3 + (-283 / 682 : k) * b * d * e ^ 2 * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEG13810_identityPartial1_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (459 / 39680 : k) * c ^ 5 * d ^ 2 * e + (639 / 2480 : k) * c ^ 3 * d ^ 2 * e * g + (-297 / 4960 : k) * c ^ 2 * d ^ 2 * e ^ 3 + (-1409 / 620 : k) * c * d ^ 2 * e * g ^ 2 + (-30 / 31 : k) * d ^ 2 * e ^ 3 * g

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEG13810_identityPartial1 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEG13810_identityPartial1_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEG13810_identityPartial1_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEG13810_identityPartial1_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEG13810_identityPartial1_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEG13810_identityPartial2_chunk01 (a b c d e f g : k) : k :=
  (-4473 / 2793472 : k) * a ^ 3 * b ^ 5 * d ^ 3 + (553 / 158720 : k) * a ^ 2 * b ^ 5 * c * d * g + (-4473 / 698368 : k) * a ^ 2 * b ^ 5 * d * e ^ 2 + (81 / 126976 : k) * a ^ 2 * b ^ 4 * c * d ^ 2 * e + (55161 / 6983680 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3 + (-15069 / 218240 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g + (4473 / 109120 : k) * a ^ 2 * b * c * d ^ 5 + (-37 / 4960 : k) * a * b ^ 4 * c ^ 2 * e * g + (27 / 31744 : k) * a * b ^ 4 * c * e ^ 3 + (-153 / 2480 : k) * a * b ^ 4 * e * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEG13810_identityPartial2_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-2737 / 39680 : k) * a * b ^ 3 * c ^ 3 * d * g + (52191 / 1745920 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (205 / 1488 : k) * a * b ^ 3 * c * d * g ^ 2 + (-6159 / 54560 : k) * a * b ^ 3 * d * e ^ 2 * g + (-243 / 158720 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e + (6757 / 19840 : k) * a * b ^ 2 * c * d ^ 2 * e * g + (22383 / 1745920 : k) * a * b * c ^ 4 * d ^ 3 + (24513 / 218240 : k) * a * b * c ^ 2 * d ^ 3 * g + (-27 / 3968 : k) * a * b * c * d ^ 3 * e ^ 2 + (1173 / 13640 : k) * a * b * d ^ 3 * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEG13810_identityPartial2_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-297 / 19840 : k) * a * c ^ 2 * d ^ 4 * e + (-15 / 62 : k) * a * d ^ 4 * e * g + (-39 / 248 : k) * b ^ 2 * c ^ 4 * e * g + (-81 / 7936 : k) * b ^ 2 * c ^ 3 * e ^ 3 + (103 / 124 : k) * b ^ 2 * c ^ 2 * e * g ^ 2 + (-1497 / 4960 : k) * b ^ 2 * c * e ^ 3 * g + (-102 / 155 : k) * b ^ 2 * e * g ^ 3 + (177 / 4960 : k) * b * c ^ 5 * d * g + (31293 / 436480 : k) * b * c ^ 4 * d * e ^ 2 + (-989 / 1240 : k) * b * c ^ 3 * d * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEG13810_identityPartial2_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-32929 / 54560 : k) * b * c ^ 2 * d * e ^ 2 * g + (-34299 / 54560 : k) * b * c * d * e ^ 4 + (1111 / 465 : k) * b * c * d * g ^ 3 + (657 / 682 : k) * b * d * e ^ 2 * g ^ 2 + (-81 / 9920 : k) * c ^ 5 * d ^ 2 * e + (7 / 155 : k) * c ^ 3 * d ^ 2 * e * g + (297 / 4960 : k) * c ^ 2 * d ^ 2 * e ^ 3 + (134 / 93 : k) * c * d ^ 2 * e * g ^ 2 + (30 / 31 : k) * d ^ 2 * e ^ 3 * g

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEG13810_identityPartial2 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEG13810_identityPartial2_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDEG13810_identityPartial2_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEG13810_identityPartial2_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEG13810_identityPartial2_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEG13810_identityPartial3_chunk01 (a b c d e f g : k) : k :=
  (4473 / 2793472 : k) * a ^ 3 * b ^ 5 * d ^ 3 + (-553 / 158720 : k) * a ^ 2 * b ^ 5 * c * d * g + (-81 / 126976 : k) * a ^ 2 * b ^ 4 * c * d ^ 2 * e + (-18189 / 1396736 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3 + (15069 / 218240 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g + (553 / 19840 : k) * a * b ^ 4 * c ^ 2 * e * g + (-71 / 39680 : k) * a * b ^ 3 * c ^ 3 * d * g + (-34299 / 349184 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (4 / 465 : k) * a * b ^ 3 * c * d * g ^ 2 + (-51 / 992 : k) * a * b ^ 3 * d * e ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEG13810_identityPartial3_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (81 / 15872 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e + (-2269 / 10912 : k) * a * b ^ 2 * c * d ^ 2 * e * g + (9243 / 349184 : k) * a * b * c ^ 4 * d ^ 3 + (-60771 / 218240 : k) * a * b * c ^ 2 * d ^ 3 * g + (7561 / 13640 : k) * a * b * d ^ 3 * g ^ 2 + (39 / 310 : k) * b ^ 2 * c ^ 4 * e * g + (27 / 3968 : k) * b ^ 2 * c ^ 3 * e ^ 3 + (-227 / 620 : k) * b ^ 2 * c ^ 2 * e * g ^ 2 + (51 / 124 : k) * b ^ 2 * c * e ^ 3 * g + (39 / 620 : k) * b * c ^ 5 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDEG13810_identityPartial3_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-27 / 7936 : k) * b * c ^ 4 * d * e ^ 2 + (-87 / 248 : k) * b * c ^ 3 * d * g ^ 2 + (-2119 / 4960 : k) * b * c ^ 2 * d * e ^ 2 * g + (227 / 465 : k) * b * c * d * g ^ 3 + (-17 / 31 : k) * b * d * e ^ 2 * g ^ 2 + (-27 / 7936 : k) * c ^ 5 * d ^ 2 * e + (-751 / 2480 : k) * c ^ 3 * d ^ 2 * e * g + (1547 / 1860 : k) * c * d ^ 2 * e * g ^ 2

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDEG13810_identityPartial3 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDEG13810_identityPartial3_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDEG13810_identityPartial3_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDEG13810_identityPartial3_chunk01 a b c d e f g))

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #13: `BCDEG` / `BG·CG·DD·DE·EE·BBB·BBC·BCC·CCC`, target `a*b*d^3*g^2`, 46 cofactor terms. -/
theorem quarticCostChamberBCDEG13810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * muQuarticCostChamberBCDEG13Face810 a b c d e f g + xiQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEG13Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * piQuarticCostChamberBCDEG13Face810 a b c d e f g + kappaQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEG13Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEG13Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEG13Face810 a b c d e f g)) =
      a * b * d ^ 3 * g ^ 2 := by
  have h1 : muQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * muQuarticCostChamberBCDEG13Face810 a b c d e f g + xiQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEG13Face810 a b c d e f g = quarticCostChamberBCDEG13810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEG13Cofactor810, muQuarticCostChamberBCDEG13Face810, xiQuarticCostChamberBCDEG13Cofactor810, xiQuarticCostChamberBCDEG13Face810, quarticCostChamberBCDEG13810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * piQuarticCostChamberBCDEG13Face810 a b c d e f g + kappaQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEG13Face810 a b c d e f g = quarticCostChamberBCDEG13810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEG13Cofactor810, piQuarticCostChamberBCDEG13Face810, kappaQuarticCostChamberBCDEG13Cofactor810, kappaQuarticCostChamberBCDEG13Face810, quarticCostChamberBCDEG13810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEG13Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEG13Face810 a b c d e f g = quarticCostChamberBCDEG13810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEG13Cofactor810, n2QuarticCostChamberBCDEG13Face810, quarticCostChamberBCDEG13810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEG13810_identityPartial1, quarticCostChamberBCDEG13810_identityPartial2, quarticCostChamberBCDEG13810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEG13810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEG13Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEG13Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEG13Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEG13Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEG13Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEG13810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * d ^ 3 * g ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        exact (ha hLll).elim
      ·
        exact (hb hRll).elim
    ·
      exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hRl)
  ·
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDFG14Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticCostChamberBCDFG14Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (306375 / 10621952 : k) * a ^ 2 * b ^ 2 * d ^ 2 + (-8489786204025 / 236733513191538688 : k) * a * b ^ 6 + (24203652502940644395439437237 / 86501963629035729667428343808 : k) * a * b ^ 3 * c * d + (-86627058343584314136045208013 / 86501963629035729667428343808 : k) * a * b ^ 2 * d * f + (-41925 / 2655488 : k) * a * c ^ 2 * d ^ 2 + (102125 / 331936 : k) * a * d ^ 2 * g + (1818424565942034485326844391 / 1704472189734694180638982144 : k) * b ^ 4 * c ^ 2 + (-57356709145669456587333265 / 168949147712960409506695984 : k) * b ^ 4 * g + (-104626839732757891739784367 / 24135592530422915643813712 : k) * b ^ 3 * c * f + (83918472870072414063667556095 / 21625490907258932416857085952 : k) * b ^ 2 * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticCostChamberBCDFG14Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-6517147829218703765241 / 12672278815014380097536 : k) * b * c ^ 3 * d + (60104648120576522411393 / 36432801593166342780416 : k) * b * c * d * g + (1509161155411064241 / 1613482895744591872 : k) * c ^ 2 * d * f + (-3535662523195187727 / 311695559405205248 : k) * d * f * g

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDFG14Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_muQuarticCostChamberBCDFG14Cofactor810_chunk02 a b c d e f g (towerSpeedT_muQuarticCostChamberBCDFG14Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDFG14Face810 (a b c d e f g : k) : k :=
  (-3 : k) * a * b ^ 4 + 24 * a * b * c * d + (-32 : k) * a * d * f + 36 * b ^ 2 * c ^ 2
  + (-32 : k) * b ^ 2 * g + (-80 : k) * b * c * f + 64 * f ^ 2

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDFG14Cofactor810 (a b c d e f g : k) : k :=
  (71741522324055 / 236733513191538688 : k) * a * b ^ 4 * c
  + (-7304570789997530201916654721 / 216254909072589324168570859520 : k) * a * b ^ 3 * f
  + (-1075 / 230912 : k) * a * b * c ^ 2 * d + (-50525 / 663872 : k) * a * b * d * g
  + (-63425 / 1327744 : k) * a * c * d * f
  + (10161435150145635422189704895 / 43250981814517864833714171904 : k) * b ^ 2 * c ^ 3
  + (-5756361821531483068344382367 / 10812745453629466208428542976 : k) * b ^ 2 * c * g
  + (-85363223735078739635607699 / 93535860325514413567720960 : k) * b * c ^ 2 * f
  + (12662968548288402181 / 17143255767286288640 : k) * b * f * g
  + (12662968548288402181 / 17143255767286288640 : k) * c * f ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDFG14Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDFG14Cofactor810 (a b c d e f g : k) : k :=
  (-134758511175 / 13925500775972864 : k) * a * b ^ 3 * d + (-1075 / 129536 : k) * a * c * d ^ 2
  + (6827421669225 / 55702003103891456 : k) * b ^ 4 * c
  + (-95296593996145079 / 24662061874247942144 : k) * b ^ 3 * f
  + (-776567937635417 / 536131779874955264 : k) * b * c ^ 2 * d
  + (-29795570675430877 / 1541378867140496384 : k) * b * d * g
  + (-2058412336941 / 130741665646592 : k) * c * d * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDFG14Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDFG14Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (-404275533525 / 13925500775972864 : k) * a ^ 2 * b ^ 4 * d + (80625 / 1327744 : k) * a ^ 2 * b * c * d ^ 2 + (-151575 / 1327744 : k) * a ^ 2 * d ^ 2 * f + (37406699582145 / 72841080982011904 : k) * a * b ^ 5 * c + (-77674561570759903607185217187 / 865019636290357296674283438080 : k) * a * b ^ 4 * f + (119961310791003313144938941 / 172486467854507935528271872 : k) * a * b ^ 2 * c ^ 2 * d + (709924630645330306640845 / 1369595275155422342995968 : k) * a * b ^ 2 * d * g + (-338277241374667905607843859 / 165206194860648834353377280 : k) * a * b * c * d * f + (3035389292883998949 / 4285813941821572160 : k) * a * d * f ^ 2 + (2202913219370688464780866053 / 4739833623508807105064566784 : k) * b ^ 3 * c ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCDFG14Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (10104958976132890659839897 / 9978479861846648498970624 : k) * b ^ 3 * c * g + (-1303312252875391504269272559 / 620530585574144402205368320 : k) * b ^ 2 * c ^ 2 * f + (-1494851127721140434183 / 1234314415244612782080 : k) * b ^ 2 * f * g + (152547741673630055616892297 / 48926450016422924020038656 : k) * b * c * f ^ 2 + (-22575 / 713728 : k) * c ^ 4 * d + (28936180369735246397 / 246862883048922556416 : k) * c ^ 2 * d * g + (33476795979037137983 / 5445504773137997568 : k) * d * g ^ 2 + (-12662968548288402181 / 8571627883643144320 : k) * f ^ 3

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDFG14Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_kappaQuarticCostChamberBCDFG14Cofactor810_chunk02 a b c d e f g (towerSpeedT_kappaQuarticCostChamberBCDFG14Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDFG14Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + 7 * b ^ 3 * c + (-12 : k) * b ^ 2 * f + (-12 : k) * c ^ 2 * d + 32 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDFG14Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (134758511175 / 6962750387986432 : k) * a ^ 2 * b ^ 5 + (-433225 / 10621952 : k) * a ^ 2 * b ^ 2 * c * d + (76325 / 663872 : k) * a ^ 2 * b * d * f + (-148217539479813251853480729 / 350920744945378213660966912 : k) * a * b ^ 3 * c ^ 2 + (-15964966090082343775487 / 69640437719767237779456 : k) * a * b ^ 3 * g + (393184403423561718068756079 / 175460372472689106830483456 : k) * a * b ^ 2 * c * f + (-53411281163041567780899 / 19022156599380865874944 : k) * a * b * f ^ 2 + (-3225 / 115456 : k) * a * c ^ 3 * d + (-13975 / 331936 : k) * a * c * d * g + (357111649996001035995 / 1810325545002054299648 : k) * b * c ^ 4

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticCostChamberBCDFG14Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-648744782492956030092913907 / 394785838063550490368587776 : k) * b * c ^ 2 * g + (-709924630645330306640845 / 128399557045820844655872 : k) * b * g ^ 2 + (-12592848312077406207 / 27429209227658061824 : k) * c ^ 3 * f + (131906475228771548681 / 23143395285836489664 : k) * c * f * g

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDFG14Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_n2QuarticCostChamberBCDFG14Cofactor810_chunk02 a b c d e f g (towerSpeedT_n2QuarticCostChamberBCDFG14Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial1_chunk01 (a b c d e f g : k) : k :=
  (919125 / 10621952 : k) * a ^ 3 * b ^ 4 * c * d ^ 2 + (-306375 / 1327744 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f + (-15043370349015 / 14795844574471168 : k) * a ^ 2 * b ^ 8 * c + (21975755396139435971852270913 / 216254909072589324168570859520 : k) * a ^ 2 * b ^ 7 * f + (398118802790466194565788913 / 462577345609816736189456384 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d + (151575 / 663872 : k) * a ^ 2 * b ^ 5 * d * g + (-20273364047907900355616031 / 3424653924961626126049280 : k) * a ^ 2 * b ^ 4 * c * d * f + (15207242368958553231 / 1672512757784028160 : k) * a ^ 2 * b ^ 3 * d * f ^ 2 + (-364425 / 1327744 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2 + (3225 / 165968 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial1_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-289175 / 331936 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f + (-1075 / 41492 : k) * a ^ 2 * b * d ^ 2 * f * g + (63425 / 41492 : k) * a ^ 2 * c * d ^ 2 * f ^ 2 + (45651084107159531250336307461 / 18210939711375943087879651328 : k) * a * b ^ 6 * c ^ 3 + (87142350193274227539 / 153477295770989425664 : k) * a * b ^ 6 * c * g + (-105712157500132227807472458537 / 5274509977380227418745630720 : k) * a * b ^ 5 * c ^ 2 * f + (21366563471104860432053675553 / 13515931817036832760535678720 : k) * a * b ^ 5 * f * g + (389482770919523749602714308541 / 8317496502791897083406571520 : k) * a * b ^ 4 * c * f ^ 2 + (7146387902934472338125782377 / 2544175400853992049042010112 : k) * a * b ^ 3 * c ^ 4 * d + (-66545120632391553582681257 / 45431703586678429447178752 : k) * a * b ^ 3 * c ^ 2 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial1_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (50525 / 20746 : k) * a * b ^ 3 * d * g ^ 2 + (-81322818830239985319 / 2449036538183755520 : k) * a * b ^ 3 * f ^ 3 + (-5736622049976496092151038979 / 289110841006135460118410240 : k) * a * b ^ 2 * c ^ 3 * d * f + (-9480398995258144761969591 / 256966649245918718592640 : k) * a * b ^ 2 * c * d * f * g + (34165560315753049348025344349 / 795054812766872515325628160 : k) * a * b * c ^ 2 * d * f ^ 2 + (133371853726969312261 / 2142906970910786080 : k) * a * b * d * f ^ 2 * g + (41925 / 663872 : k) * a * c ^ 5 * d ^ 2 + (-72025 / 41492 : k) * a * c ^ 3 * d ^ 2 * g + (102125 / 10373 : k) * a * c * d ^ 2 * g ^ 2 + (-1300072803345640971 / 48702431157063320 : k) * a * c * d * f ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial1_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (362483143924252749876309341067 / 86501963629035729667428343808 : k) * b ^ 4 * c ^ 5 + (95302997651225907569791322841 / 10812745453629466208428542976 : k) * b ^ 4 * c ^ 3 * g + (29602276306665925073 / 4796165492843419552 : k) * b ^ 4 * c * g ^ 2 + (-66247321088877544520293841499 / 1930847402433833251505096960 : k) * b ^ 3 * c ^ 4 * f + (-4466366059525506282488141 / 110735496960713383697120 : k) * b ^ 3 * c ^ 2 * f * g + (-12662968548288402181 / 535726742727696520 : k) * b ^ 3 * f * g ^ 2 + (22514989088246482852509668739 / 227158517933392147235893760 : k) * b ^ 2 * c ^ 3 * f ^ 2 + (34095289019550827906752641 / 4622411702132979740265280 : k) * b ^ 2 * c * f ^ 2 * g + (6517147829218703765241 / 3168069703753595024384 : k) * b * c ^ 6 * d + (-6562470256018959656623 / 284631262446612052972 : k) * b * c ^ 4 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial1_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (60104648120576522411393 / 1138525049786448211888 : k) * b * c ^ 2 * d * g ^ 2 + (-5838709603278819518951144461 / 49690925797929532207851760 : k) * b * c ^ 2 * f ^ 3 + (12662968548288402181 / 267863371363848260 : k) * b * f ^ 3 * g + (-1509161155411064241 / 403370723936147968 : k) * c ^ 5 * d * f + (32274013698567578547 / 428581394182157216 : k) * c ^ 3 * d * f * g + (-3535662523195187727 / 9740486231412664 : k) * c * d * f * g ^ 2 + (12662968548288402181 / 267863371363848260 : k) * c * f ^ 4

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDFG14810_identityPartial1 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDFG14810_identityPartial1_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial1_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial1_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial1_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial1_chunk01 a b c d e f g))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial2_chunk01 (a b c d e f g : k) : k :=
  (-404275533525 / 6962750387986432 : k) * a ^ 3 * b ^ 7 * d + (190275 / 5310976 : k) * a ^ 3 * b ^ 4 * c * d ^ 2 + (-151575 / 1327744 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f + (104310699962295 / 118366756595769344 : k) * a ^ 2 * b ^ 8 * c + (-21925530089258656389769451163 / 216254909072589324168570859520 : k) * a ^ 2 * b ^ 7 * f + (7044131506046122708369531537 / 10176701603415968196168040448 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d + (628379294481695956874533 / 1369595275155422342995968 : k) * a ^ 2 * b ^ 5 * d * g + (-3810822752374450789365119719 / 1817268143467137177887150080 : k) * a ^ 2 * b ^ 4 * c * d * f + (1056202824840943267347 / 1486105984326630146480 : k) * a ^ 2 * b ^ 3 * d * f ^ 2 + (-87075 / 663872 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial2_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (117175 / 82984 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g + (747125 / 331936 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f + (-151575 / 41492 : k) * a ^ 2 * b * d ^ 2 * f * g + (-63425 / 41492 : k) * a ^ 2 * c * d ^ 2 * f ^ 2 + (155626859453639970536334149799 / 346007854516142918669713375232 : k) * a * b ^ 6 * c ^ 3 + (10347213948186673629137837 / 9978479861846648498970624 : k) * a * b ^ 6 * c * g + (-44019624995593251425232075003 / 61787116877882664048163102720 : k) * a * b ^ 5 * c ^ 2 * f + (-4215502734257277845144973117101 / 973147090826651958758568867840 : k) * a * b ^ 5 * f * g + (-661758235232847097126742823 / 2350596837745536132267074560 : k) * a * b ^ 4 * c * f ^ 2 + (-513401819752361576574050265 / 62053058557414440220536832 : k) * a * b ^ 3 * c ^ 4 * d

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial2_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (49956985392305014269906269557 / 2862197325960741055172261376 : k) * a * b ^ 3 * c ^ 2 * d * g + (689750356046346517189867 / 32099889261455211163968 : k) * a * b ^ 3 * d * g ^ 2 + (-5802984711411749625657 / 11888847874613041171840 : k) * a * b ^ 3 * f ^ 3 + (151934614432978587766505530199 / 3180219251067490061302512640 : k) * a * b ^ 2 * c ^ 3 * d * f + (-5138060070301936480675711793 / 98020456368518529286721280 : k) * a * b ^ 2 * c * d * f * g + (-30079600313357745180524257067 / 397527406383436257662814080 : k) * a * b * c ^ 2 * d * f ^ 2 + (446030677695116319557 / 16153325916593805940 : k) * a * b * d * f ^ 2 * g + (-3225 / 8096 : k) * a * c ^ 5 * d ^ 2 + (1075 / 506 : k) * a * c ^ 3 * d ^ 2 * g + (-2150 / 253 : k) * a * c * d ^ 2 * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial2_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (1300072803345640971 / 48702431157063320 : k) * a * c * d * f ^ 3 + (-481929070825741485105660543957 / 86501963629035729667428343808 : k) * b ^ 4 * c ^ 5 + (47578571514647720326763825629 / 17693583469575490159246706688 : k) * b ^ 4 * c ^ 3 * g + (10144097124616423428348197 / 311827495682707765592832 : k) * b ^ 4 * c * g ^ 2 + (616185350475785252973327994947 / 15446779219470666012040775680 : k) * b ^ 3 * c ^ 4 * f + (-14073502449611371011668000966051 / 729860318119988969068926650880 : k) * b ^ 3 * c ^ 2 * f * g + (-175772958624644502907757 / 4115370418135283482560 : k) * b ^ 3 * f * g ^ 2 + (-1808317652048889402615960279 / 17283800277540706854904960 : k) * b ^ 2 * c ^ 3 * f ^ 2 + (109153969120539636339947328713 / 1788873328725463159482663360 : k) * b ^ 2 * c * f ^ 2 * g + (425930971681404159 / 1373837685929572864 : k) * b * c ^ 6 * d

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial2_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (-4994646827546302311415 / 1678425582298311694848 : k) * b * c ^ 4 * d * g + (-356067772626052476285271 / 5349981543575868527328 : k) * b * c ^ 2 * d * g ^ 2 + (5838709603278819518951144461 / 49690925797929532207851760 : k) * b * c ^ 2 * f ^ 3 + (709924630645330306640845 / 4012486157681901395496 : k) * b * d * g ^ 3 + (-12662968548288402181 / 267863371363848260 : k) * b * f ^ 3 * g + (-10068775161332331 / 5695433809729664 : k) * c ^ 5 * d * f + (60029289149566436741 / 7714465095278829888 : k) * c ^ 3 * d * f * g + (30733286380816738835 / 170172024160562424 : k) * c * d * f * g ^ 2 + (-12662968548288402181 / 267863371363848260 : k) * c * f ^ 4

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDFG14810_identityPartial2 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDFG14810_identityPartial2_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial2_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial2_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial2_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial2_chunk01 a b c d e f g))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial3_chunk01 (a b c d e f g : k) : k :=
  (404275533525 / 6962750387986432 : k) * a ^ 3 * b ^ 7 * d + (-1299675 / 10621952 : k) * a ^ 3 * b ^ 4 * c * d ^ 2 + (228975 / 663872 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f + (943309578225 / 6962750387986432 : k) * a ^ 2 * b ^ 8 * c + (-404275533525 / 1740687596996608 : k) * a ^ 2 * b ^ 7 * f + (-544922247152978585821271987 / 350920744945378213660966912 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d + (-941084761547159090791333 / 1369595275155422342995968 : k) * a ^ 2 * b ^ 5 * d * g + (1406636827897586915813677037 / 175460372472689106830483456 : k) * a ^ 2 * b ^ 4 * c * d * f + (-186477446517077283139497 / 19022156599380865874944 : k) * a ^ 2 * b ^ 3 * d * f ^ 2 + (538575 / 1327744 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial3_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-237575 / 165968 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g + (-228975 / 165968 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f + (76325 / 20746 : k) * a ^ 2 * b * d ^ 2 * f * g + (-148217539479813251853480729 / 50131534992196887665852416 : k) * a * b ^ 6 * c ^ 3 + (-15964966090082343775487 / 9948633959966748254208 : k) * a * b ^ 6 * c * g + (3641596060843811537602176927 / 175460372472689106830483456 : k) * a * b ^ 5 * c ^ 2 * f + (15964966090082343775487 / 5803369809980603148288 : k) * a * b ^ 5 * f * g + (-2041718110804502141325539895 / 43865093118172276707620864 : k) * a * b ^ 4 * c * f ^ 2 + (59927097874622208195733959 / 10966273279543069176905216 : k) * a * b ^ 3 * c ^ 4 * d + (-789045565387316317141333627 / 49348229757943811296073472 : k) * a * b ^ 3 * c ^ 2 * d * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial3_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-767926722812712300669067 / 32099889261455211163968 : k) * a * b ^ 3 * d * g ^ 2 + (160233843489124703342697 / 4755539149845216468736 : k) * a * b ^ 3 * f ^ 3 + (-1902586675588715586910347 / 68113498630702293024256 : k) * a * b ^ 2 * c ^ 3 * d * f + (4407376383131032152628497875 / 49348229757943811296073472 : k) * a * b ^ 2 * c * d * f * g + (160233843489124703342697 / 4755539149845216468736 : k) * a * b * c ^ 2 * d * f ^ 2 + (-53411281163041567780899 / 594442393730652058592 : k) * a * b * d * f ^ 2 * g + (9675 / 28864 : k) * a * c ^ 5 * d ^ 2 + (-16125 / 41492 : k) * a * c ^ 3 * d ^ 2 * g + (-13975 / 10373 : k) * a * c * d ^ 2 * g ^ 2 + (2499781549972007251965 / 1810325545002054299648 : k) * b ^ 4 * c ^ 5

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial3_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-648744782492956030092913907 / 56397976866221498624083968 : k) * b ^ 4 * c ^ 3 * g + (-709924630645330306640845 / 18342793863688692093696 : k) * b ^ 4 * c * g ^ 2 + (-34972325259539511890862987 / 6266441874024610958231552 : k) * b ^ 3 * c ^ 4 * f + (1357822697479463614657454143 / 22776106042127912905880064 : k) * b ^ 3 * c ^ 2 * f * g + (709924630645330306640845 / 10699963087151737054656 : k) * b ^ 3 * f * g ^ 2 + (37778544936232218621 / 6857302306914515456 : k) * b ^ 2 * c ^ 3 * f ^ 2 + (-131906475228771548681 / 1928616273819707472 : k) * b ^ 2 * c * f ^ 2 * g + (-1071334949988003107985 / 452581386250513574912 : k) * b * c ^ 6 * d + (856416634538430504557158247 / 32898819838629207530715648 : k) * b * c ^ 4 * d * g + (84899158320554906731990189 / 6168528719742976412009184 : k) * b * c ^ 2 * d * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCDFG14810_identityPartial3_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (-709924630645330306640845 / 4012486157681901395496 : k) * b * d * g ^ 3 + (37778544936232218621 / 6857302306914515456 : k) * c ^ 5 * d * f + (-640961535723782850587 / 7714465095278829888 : k) * c ^ 3 * d * f * g + (131906475228771548681 / 723231102682390302 : k) * c * d * f * g ^ 2

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCDFG14810_identityPartial3 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCDFG14810_identityPartial3_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial3_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial3_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial3_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCDFG14810_identityPartial3_chunk01 a b c d e f g))))

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #14: `BCDFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`, target `a*b*c^2*d*f^2`, 63 cofactor terms. -/
theorem quarticCostChamberBCDFG14810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * muQuarticCostChamberBCDFG14Face810 a b c d e f g + xiQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * xiQuarticCostChamberBCDFG14Face810 a b c d e f g) +
      (piQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * piQuarticCostChamberBCDFG14Face810 a b c d e f g + kappaQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDFG14Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDFG14Cofactor810 a b c d e f g * n2QuarticCostChamberBCDFG14Face810 a b c d e f g)) =
      a * b * c ^ 2 * d * f ^ 2 := by
  have h1 : muQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * muQuarticCostChamberBCDFG14Face810 a b c d e f g + xiQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * xiQuarticCostChamberBCDFG14Face810 a b c d e f g = quarticCostChamberBCDFG14810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDFG14Cofactor810, muQuarticCostChamberBCDFG14Face810, xiQuarticCostChamberBCDFG14Cofactor810, xiQuarticCostChamberBCDFG14Face810, quarticCostChamberBCDFG14810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * piQuarticCostChamberBCDFG14Face810 a b c d e f g + kappaQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDFG14Face810 a b c d e f g = quarticCostChamberBCDFG14810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDFG14Cofactor810, piQuarticCostChamberBCDFG14Face810, kappaQuarticCostChamberBCDFG14Cofactor810, kappaQuarticCostChamberBCDFG14Face810, quarticCostChamberBCDFG14810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDFG14Cofactor810 a b c d e f g * n2QuarticCostChamberBCDFG14Face810 a b c d e f g = quarticCostChamberBCDFG14810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDFG14Cofactor810, n2QuarticCostChamberBCDFG14Face810, quarticCostChamberBCDFG14810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDFG14810_identityPartial1, quarticCostChamberBCDFG14810_identityPartial2, quarticCostChamberBCDFG14810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDFG14810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDFG14Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDFG14Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDFG14Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDFG14Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDFG14Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDFG14810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * c ^ 2 * d * f ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRll)
    ·
      exact (hd hRl).elim
  ·
    exact hf ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDFG15Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 32 * c * g

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCDFG15Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 44 : k) * c * d

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDFG15Face810 (a b c d e f g : k) : k :=
  3 * a * b * c * d + (-4 : k) * a * d * f

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCDFG15Cofactor810 (a b c d e f g : k) : k :=
  (2 / 11 : k) * b * c + (-4 / 11 : k) * f

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDFG15Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + 128 * a * c * d ^ 2 + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCDFG15Cofactor810 (a b c d e f g : k) : k :=
  (1 / 176 : k) * d

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDFG15Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCDFG15Cofactor810 (a b c d e f g : k) : k :=
  (3 / 176 : k) * a * b * d

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDFG15Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-12 : k) * c ^ 2 * d + 32 * d * g

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCDFG15Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 88 : k) * a * b ^ 2 + (1 / 22 : k) * c ^ 2 + (-2 / 11 : k) * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #15: `BCDFG` / `BF·BG·CF·CG·DD·BBB·BBC·BCC·CCC`, target `a*c*d^3`, 8 cofactor terms. -/
theorem quarticCostChamberBCDFG15810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDFG15Cofactor810 a b c d e f g * muQuarticCostChamberBCDFG15Face810 a b c d e f g +
      xiQuarticCostChamberBCDFG15Cofactor810 a b c d e f g * xiQuarticCostChamberBCDFG15Face810 a b c d e f g +
      piQuarticCostChamberBCDFG15Cofactor810 a b c d e f g * piQuarticCostChamberBCDFG15Face810 a b c d e f g +
      kappaQuarticCostChamberBCDFG15Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDFG15Face810 a b c d e f g +
      n2QuarticCostChamberBCDFG15Cofactor810 a b c d e f g * n2QuarticCostChamberBCDFG15Face810 a b c d e f g =
      a * c * d ^ 3 := by
  simp only [muQuarticCostChamberBCDFG15Face810, xiQuarticCostChamberBCDFG15Face810, piQuarticCostChamberBCDFG15Face810, kappaQuarticCostChamberBCDFG15Face810, n2QuarticCostChamberBCDFG15Face810, muQuarticCostChamberBCDFG15Cofactor810, xiQuarticCostChamberBCDFG15Cofactor810, piQuarticCostChamberBCDFG15Cofactor810, kappaQuarticCostChamberBCDFG15Cofactor810, n2QuarticCostChamberBCDFG15Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDFG15810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDFG15Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDFG15Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDFG15Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDFG15Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDFG15Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDFG15810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * c * d ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      exact (ha hLl).elim
    ·
      exact (hc hRl).elim
  ·
    exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCEFG16Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticCostChamberBCEFG16Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (3355 / 26738688 : k) * a ^ 2 * b ^ 2 * e ^ 2 + (-3243 / 2524160 : k) * a * b ^ 4 * c ^ 2 + (-8101727 / 5169479680 : k) * a * b ^ 4 * g + (15295246243 / 2047113953280 : k) * a * b ^ 3 * c * f + (168082576657 / 1023556976640 : k) * a * b ^ 2 * c ^ 2 * e + (826223179 / 171048960 : k) * a * b ^ 2 * e * g + (-5037198949 / 15508439040 : k) * a * b ^ 2 * f ^ 2 + (20885338507 / 11631329280 : k) * a * b * c * e * f + (-3440779 / 969277440 : k) * a * c ^ 2 * e ^ 2 + (3355 / 2506752 : k) * a * e ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticCostChamberBCEFG16Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (3056583163 / 2907832320 : k) * a * e * f ^ 2 + (3619 / 315520 : k) * b ^ 2 * c ^ 4 + (-471116407189 / 383833866240 : k) * b ^ 2 * c ^ 2 * g + (123902009651 / 4361748480 : k) * b ^ 2 * g ^ 2 + (-19597476089 / 52942602240 : k) * b * c ^ 3 * f + (3354466385617 / 191916933120 : k) * b * c * f * g + (-555698239729 / 255889244160 : k) * c ^ 4 * e + (-41618401021 / 5644615680 : k) * c ^ 2 * e * g + (2028874349603 / 383833866240 : k) * c ^ 2 * f ^ 2 + (35233636591 / 1090437120 : k) * e * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticCostChamberBCEFG16Cofactor810_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (78902895179 / 4361748480 : k) * f ^ 2 * g

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCEFG16Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_muQuarticCostChamberBCEFG16Cofactor810_chunk03 a b c d e f g (towerSpeedT_muQuarticCostChamberBCEFG16Cofactor810_chunk02 a b c d e f g (towerSpeedT_muQuarticCostChamberBCEFG16Cofactor810_chunk01 a b c d e f g))

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCEFG16Face810 (a b c d e f g : k) : k :=
  (-3 : k) * a * b ^ 4 + 12 * a * b ^ 2 * e + 36 * b ^ 2 * c ^ 2 + (-32 : k) * b ^ 2 * g
  + (-80 : k) * b * c * f + (-48 : k) * c ^ 2 * e + 128 * e * g + 64 * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_xiQuarticCostChamberBCEFG16Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (-47 / 473280 : k) * a ^ 2 * b ^ 2 * c * e + (671 / 136839168 : k) * a ^ 2 * b * e * f + (17437 / 31236480 : k) * a * b ^ 2 * c ^ 3 + (-77161917331 / 63972311040 : k) * a * b ^ 2 * c * g + (-464640947137 / 767667732480 : k) * a * b * c ^ 2 * f + (31035626483 / 8723496960 : k) * a * b * f * g + (6395083 / 11631329280 : k) * a * c ^ 3 * e + (-3440779 / 1453916160 : k) * a * c * e * g + (10940393543 / 10662051840 : k) * a * c * f ^ 2 + (709022041 / 3308912640 : k) * c ^ 5

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_xiQuarticCostChamberBCEFG16Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-3847962433 / 8723496960 : k) * c ^ 3 * g + (-13344101641 / 1654456320 : k) * c * g ^ 2

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCEFG16Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_xiQuarticCostChamberBCEFG16Cofactor810_chunk02 a b c d e f g (towerSpeedT_xiQuarticCostChamberBCEFG16Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCEFG16Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCEFG16Cofactor810 (a b c d e f g : k) : k :=
  (-3337 / 13882880 : k) * a * b ^ 2 * c * e + (-202526273 / 6203375616 : k) * a * b * e * f
  + (5129 / 20193280 : k) * a * c * e ^ 2 + (3619 / 3786240 : k) * b ^ 2 * c ^ 3
  + (-11420781463 / 170592829440 : k) * b ^ 2 * c * g + (-171917281 / 7843348480 : k) * b * c ^ 2 * f
  + (207613 / 121159680 : k) * b * f * g + (11363801591 / 341185658880 : k) * c ^ 3 * e
  + (-60361 / 39198720 : k) * c * e * g + (-2029846219 / 34118565888 : k) * c * f ^ 2

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCEFG16Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCEFG16Cofactor810_chunk01 (a b c d e f g : k) : k :=
  (1175 / 2776576 : k) * a ^ 2 * b ^ 3 * c * e + (607670075 / 6203375616 : k) * a ^ 2 * b ^ 2 * e * f + (68853 / 1292369920 : k) * a ^ 2 * b * c * e ^ 2 + (61061 / 64618496 : k) * a ^ 2 * e ^ 2 * f + (-162949 / 83297280 : k) * a * b ^ 3 * c ^ 3 + (-97198643093 / 28432138240 : k) * a * b ^ 3 * c * g + (-162910049687 / 93050634240 : k) * a * b ^ 2 * c ^ 2 * f + (62014938019 / 5815664640 : k) * a * b ^ 2 * f * g + (-98691076147 / 170592829440 : k) * a * b * c ^ 3 * e + (11375539 / 3554017280 : k) * a * b * c * e * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticCostChamberBCEFG16Cofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (48914623711 / 11631329280 : k) * a * b * c * f ^ 2 + (4992579641 / 2584739840 : k) * a * c ^ 2 * e * f + (-994164581 / 193855488 : k) * a * e * f * g + (-4900982297 / 1938554880 : k) * a * f ^ 3 + (709022041 / 1102970880 : k) * b * c ^ 5 + (-84224131 / 2907832320 : k) * b * c ^ 3 * g + (-549038006861 / 15993077760 : k) * b * c * g ^ 2 + (709022041 / 2205941760 : k) * c ^ 4 * f + (-4187533201 / 1599307776 : k) * c ^ 2 * f * g + (-207613 / 3786240 : k) * f * g ^ 2

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCEFG16Cofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_kappaQuarticCostChamberBCEFG16Cofactor810_chunk02 a b c d e f g (towerSpeedT_kappaQuarticCostChamberBCEFG16Cofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def n4QuarticCostChamberBCEFG16Face810 (a b c d e f g : k) : k :=
  31 * a ^ 2 * b ^ 3 * c + (-44 : k) * a ^ 2 * b ^ 2 * f + (-24 : k) * a ^ 2 * b * c * e
  + 32 * a ^ 2 * e * f + (-96 : k) * a * b * c ^ 3 + 256 * a * b * c * g + 128 * a * c ^ 2 * f
  + (-1024 : k) * a * f * g

set_option maxHeartbeats 64000000 in
def n4QuarticCostChamberBCEFG16Cofactor810 (a b c d e f g : k) : k :=
  (47 / 315520 : k) * b ^ 3 * c ^ 2 + (352249 / 1938554880 : k) * b ^ 3 * g
  + (-6354407 / 7754219520 : k) * b ^ 2 * c * f + (-1007719 / 1292369920 : k) * b * c ^ 2 * e
  + (-61061 / 96927744 : k) * b * e * g + (3095833 / 1938554880 : k) * b * f ^ 2
  + (351207 / 323092480 : k) * c * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk01 (a b c d e f g : k) : k :=
  (47 / 157760 : k) * a ^ 3 * b ^ 6 * c * e + (-671 / 45613056 : k) * a ^ 3 * b ^ 5 * e * f + (-1053621 / 1292369920 : k) * a ^ 3 * b ^ 4 * c * e ^ 2 + (-61061 / 64618496 : k) * a ^ 3 * b ^ 3 * e ^ 2 * f + (-460553 / 83297280 : k) * a ^ 2 * b ^ 6 * c ^ 3 + (123298653535 / 34118565888 : k) * a ^ 2 * b ^ 6 * c * g + (222591418081 / 120418467840 : k) * a ^ 2 * b ^ 5 * c ^ 2 * f + (-61998337423 / 5815664640 : k) * a ^ 2 * b ^ 5 * f * g + (33717111157 / 68237131776 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e + (289479061 / 10662051840 : k) * a ^ 2 * b ^ 4 * c * e * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-2104689858629 / 511778488320 : k) * a ^ 2 * b ^ 4 * c * f ^ 2 + (-2261718061 / 710803456 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f + (327102703 / 80773120 : k) * a ^ 2 * b ^ 3 * e * f * g + (5037198949 / 1938554880 : k) * a ^ 2 * b ^ 3 * f ^ 3 + (68853 / 323092480 : k) * a ^ 2 * b ^ 2 * c ^ 3 * e ^ 2 + (-267195 / 8077312 : k) * a ^ 2 * b ^ 2 * c * e ^ 2 * g + (11676041467 / 10662051840 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2 + (2274841 / 80773120 : k) * a ^ 2 * b * c ^ 2 * e ^ 2 * f + (-61061 / 6057984 : k) * a ^ 2 * b * e ^ 2 * f * g + (-339607677 / 40386560 : k) * a ^ 2 * b * e * f ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-3730764241 / 6397231104 : k) * a * b ^ 4 * c ^ 5 + (-1466051934337 / 31986155520 : k) * a * b ^ 4 * c ^ 3 * g + (473278864285 / 3198615552 : k) * a * b ^ 4 * c * g ^ 2 + (-737801275999 / 31986155520 : k) * a * b ^ 3 * c ^ 4 * f + (37127496487 / 121159680 : k) * a * b ^ 3 * c ^ 2 * f * g + (-61991087539 / 181739520 : k) * a * b ^ 3 * f * g ^ 2 + (-32749901207 / 7108034560 : k) * a * b ^ 2 * c ^ 5 * e + (43677344041 / 2665512960 : k) * a * b ^ 2 * c ^ 3 * e * g + (397059414607 / 3763077120 : k) * a * b ^ 2 * c ^ 3 * f ^ 2 + (44817853 / 111063040 : k) * a * b ^ 2 * c * e * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-435901560757 / 888504320 : k) * a * b ^ 2 * c * f ^ 2 * g + (69657471787 / 1777008640 : k) * a * b * c ^ 4 * e * f + (-43850926109 / 333189120 : k) * a * b * c ^ 2 * e * f * g + (-153450584581 / 940769280 : k) * a * b * c ^ 2 * f ^ 3 + (596391475 / 3028992 : k) * a * b * e * f * g ^ 2 + (1675541139 / 20193280 : k) * a * b * f ^ 3 * g + (-15387 / 1262080 : k) * a * c ^ 5 * e ^ 2 + (5129 / 78880 : k) * a * c ^ 3 * e ^ 2 * g + (-142398399563 / 2665512960 : k) * a * c ^ 3 * e * f ^ 2 + (-5129 / 19720 : k) * a * c * e ^ 2 * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (54918581011 / 333189120 : k) * a * c * e * f ^ 2 * g + (10940393543 / 166594560 : k) * a * c * f ^ 4 + (20439345941 / 2665512960 : k) * b ^ 2 * c ^ 7 + (-558476238301 / 31986155520 : k) * b ^ 2 * c ^ 5 * g + (-1715846231533 / 3998269440 : k) * b ^ 2 * c ^ 3 * g ^ 2 + (58330035125 / 49978368 : k) * b ^ 2 * c * g ^ 3 + (-69096525677 / 4411883520 : k) * b * c ^ 6 * f + (-371614953613 / 7996538880 : k) * b * c ^ 4 * f * g + (802695095723 / 666378240 : k) * b * c ^ 2 * f * g ^ 2 + (-11363801591 / 7108034560 : k) * c ^ 7 * e

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk06 (a b c d e f g : k) (acc : k) : k :=
  acc + (11462310743 / 1332756480 : k) * c ^ 5 * e * g + (-13979008657 / 1881538560 : k) * c ^ 5 * f ^ 2 + (-3831715709 / 111063040 : k) * c ^ 3 * e * g ^ 2 + (1612395703 / 23519232 : k) * c ^ 3 * f ^ 2 * g + (60361 / 38280 : k) * c * e * g ^ 3 + (3480516733 / 55531520 : k) * c * f ^ 2 * g ^ 2

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCEFG16810_identityPartial1 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk06 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial1_chunk01 a b c d e f g)))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk01 (a b c d e f g : k) : k :=
  (-47 / 157760 : k) * a ^ 3 * b ^ 6 * c * e + (671 / 45613056 : k) * a ^ 3 * b ^ 5 * e * f + (1053621 / 1292369920 : k) * a ^ 3 * b ^ 4 * c * e ^ 2 + (61061 / 64618496 : k) * a ^ 3 * b ^ 3 * e ^ 2 * f + (893 / 979968 : k) * a ^ 2 * b ^ 6 * c ^ 3 + (-205818067649 / 56864276480 : k) * a ^ 2 * b ^ 6 * c * g + (-3718632324137 / 2047113953280 : k) * a ^ 2 * b ^ 5 * c ^ 2 * f + (62044834291 / 5815664640 : k) * a ^ 2 * b ^ 5 * f * g + (-159118627457 / 341185658880 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e + (-11588061 / 3554017280 : k) * a ^ 2 * b ^ 4 * c * e * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (2060900363429 / 511778488320 : k) * a ^ 2 * b ^ 4 * c * f ^ 2 + (5490027593 / 1777008640 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f + (-197886763 / 48463872 : k) * a ^ 2 * b ^ 3 * e * f * g + (-4900982297 / 1938554880 : k) * a ^ 2 * b ^ 3 * f ^ 3 + (-6115167 / 323092480 : k) * a ^ 2 * b ^ 2 * c ^ 3 * e ^ 2 + (145073 / 8077312 : k) * a ^ 2 * b ^ 2 * c * e ^ 2 * g + (-3492615013 / 3554017280 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2 + (1847839 / 80773120 : k) * a ^ 2 * b * c ^ 2 * e ^ 2 * f + (61061 / 2019328 : k) * a ^ 2 * b * e ^ 2 * f * g + (202526273 / 24231936 : k) * a ^ 2 * b * e * f ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-351207 / 10096640 : k) * a ^ 2 * c * e ^ 2 * f ^ 2 + (19111229717 / 31986155520 : k) * a * b ^ 4 * c ^ 5 + (1465390140721 / 31986155520 : k) * a * b ^ 4 * c ^ 3 * g + (-2367138271313 / 15993077760 : k) * a * b ^ 4 * c * g ^ 2 + (734675052811 / 31986155520 : k) * a * b ^ 3 * c ^ 4 * f + (-37086415699 / 121159680 : k) * a * b ^ 3 * c ^ 2 * f * g + (62024903443 / 181739520 : k) * a * b ^ 3 * f * g ^ 2 + (6443565115 / 1421606912 : k) * a * b ^ 2 * c ^ 5 * e + (-43306469449 / 2665512960 : k) * a * b ^ 2 * c ^ 3 * e * g + (-6733492195583 / 63972311040 : k) * a * b ^ 2 * c ^ 3 * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-80719879 / 333189120 : k) * a * b ^ 2 * c * e * g ^ 2 + (434792732597 / 888504320 : k) * a * b ^ 2 * c * f ^ 2 * g + (-69294675947 / 1777008640 : k) * a * b * c ^ 4 * e * f + (2923481707 / 22212608 : k) * a * b * c ^ 2 * e * f * g + (2605390738229 / 15993077760 : k) * a * b * c ^ 2 * f ^ 3 + (-598345427 / 3028992 : k) * a * b * e * f * g ^ 2 + (-4927556761 / 60579840 : k) * a * b * f ^ 3 * g + (15387 / 1262080 : k) * a * c ^ 5 * e ^ 2 + (-5129 / 78880 : k) * a * c ^ 3 * e ^ 2 * g + (142027524971 / 2665512960 : k) * a * c ^ 3 * e * f ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (5129 / 19720 : k) * a * c * e ^ 2 * g ^ 2 + (-54547706419 / 333189120 : k) * a * c * e * f ^ 2 * g + (-10940393543 / 166594560 : k) * a * c * f ^ 4 + (-20439345941 / 2665512960 : k) * b ^ 2 * c ^ 7 + (558476238301 / 31986155520 : k) * b ^ 2 * c ^ 5 * g + (1715846231533 / 3998269440 : k) * b ^ 2 * c ^ 3 * g ^ 2 + (-58330035125 / 49978368 : k) * b ^ 2 * c * g ^ 3 + (69096525677 / 4411883520 : k) * b * c ^ 6 * f + (371614953613 / 7996538880 : k) * b * c ^ 4 * f * g + (-802695095723 / 666378240 : k) * b * c ^ 2 * f * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk06 (a b c d e f g : k) (acc : k) : k :=
  acc + (11363801591 / 7108034560 : k) * c ^ 7 * e + (-11462310743 / 1332756480 : k) * c ^ 5 * e * g + (13979008657 / 1881538560 : k) * c ^ 5 * f ^ 2 + (3831715709 / 111063040 : k) * c ^ 3 * e * g ^ 2 + (-1612395703 / 23519232 : k) * c ^ 3 * f ^ 2 * g + (-60361 / 38280 : k) * c * e * g ^ 3 + (-3480516733 / 55531520 : k) * c * f ^ 2 * g ^ 2

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCEFG16810_identityPartial2 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk06 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk05 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial2_chunk01 a b c d e f g)))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial3_chunk01 (a b c d e f g : k) : k :=
  (1457 / 315520 : k) * a ^ 2 * b ^ 6 * c ^ 3 + (10919719 / 1938554880 : k) * a ^ 2 * b ^ 6 * c * g + (-1709033 / 53477376 : k) * a ^ 2 * b ^ 5 * c ^ 2 * f + (-3874739 / 484638720 : k) * a ^ 2 * b ^ 5 * f * g + (-35859577 / 1292369920 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e + (-11577949 / 484638720 : k) * a ^ 2 * b ^ 4 * c * e * g + (8293465 / 96927744 : k) * a ^ 2 * b ^ 4 * c * f ^ 2 + (29866829 / 323092480 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f + (4062853 / 121159680 : k) * a ^ 2 * b ^ 3 * e * f * g + (-34054163 / 484638720 : k) * a ^ 2 * b ^ 3 * f ^ 3

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial3_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (3023157 / 161546240 : k) * a ^ 2 * b ^ 2 * c ^ 3 * e ^ 2 + (61061 / 4038656 : k) * a ^ 2 * b ^ 2 * c * e ^ 2 * g + (-27231737 / 242319360 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2 + (-103067 / 2019328 : k) * a ^ 2 * b * c ^ 2 * e ^ 2 * f + (-61061 / 3028992 : k) * a ^ 2 * b * e ^ 2 * f * g + (3095833 / 60579840 : k) * a ^ 2 * b * e * f ^ 3 + (351207 / 10096640 : k) * a ^ 2 * c * e ^ 2 * f ^ 2 + (-141 / 9860 : k) * a * b ^ 4 * c ^ 5 + (417799 / 20193280 : k) * a * b ^ 4 * c ^ 3 * g + (352249 / 7572480 : k) * a * b ^ 4 * c * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial3_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (7894503 / 80773120 : k) * a * b ^ 3 * c ^ 4 * f + (-3423399 / 10096640 : k) * a * b ^ 3 * c ^ 2 * f * g + (-352249 / 1893120 : k) * a * b ^ 3 * f * g ^ 2 + (3023157 / 40386560 : k) * a * b ^ 2 * c ^ 5 * e + (-351207 / 2524160 : k) * a * b ^ 2 * c ^ 3 * e * g + (-7820953 / 30289920 : k) * a * b ^ 2 * c ^ 3 * f ^ 2 + (-61061 / 378624 : k) * a * b ^ 2 * c * e * g ^ 2 + (2461 / 1972 : k) * a * b ^ 2 * c * f ^ 2 * g + (-103067 / 504832 : k) * a * b * c ^ 4 * e * f + (3771473 / 3786240 : k) * a * b * c ^ 2 * e * f * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticCostChamberBCEFG16810_identityPartial3_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (3095833 / 15144960 : k) * a * b * c ^ 2 * f ^ 3 + (61061 / 94656 : k) * a * b * e * f * g ^ 2 + (-3095833 / 1893120 : k) * a * b * f ^ 3 * g + (351207 / 2524160 : k) * a * c ^ 3 * e * f ^ 2 + (-351207 / 315520 : k) * a * c * e * f ^ 2 * g

set_option maxHeartbeats 64000000 in
def quarticCostChamberBCEFG16810_identityPartial3 (a b c d e f g : k) : k :=
  towerSpeedT_quarticCostChamberBCEFG16810_identityPartial3_chunk04 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial3_chunk03 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial3_chunk02 a b c d e f g (towerSpeedT_quarticCostChamberBCEFG16810_identityPartial3_chunk01 a b c d e f g)))

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #16: `BCEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`, target `a*b*c^2*e*f*g`, 70 cofactor terms. -/
theorem quarticCostChamberBCEFG16810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * muQuarticCostChamberBCEFG16Face810 a b c d e f g + xiQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * xiQuarticCostChamberBCEFG16Face810 a b c d e f g) +
      (piQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * piQuarticCostChamberBCEFG16Face810 a b c d e f g + kappaQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * kappaQuarticCostChamberBCEFG16Face810 a b c d e f g)) +
      (n4QuarticCostChamberBCEFG16Cofactor810 a b c d e f g * n4QuarticCostChamberBCEFG16Face810 a b c d e f g)) =
      a * b * c ^ 2 * e * f * g := by
  have h1 : muQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * muQuarticCostChamberBCEFG16Face810 a b c d e f g + xiQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * xiQuarticCostChamberBCEFG16Face810 a b c d e f g = quarticCostChamberBCEFG16810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCEFG16Cofactor810, muQuarticCostChamberBCEFG16Face810, xiQuarticCostChamberBCEFG16Cofactor810, xiQuarticCostChamberBCEFG16Face810, quarticCostChamberBCEFG16810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * piQuarticCostChamberBCEFG16Face810 a b c d e f g + kappaQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * kappaQuarticCostChamberBCEFG16Face810 a b c d e f g = quarticCostChamberBCEFG16810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCEFG16Cofactor810, piQuarticCostChamberBCEFG16Face810, kappaQuarticCostChamberBCEFG16Cofactor810, kappaQuarticCostChamberBCEFG16Face810, quarticCostChamberBCEFG16810_identityPartial2]
    ring
  have h3 : n4QuarticCostChamberBCEFG16Cofactor810 a b c d e f g * n4QuarticCostChamberBCEFG16Face810 a b c d e f g = quarticCostChamberBCEFG16810_identityPartial3 a b c d e f g := by
    simp only [n4QuarticCostChamberBCEFG16Cofactor810, n4QuarticCostChamberBCEFG16Face810, quarticCostChamberBCEFG16810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCEFG16810_identityPartial1, quarticCostChamberBCEFG16810_identityPartial2, quarticCostChamberBCEFG16810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCEFG16810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCEFG16Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCEFG16Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCEFG16Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCEFG16Face810 a b c d e f g = 0)
    (hn4 : n4QuarticCostChamberBCEFG16Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCEFG16810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn4] at hid
  have hz : a * b * c ^ 2 * e * f * g = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          rcases (mul_eq_zero.mp hLlll) with hLllll | hRllll
          ·
            exact (ha hLllll).elim
          ·
            exact (hb hRllll).elim
        ·
          exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRlll)
      ·
        exact (he hRll).elim
    ·
      exact (hf hRl).elim
  ·
    exact (hg hR).elim

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCEFG17Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g + 16 * e ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBCEFG17Cofactor810 (a b c d e f g : k) : k :=
  (3 / 176 : k) * c * e

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCEFG17Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + (-12 : k) * c ^ 2 * e + 32 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBCEFG17Cofactor810 (a b c d e f g : k) : k :=
  (1 / 352 : k) * a * b ^ 2 + (-1 / 88 : k) * c ^ 2 + (1 / 22 : k) * g

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCEFG17Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + (-512 : k) * c * e ^ 2 + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBCEFG17Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 704 : k) * e

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCEFG17Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBCEFG17Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 704 : k) * a * b * e

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCEFG17Face810 (a b c d e f g : k) : k :=
  (-3 : k) * b * c * e + 4 * e * f

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBCEFG17Cofactor810 (a b c d e f g : k) : k :=
  (1 / 22 : k) * a * b * c + (-1 / 11 : k) * a * f

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #17: `BCEFG` / `BF·BG·CF·CG·EE·BBB·BBC·BCC·CCC`, target `c*e^3`, 8 cofactor terms. -/
theorem quarticCostChamberBCEFG17810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCEFG17Cofactor810 a b c d e f g * muQuarticCostChamberBCEFG17Face810 a b c d e f g +
      xiQuarticCostChamberBCEFG17Cofactor810 a b c d e f g * xiQuarticCostChamberBCEFG17Face810 a b c d e f g +
      piQuarticCostChamberBCEFG17Cofactor810 a b c d e f g * piQuarticCostChamberBCEFG17Face810 a b c d e f g +
      kappaQuarticCostChamberBCEFG17Cofactor810 a b c d e f g * kappaQuarticCostChamberBCEFG17Face810 a b c d e f g +
      n2QuarticCostChamberBCEFG17Cofactor810 a b c d e f g * n2QuarticCostChamberBCEFG17Face810 a b c d e f g =
      c * e ^ 3 := by
  simp only [muQuarticCostChamberBCEFG17Face810, xiQuarticCostChamberBCEFG17Face810, piQuarticCostChamberBCEFG17Face810, kappaQuarticCostChamberBCEFG17Face810, n2QuarticCostChamberBCEFG17Face810, muQuarticCostChamberBCEFG17Cofactor810, xiQuarticCostChamberBCEFG17Cofactor810, piQuarticCostChamberBCEFG17Cofactor810, kappaQuarticCostChamberBCEFG17Cofactor810, n2QuarticCostChamberBCEFG17Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCEFG17810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCEFG17Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCEFG17Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCEFG17Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCEFG17Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCEFG17Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCEFG17810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : c * e ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    exact (hc hL).elim
  ·
    exact he ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBDEFG18Face810 (a b c d e f g : k) : k :=
  (-2 : k) * a * b * f - a * d ^ 2 + 4 * e ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberBDEFG18Cofactor810 (a b c d e f g : k) : k :=
  (1 / 256 : k) * a * b ^ 4 + (1 / 24 : k) * b ^ 2 * g + (-1 / 3 : k) * f ^ 2

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBDEFG18Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + (-8 : k) * a * d * f + 32 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberBDEFG18Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 192 : k) * b ^ 2 * e + (1 / 24 : k) * d * f

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBDEFG18Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + 64 * a * b ^ 2 * g + 256 * a * b * d * e + (-256 : k) * a * f ^ 2 + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberBDEFG18Cofactor810 (a b c d e f g : k) : k :=
  (1 / 384 : k) * b * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBDEFG18Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + 32 * b * g + 32 * d * e

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberBDEFG18Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 12 : k) * f * g

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBDEFG18Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + 32 * d * g + 32 * e * f

set_option maxHeartbeats 64000000 in
def n2QuarticCostChamberBDEFG18Cofactor810 (a b c d e f g : k) : k :=
  (1 / 768 : k) * a * b ^ 2 * d + (1 / 24 : k) * e * f

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #18: `BDEFG` / `BF·BG·DD·DE·EE·BBB`, target `a*b^2*d*e*f`, 9 cofactor terms. -/
theorem quarticCostChamberBDEFG18810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBDEFG18Cofactor810 a b c d e f g * muQuarticCostChamberBDEFG18Face810 a b c d e f g +
      xiQuarticCostChamberBDEFG18Cofactor810 a b c d e f g * xiQuarticCostChamberBDEFG18Face810 a b c d e f g +
      piQuarticCostChamberBDEFG18Cofactor810 a b c d e f g * piQuarticCostChamberBDEFG18Face810 a b c d e f g +
      kappaQuarticCostChamberBDEFG18Cofactor810 a b c d e f g * kappaQuarticCostChamberBDEFG18Face810 a b c d e f g +
      n2QuarticCostChamberBDEFG18Cofactor810 a b c d e f g * n2QuarticCostChamberBDEFG18Face810 a b c d e f g =
      a * b ^ 2 * d * e * f := by
  simp only [muQuarticCostChamberBDEFG18Face810, xiQuarticCostChamberBDEFG18Face810, piQuarticCostChamberBDEFG18Face810, kappaQuarticCostChamberBDEFG18Face810, n2QuarticCostChamberBDEFG18Face810, muQuarticCostChamberBDEFG18Cofactor810, xiQuarticCostChamberBDEFG18Cofactor810, piQuarticCostChamberBDEFG18Cofactor810, kappaQuarticCostChamberBDEFG18Cofactor810, n2QuarticCostChamberBDEFG18Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBDEFG18810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBDEFG18Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBDEFG18Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBDEFG18Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBDEFG18Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBDEFG18Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBDEFG18810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b ^ 2 * d * e * f = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRlll)
      ·
        exact (hd hRll).elim
    ·
      exact (he hRl).elim
  ·
    exact (hf hR).elim

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberCDEFG19Face810 (a b c d e f g : k) : k :=
  -a * d ^ 2 - c ^ 3 + 8 * c * g + 4 * e ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticCostChamberCDEFG19Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 12 : k) * a ^ 2 * f * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberCDEFG19Face810 (a b c d e f g : k) : k :=
  (-2 : k) * a * d * f + (-3 : k) * c ^ 2 * e + 8 * e * g

set_option maxHeartbeats 64000000 in
def xiQuarticCostChamberCDEFG19Cofactor810 (a b c d e f g : k) : k :=
  (-7 / 192 : k) * a ^ 2 * c ^ 2 * d + (1 / 4 : k) * a ^ 2 * d * g + (7 / 24 : k) * a ^ 2 * e * f

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberCDEFG19Face810 (a b c d e f g : k) : k :=
  8 * a * c * d ^ 2 + (-16 : k) * a * f ^ 2 + 3 * c ^ 4 + (-16 : k) * c ^ 2 * g + (-32 : k) * c * e ^ 2
  + 64 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticCostChamberCDEFG19Cofactor810 (a b c d e f g : k) : k :=
  (1 / 96 : k) * a ^ 2 * c * f

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberCDEFG19Face810 (a b c d e f g : k) : k :=
  c * f + d * e

set_option maxHeartbeats 64000000 in
def kappaQuarticCostChamberCDEFG19Cofactor810 (a b c d e f g : k) : k :=
  (1 / 6 : k) * a ^ 3 * f ^ 2 + (-1 / 32 : k) * a ^ 2 * c ^ 4 + (1 / 12 : k) * a ^ 2 * c ^ 2 * g
  + a ^ 2 * c * e ^ 2

set_option maxHeartbeats 64000000 in
def n4QuarticCostChamberCDEFG19Face810 (a b c d e f g : k) : k :=
  (-3 : k) * a ^ 2 * c ^ 2 * d + 8 * a ^ 2 * d * g + 8 * a ^ 2 * e * f

set_option maxHeartbeats 64000000 in
def n4QuarticCostChamberCDEFG19Cofactor810 (a b c d e f g : k) : k :=
  (5 / 96 : k) * a * d * f + (5 / 192 : k) * c ^ 2 * e + (-1 / 4 : k) * e * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #19: `CDEFG` / `CF·CG·DD·DE·EE·CCC`, target `a^2*c*d*e^3`, 12 cofactor terms. -/
theorem quarticCostChamberCDEFG19810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberCDEFG19Cofactor810 a b c d e f g * muQuarticCostChamberCDEFG19Face810 a b c d e f g +
      xiQuarticCostChamberCDEFG19Cofactor810 a b c d e f g * xiQuarticCostChamberCDEFG19Face810 a b c d e f g +
      piQuarticCostChamberCDEFG19Cofactor810 a b c d e f g * piQuarticCostChamberCDEFG19Face810 a b c d e f g +
      kappaQuarticCostChamberCDEFG19Cofactor810 a b c d e f g * kappaQuarticCostChamberCDEFG19Face810 a b c d e f g +
      n4QuarticCostChamberCDEFG19Cofactor810 a b c d e f g * n4QuarticCostChamberCDEFG19Face810 a b c d e f g =
      a ^ 2 * c * d * e ^ 3 := by
  simp only [muQuarticCostChamberCDEFG19Face810, xiQuarticCostChamberCDEFG19Face810, piQuarticCostChamberCDEFG19Face810, kappaQuarticCostChamberCDEFG19Face810, n4QuarticCostChamberCDEFG19Face810, muQuarticCostChamberCDEFG19Cofactor810, xiQuarticCostChamberCDEFG19Cofactor810, piQuarticCostChamberCDEFG19Cofactor810, kappaQuarticCostChamberCDEFG19Cofactor810, n4QuarticCostChamberCDEFG19Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberCDEFG19810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberCDEFG19Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberCDEFG19Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberCDEFG19Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberCDEFG19Face810 a b c d e f g = 0)
    (hn4 : n4QuarticCostChamberCDEFG19Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberCDEFG19810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn4] at hid
  have hz : a ^ 2 * c * d * e ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        exact ha ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hLll)
      ·
        exact (hc hRll).elim
    ·
      exact (hd hRl).elim
  ·
    exact he ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

end QuarticRescueCertificates810

end Max11DegreeRoutes
