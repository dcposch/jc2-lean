import Grok810DegreeZeroClearingDischargeScratch
import Grok810DegreeZeroTowerOrders111to118Scratch
import Grok810RouteAdapterScratch

/-! # `(8,10)` nonzero-face closure, split 1: integer bars and compact blocks

Coordinator split of untracked `Grok810NonzeroFaceClosureScratch`
(SHA `be179b5c`; 12,518 lines).  No tracked file was edited.  The
monolith is not imported.

Parents (tracked, green):

* `Grok810DegreeZeroClearingDischargeScratch`
* `Grok810DegreeZeroTowerOrders111to118Scratch`
* `Grok810RouteAdapterScratch`

This piece holds `DegreeZeroBars810` and `DegreeZeroCompactBlocks810`.
Later pieces import this file in order.  No `sorry`, no new axioms,
no finite-root shortcut, no closure overclaim.
-/


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
set_option maxHeartbeats 800000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Integer bars on the ninth-power face -/

section DegreeZeroBars810

variable {R : Type*} [CommRing R]

def degreeZeroLBar810 (h lambda : R) : R :=
  -lambda * h ^ 7

def degreeZeroABar810 (h a7 a6 : R) : R :=
  (16 : R) * a6 * h ^ 8 - (7 : R) * a7 ^ 2

def degreeZeroBBar810 (h a7 a6 a5 : R) : R :=
  (32 : R) * a5 * h ^ 16 - (24 : R) * a6 * a7 * h ^ 8 + (7 : R) * a7 ^ 3

def degreeZeroCBar810 (h a7 a6 a5 a4 : R) : R :=
  (2048 : R) * a4 * h ^ 24 - (1280 : R) * a5 * a7 * h ^ 16 +
    (480 : R) * a6 * a7 ^ 2 * h ^ 8 - (105 : R) * a7 ^ 4

def degreeZeroDBar810 (h a7 a6 a5 a4 a3 : R) : R :=
  (1024 : R) * a3 * h ^ 32 - (512 : R) * a4 * a7 * h ^ 24 +
    (160 : R) * a5 * a7 ^ 2 * h ^ 16 - (40 : R) * a6 * a7 ^ 3 * h ^ 8 +
    (7 : R) * a7 ^ 5

def degreeZeroEBar810 (h a7 a6 a5 a4 a3 a2 : R) : R :=
  (65536 : R) * a2 * h ^ 40 - (24576 : R) * a3 * a7 * h ^ 32 +
    (6144 : R) * a4 * a7 ^ 2 * h ^ 24 - (1280 : R) * a5 * a7 ^ 3 * h ^ 16 +
    (240 : R) * a6 * a7 ^ 4 * h ^ 8 - (35 : R) * a7 ^ 6

def degreeZeroFBar810 (h a7 a6 a5 a4 a3 a2 a1 : R) : R :=
  (131072 : R) * a1 * h ^ 48 - (32768 : R) * a2 * a7 * h ^ 40 +
    (6144 : R) * a3 * a7 ^ 2 * h ^ 32 - (1024 : R) * a4 * a7 ^ 3 * h ^ 24 +
    (160 : R) * a5 * a7 ^ 4 * h ^ 16 - (24 : R) * a6 * a7 ^ 5 * h ^ 8 +
    (3 : R) * a7 ^ 7

def degreeZeroGBar810 (h a7 a6 a5 a4 a3 a2 a1 a0 : R) : R :=
  (16777216 : R) * a0 * h ^ 56 - (2097152 : R) * a1 * a7 * h ^ 48 +
    (262144 : R) * a2 * a7 ^ 2 * h ^ 40 -
    (32768 : R) * a3 * a7 ^ 3 * h ^ 32 +
    (4096 : R) * a4 * a7 ^ 4 * h ^ 24 - (512 : R) * a5 * a7 ^ 5 * h ^ 16 +
    (64 : R) * a6 * a7 ^ 6 * h ^ 8 - (7 : R) * a7 ^ 8

def degreeZeroPBar810 (h a7 b8 lambda : R) : R :=
  -(45 : R) * a7 ^ 2 + (18 : R) * lambda * a7 * h ^ 7 +
    (64 : R) * b8 * h ^ 6

def degreeZeroQBar810 (h a7 b8 b7 lambda : R) : R :=
  (64 : R) * b7 * h ^ 14 - (64 : R) * a7 * b8 * h ^ 6 -
    (9 : R) * lambda * a7 ^ 2 * h ^ 7 + (30 : R) * a7 ^ 3

def degreeZeroRBar810 (h a7 b8 b7 b6 lambda : R) : R :=
  -(315 : R) * a7 ^ 4 + (84 : R) * lambda * a7 ^ 3 * h ^ 7 +
    (896 : R) * a7 ^ 2 * b8 * h ^ 6 - (1792 : R) * a7 * b7 * h ^ 14 +
    (2048 : R) * b6 * h ^ 22

def degreeZeroSBar810 (h a7 b8 b7 b6 b5 lambda : R) : R :=
  (252 : R) * a7 ^ 5 - (63 : R) * lambda * a7 ^ 4 * h ^ 7 -
    (896 : R) * a7 ^ 3 * b8 * h ^ 6 + (2688 : R) * a7 ^ 2 * b7 * h ^ 14 -
    (6144 : R) * a7 * b6 * h ^ 22 + (8192 : R) * b5 * h ^ 30

def degreeZeroTBar810 (h a7 b8 b7 b6 b5 b4 lambda : R) : R :=
  -(525 : R) * a7 ^ 6 + (126 : R) * lambda * a7 ^ 5 * h ^ 7 +
    (2240 : R) * a7 ^ 4 * b8 * h ^ 6 - (8960 : R) * a7 ^ 3 * b7 * h ^ 14 +
    (30720 : R) * a7 ^ 2 * b6 * h ^ 22 - (81920 : R) * a7 * b5 * h ^ 30 +
    (131072 : R) * b4 * h ^ 38

def degreeZeroUBar810 (h a7 b8 b7 b6 b5 b4 b3 lambda : R) : R :=
  (90 : R) * a7 ^ 7 - (21 : R) * lambda * a7 ^ 6 * h ^ 7 -
    (448 : R) * a7 ^ 5 * b8 * h ^ 6 + (2240 : R) * a7 ^ 4 * b7 * h ^ 14 -
    (10240 : R) * a7 ^ 3 * b6 * h ^ 22 + (40960 : R) * a7 ^ 2 * b5 * h ^ 30 -
    (131072 : R) * a7 * b4 * h ^ 38 + (262144 : R) * b3 * h ^ 46

def degreeZeroVBar810 (h a7 b8 b7 b6 b5 b4 b3 b2 lambda : R) : R :=
  -(315 : R) * a7 ^ 8 + (72 : R) * lambda * a7 ^ 7 * h ^ 7 +
    (1792 : R) * a7 ^ 6 * b8 * h ^ 6 - (10752 : R) * a7 ^ 5 * b7 * h ^ 14 +
    (61440 : R) * a7 ^ 4 * b6 * h ^ 22 - (327680 : R) * a7 ^ 3 * b5 * h ^ 30 +
    (1572864 : R) * a7 ^ 2 * b4 * h ^ 38 -
    (6291456 : R) * a7 * b3 * h ^ 46 + (16777216 : R) * b2 * h ^ 54

def degreeZeroWBar810 (h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
  (40 : R) * a7 ^ 9 - (9 : R) * lambda * a7 ^ 8 * h ^ 7 -
    (256 : R) * a7 ^ 7 * b8 * h ^ 6 + (1792 : R) * a7 ^ 6 * b7 * h ^ 14 -
    (12288 : R) * a7 ^ 5 * b6 * h ^ 22 + (81920 : R) * a7 ^ 4 * b5 * h ^ 30 -
    (524288 : R) * a7 ^ 3 * b4 * h ^ 38 +
    (3145728 : R) * a7 ^ 2 * b3 * h ^ 46 -
    (16777216 : R) * a7 * b2 * h ^ 54 + (67108864 : R) * b1 * h ^ 62

end DegreeZeroBars810

/-! ## Compact blocks of the 215-term integer numerator -/

section DegreeZeroCompactBlocks810

-- Ring named `S` so the residual coordinate `R` is not shadowed.
variable {S : Type*} [CommRing S]

/-- Compact block `0` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock0_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    - (7245315 : S) * L * A ^ 8
    + (66242880 : S) * L * A ^ 6 * C0
    + (198728640 : S) * L * A ^ 5 * B ^ 2
    - (77552640 : S) * L * A ^ 5 * E0
    - (387763200 : S) * L * A ^ 4 * B * D0
    - (193881600 : S) * L * A ^ 4 * C0 ^ 2
    + (94003200 : S) * L * A ^ 4 * G0
    - (775526400 : S) * L * A ^ 3 * B ^ 2 * C0
    + (376012800 : S) * L * A ^ 3 * B * F0

/-- Compact block `1` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock1_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (376012800 : S) * L * A ^ 3 * C0 * E0
    + (188006400 : S) * L * A ^ 3 * D0 ^ 2
    - (193881600 : S) * L * A ^ 2 * B ^ 4
    + (564019200 : S) * L * A ^ 2 * B ^ 2 * E0
    + (1128038400 : S) * L * A ^ 2 * B * C0 * D0
    + (188006400 : S) * L * A ^ 2 * C0 ^ 3
    - (360972288 : S) * L * A ^ 2 * C0 * G0
    - (360972288 : S) * L * A ^ 2 * D0 * F0
    - (180486144 : S) * L * A ^ 2 * E0 ^ 2

/-- Compact block `2` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock2_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (376012800 : S) * L * A * B ^ 3 * D0
    + (564019200 : S) * L * A * B ^ 2 * C0 ^ 2
    - (360972288 : S) * L * A * B ^ 2 * G0
    - (721944576 : S) * L * A * B * C0 * F0
    - (721944576 : S) * L * A * B * D0 * E0
    - (360972288 : S) * L * A * C0 ^ 2 * E0
    - (360972288 : S) * L * A * C0 * D0 ^ 2
    + (339738624 : S) * L * A * E0 * G0
    + (169869312 : S) * L * A * F0 ^ 2

/-- Compact block `3` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock3_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (94003200 : S) * L * B ^ 4 * C0
    - (120324096 : S) * L * B ^ 3 * F0
    - (360972288 : S) * L * B ^ 2 * C0 * E0
    - (180486144 : S) * L * B ^ 2 * D0 ^ 2
    - (360972288 : S) * L * B * C0 ^ 2 * D0
    + (339738624 : S) * L * B * D0 * G0
    + (339738624 : S) * L * B * E0 * F0
    - (30081024 : S) * L * C0 ^ 4
    + (169869312 : S) * L * C0 ^ 2 * G0

/-- Compact block `4` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock4_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (339738624 : S) * L * C0 * D0 * F0
    + (169869312 : S) * L * C0 * E0 ^ 2
    + (169869312 : S) * L * D0 ^ 2 * E0
    - (150994944 : S) * L * G0 ^ 2
    - (64402800 : S) * A ^ 7 * B
    + (7360320 : S) * A ^ 7 * Q
    + (58882560 : S) * A ^ 6 * B * P
    + (73603200 : S) * A ^ 6 * D0
    - (7180800 : S) * A ^ 6 * S0

/-- Compact block `5` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock5_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (441619200 : S) * A ^ 5 * B * C0
    - (51701760 : S) * A ^ 5 * B * R
    - (60318720 : S) * A ^ 5 * C0 * Q
    - (68935680 : S) * A ^ 5 * D0 * P
    - (86169600 : S) * A ^ 5 * F0
    + (6266880 : S) * A ^ 5 * U0
    + (368016000 : S) * A ^ 4 * B ^ 3
    - (150796800 : S) * A ^ 4 * B ^ 2 * Q
    - (344678400 : S) * A ^ 4 * B * C0 * P

/-- Compact block `6` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock6_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    - (430848000 : S) * A ^ 4 * B * E0
    + (41779200 : S) * A ^ 4 * B * T0
    - (430848000 : S) * A ^ 4 * C0 * D0
    + (52224000 : S) * A ^ 4 * C0 * S0
    + (62668800 : S) * A ^ 4 * D0 * R
    + (73113600 : S) * A ^ 4 * E0 * Q
    + (83558400 : S) * A ^ 4 * F0 * P
    - (3342336 : S) * A ^ 4 * W0
    - (229785600 : S) * A ^ 3 * B ^ 3 * P

/-- Compact block `7` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock7_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    - (861696000 : S) * A ^ 3 * B ^ 2 * D0
    + (104448000 : S) * A ^ 3 * B ^ 2 * S0
    - (861696000 : S) * A ^ 3 * B * C0 ^ 2
    + (250675200 : S) * A ^ 3 * B * C0 * R
    + (292454400 : S) * A ^ 3 * B * D0 * Q
    + (334233600 : S) * A ^ 3 * B * E0 * P
    + (417792000 : S) * A ^ 3 * B * G0
    - (26738688 : S) * A ^ 3 * B * V0
    + (146227200 : S) * A ^ 3 * C0 ^ 2 * Q

/-- Compact block `8` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock8_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (334233600 : S) * A ^ 3 * C0 * D0 * P
    + (417792000 : S) * A ^ 3 * C0 * F0
    - (40108032 : S) * A ^ 3 * C0 * U0
    + (417792000 : S) * A ^ 3 * D0 * E0
    - (53477376 : S) * A ^ 3 * D0 * T0
    - (66846720 : S) * A ^ 3 * E0 * S0
    - (80216064 : S) * A ^ 3 * F0 * R
    - (93585408 : S) * A ^ 3 * G0 * Q
    - (861696000 : S) * A ^ 2 * B ^ 3 * C0

/-- Compact block `9` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock9_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (125337600 : S) * A ^ 2 * B ^ 3 * R
    + (438681600 : S) * A ^ 2 * B ^ 2 * C0 * Q
    + (501350400 : S) * A ^ 2 * B ^ 2 * D0 * P
    + (626688000 : S) * A ^ 2 * B ^ 2 * F0
    - (60162048 : S) * A ^ 2 * B ^ 2 * U0
    + (501350400 : S) * A ^ 2 * B * C0 ^ 2 * P
    + (1253376000 : S) * A ^ 2 * B * C0 * E0
    - (160432128 : S) * A ^ 2 * B * C0 * T0
    + (626688000 : S) * A ^ 2 * B * D0 ^ 2

/-- Compact block `10` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock10_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    - (200540160 : S) * A ^ 2 * B * D0 * S0
    - (240648192 : S) * A ^ 2 * B * E0 * R
    - (280756224 : S) * A ^ 2 * B * F0 * Q
    - (320864256 : S) * A ^ 2 * B * G0 * P
    + (626688000 : S) * A ^ 2 * C0 ^ 2 * D0
    - (100270080 : S) * A ^ 2 * C0 ^ 2 * S0
    - (240648192 : S) * A ^ 2 * C0 * D0 * R
    - (280756224 : S) * A ^ 2 * C0 * E0 * Q
    - (320864256 : S) * A ^ 2 * C0 * F0 * P

/-- Compact block `11` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock11_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (18874368 : S) * A ^ 2 * C0 * W0
    - (140378112 : S) * A ^ 2 * D0 ^ 2 * Q
    - (320864256 : S) * A ^ 2 * D0 * E0 * P
    - (401080320 : S) * A ^ 2 * D0 * G0
    + (37748736 : S) * A ^ 2 * D0 * V0
    - (401080320 : S) * A ^ 2 * E0 * F0
    + (56623104 : S) * A ^ 2 * E0 * U0
    + (75497472 : S) * A ^ 2 * F0 * T0
    + (94371840 : S) * A ^ 2 * G0 * S0

/-- Compact block `12` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock12_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    - (86169600 : S) * A * B ^ 5
    + (73113600 : S) * A * B ^ 4 * Q
    + (334233600 : S) * A * B ^ 3 * C0 * P
    + (417792000 : S) * A * B ^ 3 * E0
    - (53477376 : S) * A * B ^ 3 * T0
    + (1253376000 : S) * A * B ^ 2 * C0 * D0
    - (200540160 : S) * A * B ^ 2 * C0 * S0
    - (240648192 : S) * A * B ^ 2 * D0 * R
    - (280756224 : S) * A * B ^ 2 * E0 * Q

/-- Compact block `13` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock13_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    - (320864256 : S) * A * B ^ 2 * F0 * P
    + (18874368 : S) * A * B ^ 2 * W0
    + (417792000 : S) * A * B * C0 ^ 3
    - (240648192 : S) * A * B * C0 ^ 2 * R
    - (561512448 : S) * A * B * C0 * D0 * Q
    - (641728512 : S) * A * B * C0 * E0 * P
    - (802160640 : S) * A * B * C0 * G0
    + (75497472 : S) * A * B * C0 * V0
    - (320864256 : S) * A * B * D0 ^ 2 * P

/-- Compact block `14` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock14_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    - (802160640 : S) * A * B * D0 * F0
    + (113246208 : S) * A * B * D0 * U0
    - (401080320 : S) * A * B * E0 ^ 2
    + (150994944 : S) * A * B * E0 * T0
    + (188743680 : S) * A * B * F0 * S0
    + (226492416 : S) * A * B * G0 * R
    - (93585408 : S) * A * C0 ^ 3 * Q
    - (320864256 : S) * A * C0 ^ 2 * D0 * P
    - (401080320 : S) * A * C0 ^ 2 * F0

/-- Compact block `15` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock15_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (56623104 : S) * A * C0 ^ 2 * U0
    - (802160640 : S) * A * C0 * D0 * E0
    + (150994944 : S) * A * C0 * D0 * T0
    + (188743680 : S) * A * C0 * E0 * S0
    + (226492416 : S) * A * C0 * F0 * R
    + (264241152 : S) * A * C0 * G0 * Q
    - (133693440 : S) * A * D0 ^ 3
    + (94371840 : S) * A * D0 ^ 2 * S0
    + (226492416 : S) * A * D0 * E0 * R

/-- Compact block `16` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock16_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (264241152 : S) * A * D0 * F0 * Q
    + (301989888 : S) * A * D0 * G0 * P
    + (132120576 : S) * A * E0 ^ 2 * Q
    + (301989888 : S) * A * E0 * F0 * P
    - (33554432 : S) * A * E0 * W0
    + (377487360 : S) * A * F0 * G0
    - (67108864 : S) * A * F0 * V0
    - (100663296 : S) * A * G0 * U0
    + (16711680 : S) * B ^ 5 * P

/-- Compact block `17` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock17_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (104448000 : S) * B ^ 4 * D0
    - (16711680 : S) * B ^ 4 * S0
    + (208896000 : S) * B ^ 3 * C0 ^ 2
    - (80216064 : S) * B ^ 3 * C0 * R
    - (93585408 : S) * B ^ 3 * D0 * Q
    - (106954752 : S) * B ^ 3 * E0 * P
    - (133693440 : S) * B ^ 3 * G0
    + (12582912 : S) * B ^ 3 * V0
    - (140378112 : S) * B ^ 2 * C0 ^ 2 * Q

/-- Compact block `18` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock18_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    - (320864256 : S) * B ^ 2 * C0 * D0 * P
    - (401080320 : S) * B ^ 2 * C0 * F0
    + (56623104 : S) * B ^ 2 * C0 * U0
    - (401080320 : S) * B ^ 2 * D0 * E0
    + (75497472 : S) * B ^ 2 * D0 * T0
    + (94371840 : S) * B ^ 2 * E0 * S0
    + (113246208 : S) * B ^ 2 * F0 * R
    + (132120576 : S) * B ^ 2 * G0 * Q
    - (106954752 : S) * B * C0 ^ 3 * P

/-- Compact block `19` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock19_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    - (401080320 : S) * B * C0 ^ 2 * E0
    + (75497472 : S) * B * C0 ^ 2 * T0
    - (401080320 : S) * B * C0 * D0 ^ 2
    + (188743680 : S) * B * C0 * D0 * S0
    + (226492416 : S) * B * C0 * E0 * R
    + (264241152 : S) * B * C0 * F0 * Q
    + (301989888 : S) * B * C0 * G0 * P
    + (113246208 : S) * B * D0 ^ 2 * R
    + (264241152 : S) * B * D0 * E0 * Q

/-- Compact block `20` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock20_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (301989888 : S) * B * D0 * F0 * P
    - (33554432 : S) * B * D0 * W0
    + (150994944 : S) * B * E0 ^ 2 * P
    + (377487360 : S) * B * E0 * G0
    - (67108864 : S) * B * E0 * V0
    + (188743680 : S) * B * F0 ^ 2
    - (100663296 : S) * B * F0 * U0
    - (134217728 : S) * B * G0 * T0
    - (133693440 : S) * C0 ^ 3 * D0

/-- Compact block `21` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock21_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (31457280 : S) * C0 ^ 3 * S0
    + (113246208 : S) * C0 ^ 2 * D0 * R
    + (132120576 : S) * C0 ^ 2 * E0 * Q
    + (150994944 : S) * C0 ^ 2 * F0 * P
    - (16777216 : S) * C0 ^ 2 * W0
    + (132120576 : S) * C0 * D0 ^ 2 * Q
    + (301989888 : S) * C0 * D0 * E0 * P
    + (377487360 : S) * C0 * D0 * G0
    - (67108864 : S) * C0 * D0 * V0

/-- Compact block `22` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock22_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    (377487360 : S) * C0 * E0 * F0
    - (100663296 : S) * C0 * E0 * U0
    - (134217728 : S) * C0 * F0 * T0
    - (167772160 : S) * C0 * G0 * S0
    + (50331648 : S) * D0 ^ 3 * P
    + (188743680 : S) * D0 ^ 2 * F0
    - (50331648 : S) * D0 ^ 2 * U0
    + (188743680 : S) * D0 * E0 ^ 2
    - (134217728 : S) * D0 * E0 * T0

/-- Compact block `23` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock23_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    - (167772160 : S) * D0 * F0 * S0
    - (201326592 : S) * D0 * G0 * R
    - (83886080 : S) * E0 ^ 2 * S0
    - (201326592 : S) * E0 * F0 * R
    - (234881024 : S) * E0 * G0 * Q
    - (117440512 : S) * F0 ^ 2 * Q
    - (268435456 : S) * F0 * G0 * P
    + (268435456 : S) * G0 * W0

/-- The 215-term compact is the sum of the 24 blocks. -/
theorem degreeZeroCompact810_blockSum
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) :
    degreeZeroClearedCompact810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0
        W0 =
      degreeZeroCompactBlock0_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock1_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock2_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock3_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock4_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock5_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock6_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock7_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock8_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock9_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock10_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock11_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock12_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock13_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock14_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock15_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock16_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock17_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock18_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock19_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock20_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock21_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock22_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      degreeZeroCompactBlock23_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 := by
  simp only [degreeZeroClearedCompact810, degreeZeroCompactBlock0_810, degreeZeroCompactBlock1_810, degreeZeroCompactBlock2_810, degreeZeroCompactBlock3_810, degreeZeroCompactBlock4_810, degreeZeroCompactBlock5_810, degreeZeroCompactBlock6_810, degreeZeroCompactBlock7_810, degreeZeroCompactBlock8_810, degreeZeroCompactBlock9_810, degreeZeroCompactBlock10_810, degreeZeroCompactBlock11_810, degreeZeroCompactBlock12_810, degreeZeroCompactBlock13_810, degreeZeroCompactBlock14_810, degreeZeroCompactBlock15_810, degreeZeroCompactBlock16_810, degreeZeroCompactBlock17_810, degreeZeroCompactBlock18_810, degreeZeroCompactBlock19_810, degreeZeroCompactBlock20_810, degreeZeroCompactBlock21_810, degreeZeroCompactBlock22_810, degreeZeroCompactBlock23_810]
  ring

#print axioms degreeZeroCompact810_blockSum

end DegreeZeroCompactBlocks810

end Max11DegreeRoutes
