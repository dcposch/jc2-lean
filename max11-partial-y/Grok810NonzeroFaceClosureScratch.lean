import Grok810DegreeZeroClearingDischargeScratch
import Grok810DegreeZeroTowerOrders111to118Scratch
import Grok810RouteAdapterScratch

/-! # Closure of the `(8,10)` scale-two nonzero linear-root face

Untracked working note.  No tracked file was edited.

Parents (tracked, green):

* `Grok810DegreeZeroClearingDischargeScratch`
  (`sourceRhoResidualLeftJet810_deriv_eq_simplePole_of_source`,
  `degreeZeroFace810_linearRoot_headVanishing_of_clearing`;
  the remaining-`17` clearing is still hypothesized);
* `Grok810DegreeZeroCompactBridgeScratch`
  (`rhoResidual810_eq_clearedCompact`, the sixteen
  `h^{7d} · depressed` identities);
* `Grok810DegreeZeroTowerOrders111to118Scratch`
  (`degreeZeroFace810_linearRoot_order118Ceiling` on `hclear` /
  `hderiv` / `hj`);
* `Grok810RouteAdapterScratch`
  (`normalized810ScaleTwo_nonzeroFace_false_of_linearRootFalse`,
  `PlaneKeller810NonzeroFaceExclusion`).

The algebraic identity
`degreeZeroClearedSource810 = 2^{62} · h^{119} · sourceRhoResidual810`
on the ninth-power face is proved block-by-block: the 215-term compact
is split into 24 groups of at most 9 terms; each group is substituted
with the integer-cleared bars and discharged by its own
`field_simp; ring`.  A one-shot 977-term `field_simp` is not used.
The in-flight aligned-square lane is a `λ = 0` instance and is not
imported.

CAS: `derive_810_degree_zero_clearing.py` (job `810-dz-clearing`).

**CLOSED:** `PlaneKeller810NonzeroFaceExclusion`.  No `sorry`, no new
axioms, no finite-root shortcut.
-/

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

variable {R : Type*} [CommRing R]

/-- Compact block `0` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock0_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    - (7245315 : R) * L * A ^ 8
    + (66242880 : R) * L * A ^ 6 * C0
    + (198728640 : R) * L * A ^ 5 * B ^ 2
    - (77552640 : R) * L * A ^ 5 * E0
    - (387763200 : R) * L * A ^ 4 * B * D0
    - (193881600 : R) * L * A ^ 4 * C0 ^ 2
    + (94003200 : R) * L * A ^ 4 * G0
    - (775526400 : R) * L * A ^ 3 * B ^ 2 * C0
    + (376012800 : R) * L * A ^ 3 * B * F0

/-- Compact block `1` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock1_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (376012800 : R) * L * A ^ 3 * C0 * E0
    + (188006400 : R) * L * A ^ 3 * D0 ^ 2
    - (193881600 : R) * L * A ^ 2 * B ^ 4
    + (564019200 : R) * L * A ^ 2 * B ^ 2 * E0
    + (1128038400 : R) * L * A ^ 2 * B * C0 * D0
    + (188006400 : R) * L * A ^ 2 * C0 ^ 3
    - (360972288 : R) * L * A ^ 2 * C0 * G0
    - (360972288 : R) * L * A ^ 2 * D0 * F0
    - (180486144 : R) * L * A ^ 2 * E0 ^ 2

/-- Compact block `2` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock2_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (376012800 : R) * L * A * B ^ 3 * D0
    + (564019200 : R) * L * A * B ^ 2 * C0 ^ 2
    - (360972288 : R) * L * A * B ^ 2 * G0
    - (721944576 : R) * L * A * B * C0 * F0
    - (721944576 : R) * L * A * B * D0 * E0
    - (360972288 : R) * L * A * C0 ^ 2 * E0
    - (360972288 : R) * L * A * C0 * D0 ^ 2
    + (339738624 : R) * L * A * E0 * G0
    + (169869312 : R) * L * A * F0 ^ 2

/-- Compact block `3` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock3_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (94003200 : R) * L * B ^ 4 * C0
    - (120324096 : R) * L * B ^ 3 * F0
    - (360972288 : R) * L * B ^ 2 * C0 * E0
    - (180486144 : R) * L * B ^ 2 * D0 ^ 2
    - (360972288 : R) * L * B * C0 ^ 2 * D0
    + (339738624 : R) * L * B * D0 * G0
    + (339738624 : R) * L * B * E0 * F0
    - (30081024 : R) * L * C0 ^ 4
    + (169869312 : R) * L * C0 ^ 2 * G0

/-- Compact block `4` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock4_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (339738624 : R) * L * C0 * D0 * F0
    + (169869312 : R) * L * C0 * E0 ^ 2
    + (169869312 : R) * L * D0 ^ 2 * E0
    - (150994944 : R) * L * G0 ^ 2
    - (64402800 : R) * A ^ 7 * B
    + (7360320 : R) * A ^ 7 * Q
    + (58882560 : R) * A ^ 6 * B * P
    + (73603200 : R) * A ^ 6 * D0
    - (7180800 : R) * A ^ 6 * S0

/-- Compact block `5` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock5_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (441619200 : R) * A ^ 5 * B * C0
    - (51701760 : R) * A ^ 5 * B * R
    - (60318720 : R) * A ^ 5 * C0 * Q
    - (68935680 : R) * A ^ 5 * D0 * P
    - (86169600 : R) * A ^ 5 * F0
    + (6266880 : R) * A ^ 5 * U0
    + (368016000 : R) * A ^ 4 * B ^ 3
    - (150796800 : R) * A ^ 4 * B ^ 2 * Q
    - (344678400 : R) * A ^ 4 * B * C0 * P

/-- Compact block `6` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock6_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    - (430848000 : R) * A ^ 4 * B * E0
    + (41779200 : R) * A ^ 4 * B * T0
    - (430848000 : R) * A ^ 4 * C0 * D0
    + (52224000 : R) * A ^ 4 * C0 * S0
    + (62668800 : R) * A ^ 4 * D0 * R
    + (73113600 : R) * A ^ 4 * E0 * Q
    + (83558400 : R) * A ^ 4 * F0 * P
    - (3342336 : R) * A ^ 4 * W0
    - (229785600 : R) * A ^ 3 * B ^ 3 * P

/-- Compact block `7` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock7_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    - (861696000 : R) * A ^ 3 * B ^ 2 * D0
    + (104448000 : R) * A ^ 3 * B ^ 2 * S0
    - (861696000 : R) * A ^ 3 * B * C0 ^ 2
    + (250675200 : R) * A ^ 3 * B * C0 * R
    + (292454400 : R) * A ^ 3 * B * D0 * Q
    + (334233600 : R) * A ^ 3 * B * E0 * P
    + (417792000 : R) * A ^ 3 * B * G0
    - (26738688 : R) * A ^ 3 * B * V0
    + (146227200 : R) * A ^ 3 * C0 ^ 2 * Q

/-- Compact block `8` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock8_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (334233600 : R) * A ^ 3 * C0 * D0 * P
    + (417792000 : R) * A ^ 3 * C0 * F0
    - (40108032 : R) * A ^ 3 * C0 * U0
    + (417792000 : R) * A ^ 3 * D0 * E0
    - (53477376 : R) * A ^ 3 * D0 * T0
    - (66846720 : R) * A ^ 3 * E0 * S0
    - (80216064 : R) * A ^ 3 * F0 * R
    - (93585408 : R) * A ^ 3 * G0 * Q
    - (861696000 : R) * A ^ 2 * B ^ 3 * C0

/-- Compact block `9` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock9_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (125337600 : R) * A ^ 2 * B ^ 3 * R
    + (438681600 : R) * A ^ 2 * B ^ 2 * C0 * Q
    + (501350400 : R) * A ^ 2 * B ^ 2 * D0 * P
    + (626688000 : R) * A ^ 2 * B ^ 2 * F0
    - (60162048 : R) * A ^ 2 * B ^ 2 * U0
    + (501350400 : R) * A ^ 2 * B * C0 ^ 2 * P
    + (1253376000 : R) * A ^ 2 * B * C0 * E0
    - (160432128 : R) * A ^ 2 * B * C0 * T0
    + (626688000 : R) * A ^ 2 * B * D0 ^ 2

/-- Compact block `10` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock10_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    - (200540160 : R) * A ^ 2 * B * D0 * S0
    - (240648192 : R) * A ^ 2 * B * E0 * R
    - (280756224 : R) * A ^ 2 * B * F0 * Q
    - (320864256 : R) * A ^ 2 * B * G0 * P
    + (626688000 : R) * A ^ 2 * C0 ^ 2 * D0
    - (100270080 : R) * A ^ 2 * C0 ^ 2 * S0
    - (240648192 : R) * A ^ 2 * C0 * D0 * R
    - (280756224 : R) * A ^ 2 * C0 * E0 * Q
    - (320864256 : R) * A ^ 2 * C0 * F0 * P

/-- Compact block `11` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock11_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (18874368 : R) * A ^ 2 * C0 * W0
    - (140378112 : R) * A ^ 2 * D0 ^ 2 * Q
    - (320864256 : R) * A ^ 2 * D0 * E0 * P
    - (401080320 : R) * A ^ 2 * D0 * G0
    + (37748736 : R) * A ^ 2 * D0 * V0
    - (401080320 : R) * A ^ 2 * E0 * F0
    + (56623104 : R) * A ^ 2 * E0 * U0
    + (75497472 : R) * A ^ 2 * F0 * T0
    + (94371840 : R) * A ^ 2 * G0 * S0

/-- Compact block `12` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock12_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    - (86169600 : R) * A * B ^ 5
    + (73113600 : R) * A * B ^ 4 * Q
    + (334233600 : R) * A * B ^ 3 * C0 * P
    + (417792000 : R) * A * B ^ 3 * E0
    - (53477376 : R) * A * B ^ 3 * T0
    + (1253376000 : R) * A * B ^ 2 * C0 * D0
    - (200540160 : R) * A * B ^ 2 * C0 * S0
    - (240648192 : R) * A * B ^ 2 * D0 * R
    - (280756224 : R) * A * B ^ 2 * E0 * Q

/-- Compact block `13` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock13_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    - (320864256 : R) * A * B ^ 2 * F0 * P
    + (18874368 : R) * A * B ^ 2 * W0
    + (417792000 : R) * A * B * C0 ^ 3
    - (240648192 : R) * A * B * C0 ^ 2 * R
    - (561512448 : R) * A * B * C0 * D0 * Q
    - (641728512 : R) * A * B * C0 * E0 * P
    - (802160640 : R) * A * B * C0 * G0
    + (75497472 : R) * A * B * C0 * V0
    - (320864256 : R) * A * B * D0 ^ 2 * P

/-- Compact block `14` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock14_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    - (802160640 : R) * A * B * D0 * F0
    + (113246208 : R) * A * B * D0 * U0
    - (401080320 : R) * A * B * E0 ^ 2
    + (150994944 : R) * A * B * E0 * T0
    + (188743680 : R) * A * B * F0 * S0
    + (226492416 : R) * A * B * G0 * R
    - (93585408 : R) * A * C0 ^ 3 * Q
    - (320864256 : R) * A * C0 ^ 2 * D0 * P
    - (401080320 : R) * A * C0 ^ 2 * F0

/-- Compact block `15` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock15_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (56623104 : R) * A * C0 ^ 2 * U0
    - (802160640 : R) * A * C0 * D0 * E0
    + (150994944 : R) * A * C0 * D0 * T0
    + (188743680 : R) * A * C0 * E0 * S0
    + (226492416 : R) * A * C0 * F0 * R
    + (264241152 : R) * A * C0 * G0 * Q
    - (133693440 : R) * A * D0 ^ 3
    + (94371840 : R) * A * D0 ^ 2 * S0
    + (226492416 : R) * A * D0 * E0 * R

/-- Compact block `16` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock16_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (264241152 : R) * A * D0 * F0 * Q
    + (301989888 : R) * A * D0 * G0 * P
    + (132120576 : R) * A * E0 ^ 2 * Q
    + (301989888 : R) * A * E0 * F0 * P
    - (33554432 : R) * A * E0 * W0
    + (377487360 : R) * A * F0 * G0
    - (67108864 : R) * A * F0 * V0
    - (100663296 : R) * A * G0 * U0
    + (16711680 : R) * B ^ 5 * P

/-- Compact block `17` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock17_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (104448000 : R) * B ^ 4 * D0
    - (16711680 : R) * B ^ 4 * S0
    + (208896000 : R) * B ^ 3 * C0 ^ 2
    - (80216064 : R) * B ^ 3 * C0 * R
    - (93585408 : R) * B ^ 3 * D0 * Q
    - (106954752 : R) * B ^ 3 * E0 * P
    - (133693440 : R) * B ^ 3 * G0
    + (12582912 : R) * B ^ 3 * V0
    - (140378112 : R) * B ^ 2 * C0 ^ 2 * Q

/-- Compact block `18` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock18_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    - (320864256 : R) * B ^ 2 * C0 * D0 * P
    - (401080320 : R) * B ^ 2 * C0 * F0
    + (56623104 : R) * B ^ 2 * C0 * U0
    - (401080320 : R) * B ^ 2 * D0 * E0
    + (75497472 : R) * B ^ 2 * D0 * T0
    + (94371840 : R) * B ^ 2 * E0 * S0
    + (113246208 : R) * B ^ 2 * F0 * R
    + (132120576 : R) * B ^ 2 * G0 * Q
    - (106954752 : R) * B * C0 ^ 3 * P

/-- Compact block `19` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock19_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    - (401080320 : R) * B * C0 ^ 2 * E0
    + (75497472 : R) * B * C0 ^ 2 * T0
    - (401080320 : R) * B * C0 * D0 ^ 2
    + (188743680 : R) * B * C0 * D0 * S0
    + (226492416 : R) * B * C0 * E0 * R
    + (264241152 : R) * B * C0 * F0 * Q
    + (301989888 : R) * B * C0 * G0 * P
    + (113246208 : R) * B * D0 ^ 2 * R
    + (264241152 : R) * B * D0 * E0 * Q

/-- Compact block `20` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock20_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (301989888 : R) * B * D0 * F0 * P
    - (33554432 : R) * B * D0 * W0
    + (150994944 : R) * B * E0 ^ 2 * P
    + (377487360 : R) * B * E0 * G0
    - (67108864 : R) * B * E0 * V0
    + (188743680 : R) * B * F0 ^ 2
    - (100663296 : R) * B * F0 * U0
    - (134217728 : R) * B * G0 * T0
    - (133693440 : R) * C0 ^ 3 * D0

/-- Compact block `21` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock21_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (31457280 : R) * C0 ^ 3 * S0
    + (113246208 : R) * C0 ^ 2 * D0 * R
    + (132120576 : R) * C0 ^ 2 * E0 * Q
    + (150994944 : R) * C0 ^ 2 * F0 * P
    - (16777216 : R) * C0 ^ 2 * W0
    + (132120576 : R) * C0 * D0 ^ 2 * Q
    + (301989888 : R) * C0 * D0 * E0 * P
    + (377487360 : R) * C0 * D0 * G0
    - (67108864 : R) * C0 * D0 * V0

/-- Compact block `22` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock22_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    (377487360 : R) * C0 * E0 * F0
    - (100663296 : R) * C0 * E0 * U0
    - (134217728 : R) * C0 * F0 * T0
    - (167772160 : R) * C0 * G0 * S0
    + (50331648 : R) * D0 ^ 3 * P
    + (188743680 : R) * D0 ^ 2 * F0
    - (50331648 : R) * D0 ^ 2 * U0
    + (188743680 : R) * D0 * E0 ^ 2
    - (134217728 : R) * D0 * E0 * T0

/-- Compact block `23` of `degreeZeroClearedCompact810`. -/
def degreeZeroCompactBlock23_810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) : R :=
    - (167772160 : R) * D0 * F0 * S0
    - (201326592 : R) * D0 * G0 * R
    - (83886080 : R) * E0 ^ 2 * S0
    - (201326592 : R) * E0 * F0 * R
    - (234881024 : R) * E0 * G0 * Q
    - (117440512 : R) * F0 ^ 2 * Q
    - (268435456 : R) * F0 * G0 * P
    + (268435456 : R) * G0 * W0

/-- The 215-term compact is the sum of the 24 blocks. -/
theorem degreeZeroCompact810_blockSum
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : R) :
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

/-! ## Compact-block expansions after `2^{34}` -/

section DegreeZeroCompactExpansions810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `0` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock0Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (403740669719347200 : R) * h ^ 95 * a6 ^ 4 * a0 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a6 ^ 3 * a5 * a1 * lambda
    + (706546172008857600 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 3 * a0 * lambda
    + (2119638516026572800 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (1261689592872960000 : R) * h ^ 87 * a7 * a6 ^ 4 * a1 * lambda
    + (403740669719347200 : R) * h ^ 87 * a7 * a6 ^ 3 * a5 * a2 * lambda
    + (333086052518461440 : R) * h ^ 87 * a6 ^ 5 * a2 * lambda
    + (1665430262592307200 : R) * h ^ 87 * a6 ^ 4 * a5 * a3 * lambda
    + (832715131296153600 : R) * h ^ 87 * a6 ^ 4 * a4 ^ 2 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a6 ^ 3 * a5 ^ 2 * a4 * lambda
    - (463670925380812800 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (927341850761625600 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (2031320244525465600 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (529909629006643200 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (1037739690138009600 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 4 * a2 * lambda
    - (2990204335108915200 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a5 * a3 * lambda
    - (1457251479768268800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a4 ^ 2 * lambda
    - (4371754439304806400 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (1373979966638653440 : R) * h ^ 79 * a7 * a6 ^ 5 * a3 * lambda
    - (6869899833193267200 : R) * h ^ 79 * a7 * a6 ^ 4 * a5 * a4 * lambda
    - (2081787828240384000 : R) * h ^ 79 * a7 * a6 ^ 3 * a5 ^ 3 * lambda
    - (284511003192852480 : R) * h ^ 79 * a6 ^ 6 * a4 * lambda
    - (853533009578557440 : R) * h ^ 79 * a6 ^ 5 * a5 ^ 2 * lambda
    + (135237353236070400 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (135237353236070400 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (1217136179124633600 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (231835462690406400 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (1134337799592345600 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (2012000622634598400 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (956321283597926400 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (1912642567195852800 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (2880989329725849600 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (11306315864132812800 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (2732346524565504000 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (3666548812488376320 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 5 * a4 * lambda
    + (6355958463096422400 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 4 * a5 ^ 2 * lambda
    + (1458118891363368960 : R) * h ^ 71 * a7 * a6 ^ 6 * a5 * lambda
    + (31118390974218240 : R) * h ^ 71 * a6 ^ 8 * lambda
    - (14791585510195200 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (321188713935667200 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (33809338309017600 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (575966227621478400 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (601323231353241600 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (278927041049395200 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (278927041049395200 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (2403567959172710400 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (6949888981991424000 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (1195401604497408000 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (6490345654399795200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (8865020429048217600 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (6493551627369185280 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 5 * a5 * lambda
    - (655708952671027200 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 7 * lambda
    + (31432119209164800 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (139199385069158400 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (67354541162496000 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (30507645114777600 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (996620807385907200 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (1890002385292492800 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (174329400655872000 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (4855068417746534400 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (5050668808352563200 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (9152657009462476800 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (2221595263909232640 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 6 * lambda
    - (12965749173780480 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (205200232022016000 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (191729323789516800 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (1832545848655872000 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (1301520382112563200 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (6092102929534156800 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (3087977982103388160 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    + (16764759905402880 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (345335234400092160 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (125866116171694080 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (2121043546511769600 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (2259872608606617600 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    - (25879225837731840 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (374223627468472320 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (950033679000698880 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    + (26432322321807360 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (231208843998182400 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    - (30317122767012480 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    + (1657967651320995 : R) * h ^ 7 * a7 ^ 16 * lambda

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `1` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock1Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1550364171722293248 : R) * h ^ 103 * a6 ^ 2 * a4 * a0 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 ^ 2 * a3 * a1 * lambda
    + (775182085861146624 : R) * h ^ 103 * a6 ^ 2 * a2 ^ 2 * lambda
    - (1356568650257006592 : R) * h ^ 95 * a7 ^ 2 * a6 * a4 * a0 * lambda
    - (1356568650257006592 : R) * h ^ 95 * a7 ^ 2 * a6 * a3 * a1 * lambda
    - (678284325128503296 : R) * h ^ 95 * a7 ^ 2 * a6 * a2 ^ 2 * lambda
    - (968977607326433280 : R) * h ^ 95 * a7 * a6 ^ 2 * a5 * a0 * lambda
    - (968977607326433280 : R) * h ^ 95 * a7 * a6 ^ 2 * a4 * a1 * lambda
    - (968977607326433280 : R) * h ^ 95 * a7 * a6 ^ 2 * a3 * a2 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a6 ^ 3 * a4 * a2 * lambda
    - (807481339438694400 : R) * h ^ 95 * a6 ^ 3 * a3 ^ 2 * lambda
    - (2422444018316083200 : R) * h ^ 95 * a6 ^ 2 * a5 ^ 2 * a2 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a6 ^ 2 * a5 * a4 * a3 * lambda
    - (807481339438694400 : R) * h ^ 95 * a6 ^ 2 * a4 ^ 3 * lambda
    + (296749392243720192 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (296749392243720192 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (148374696121860096 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (847855406410629120 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (847855406410629120 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (847855406410629120 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (363366602747412480 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 3 * a0 * lambda
    + (363366602747412480 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (2483005118773985280 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (1241502559386992640 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a3 ^ 2 * lambda
    + (2119638516026572800 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (4239277032053145600 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (706546172008857600 : R) * h ^ 87 * a7 ^ 2 * a6 * a4 ^ 3 * lambda
    + (4643017701772492800 : R) * h ^ 87 * a7 * a6 ^ 3 * a5 * a2 * lambda
    + (5046758371491840000 : R) * h ^ 87 * a7 * a6 ^ 3 * a4 * a3 * lambda
    + (3936471529763635200 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 ^ 2 * a3 * lambda
    + (3936471529763635200 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 * a4 ^ 2 * lambda
    + (832715131296153600 : R) * h ^ 87 * a6 ^ 2 * a5 ^ 4 * lambda
    - (185468370152325120 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (185468370152325120 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (185468370152325120 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (397432221754982400 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (317945777403985920 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (1245287628165611520 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (622643814082805760 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (463670925380812800 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (927341850761625600 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (154556975126937600 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (105981925801328640 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (5670033030371082240 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (6199942659377725440 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (3444412588543180800 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (3444412588543180800 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (1741131638164684800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 4 * a2 * lambda
    - (5400031457496268800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a5 * a3 * lambda
    - (2737866416534323200 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a4 ^ 2 * lambda
    - (3444412588543180800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (728625739884134400 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 ^ 4 * lambda
    - (2498145393888460800 : R) * h ^ 79 * a7 * a6 ^ 3 * a5 ^ 3 * lambda
    + (139101277614243840 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (69550638807121920 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (204787992043192320 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (102393996021596160 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (113268183200169984 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (2295171080635023360 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (2527006543325429760 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (753465253743820800 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (753465253743820800 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (2593245246951260160 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (6335732001810677760 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (3217545028624711680 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (3013861014975283200 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (159386880599654400 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (1567649319144652800 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (3762989210743603200 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (3632088915483033600 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (2810413568124518400 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 4 * a5 ^ 2 * lambda
    - (15214202239057920 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (38252851343917056 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (307664978612060160 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (341474316921077760 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (1426160688253894656 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (2442966188100157440 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (1243217668677304320 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (659282097025843200 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (2242207717194203136 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (4317687097470222336 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (1743595875650764800 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (901516641907507200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (5090128951246848000 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (1405206784062259200 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 5 * a5 * lambda
    + (3930335578423296 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (342011643904917504 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (308298903705354240 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (157319077319147520 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (1178975736686444544 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (1617197249429766144 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (276813957405081600 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (1252446238062673920 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (3330538942192680960 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (2869284201666969600 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (263476272011673600 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 6 * lambda
    - (30024277231140864 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (269187342604959744 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (196205099083628544 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (636257147541258240 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (932752854236528640 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (2260154573987512320 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (589202263218585600 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    + (22436184431001600 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (139519750381240320 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (93878693438423040 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (858855083920588800 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (534109479008993280 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    - (11108156149923840 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (157364934636994560 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (251352448947191808 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    + (11125916569313280 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (64818656622010368 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    - (8698363322535936 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    + (475691744201184 : R) * h ^ 7 * a7 ^ 16 * lambda

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `2` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock2Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1459166279268040704 : R) * h ^ 111 * a6 * a2 * a0 * lambda
    - (729583139634020352 : R) * h ^ 111 * a6 * a1 ^ 2 * lambda
    + (638385247179767808 : R) * h ^ 103 * a7 ^ 2 * a2 * a0 * lambda
    + (319192623589883904 : R) * h ^ 103 * a7 ^ 2 * a1 ^ 2 * lambda
    + (547187354725515264 : R) * h ^ 103 * a7 * a6 * a3 * a0 * lambda
    + (547187354725515264 : R) * h ^ 103 * a7 * a6 * a2 * a1 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 * a5 ^ 2 * a0 * lambda
    + (3100728343444586496 : R) * h ^ 103 * a6 * a5 * a4 * a1 * lambda
    + (3100728343444586496 : R) * h ^ 103 * a6 * a5 * a3 * a2 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 * a4 ^ 2 * a2 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 * a4 * a3 ^ 2 * lambda
    - (239394467692412928 : R) * h ^ 95 * a7 ^ 3 * a3 * a0 * lambda
    - (239394467692412928 : R) * h ^ 95 * a7 ^ 3 * a2 * a1 * lambda
    - (136796838681378816 : R) * h ^ 95 * a7 ^ 2 * a6 * a4 * a0 * lambda
    - (136796838681378816 : R) * h ^ 95 * a7 ^ 2 * a6 * a3 * a1 * lambda
    - (68398419340689408 : R) * h ^ 95 * a7 ^ 2 * a6 * a2 ^ 2 * lambda
    - (678284325128503296 : R) * h ^ 95 * a7 ^ 2 * a5 ^ 2 * a0 * lambda
    - (1356568650257006592 : R) * h ^ 95 * a7 ^ 2 * a5 * a4 * a1 * lambda
    - (1356568650257006592 : R) * h ^ 95 * a7 ^ 2 * a5 * a3 * a2 * lambda
    - (678284325128503296 : R) * h ^ 95 * a7 ^ 2 * a4 ^ 2 * a2 * lambda
    - (678284325128503296 : R) * h ^ 95 * a7 ^ 2 * a4 * a3 ^ 2 * lambda
    - (2325546257583439872 : R) * h ^ 95 * a7 * a6 ^ 2 * a5 * a0 * lambda
    - (2325546257583439872 : R) * h ^ 95 * a7 * a6 ^ 2 * a4 * a1 * lambda
    - (2325546257583439872 : R) * h ^ 95 * a7 * a6 ^ 2 * a3 * a2 * lambda
    - (2131750736118153216 : R) * h ^ 95 * a7 * a6 * a5 ^ 2 * a1 * lambda
    - (4263501472236306432 : R) * h ^ 95 * a7 * a6 * a5 * a4 * a2 * lambda
    - (2131750736118153216 : R) * h ^ 95 * a7 * a6 * a5 * a3 ^ 2 * lambda
    - (2131750736118153216 : R) * h ^ 95 * a7 * a6 * a4 ^ 2 * a3 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a6 * a5 ^ 3 * a3 * lambda
    - (2422444018316083200 : R) * h ^ 95 * a6 * a5 ^ 2 * a4 ^ 2 * lambda
    + (59848616923103232 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (59848616923103232 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (29924308461551616 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (1724210154213212160 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (1724210154213212160 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (1724210154213212160 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (932640947051692032 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (1865281894103384064 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (932640947051692032 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (932640947051692032 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (872079846593789952 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 3 * a0 * lambda
    + (2470892898682404864 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (2470892898682404864 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (1235446449341202432 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a3 ^ 2 * lambda
    + (1598813052088614912 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (3197626104177229824 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (532937684029538304 : R) * h ^ 87 * a7 ^ 2 * a6 * a4 ^ 3 * lambda
    + (706546172008857600 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 3 * a3 * lambda
    + (1059819258013286400 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 2 * a4 ^ 2 * lambda
    + (3633666027474124800 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 ^ 2 * a3 * lambda
    + (3633666027474124800 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 * a4 ^ 2 * lambda
    + (3835536362333798400 : R) * h ^ 87 * a7 * a6 * a5 ^ 3 * a4 * lambda
    - (309217854102700032 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (309217854102700032 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (309217854102700032 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (895591803242151936 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (1754045402232913920 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (1754045402232913920 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (877022701116456960 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (699480710288769024 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (1398961420577538048 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (233160236762923008 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (654059884945342464 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (1520083621493342208 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (1520083621493342208 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (3515571881581215744 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (3515571881581215744 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (1678047158521036800 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    - (2725249520605593600 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a5 * a3 * lambda
    - (1362624760302796800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a4 ^ 2 * lambda
    - (7494436181665382400 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (1198605113229312000 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 ^ 4 * lambda
    + (299866507708465152 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (294450519588470784 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (294450519588470784 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (147225259794235392 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (628878045012295680 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (1048831426000060416 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (1048831426000060416 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (842556310120562688 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (842556310120562688 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (325894421839085568 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (3486805358863712256 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (1743402679431856128 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (5760780054338469888 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (524389737037824000 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (681312380151398400 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (4769186661059788800 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (2759945984409600000 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    - (32797899280613376 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (194122540275204096 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (167910243198566400 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (167910243198566400 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (299885989680119808 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (1402429211532066816 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (701214605766033408 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (1085859348376190976 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (1024381551573467136 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (5016588219102265344 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (2000712443558363136 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (979386546467635200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (2297655032020992000 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    + (19328551127875584 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (87407974925991936 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (174379475411140608 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (87189737705570304 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (550468675379920896 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (1712221609852403712 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (347040782978383872 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (1283747475458359296 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (2278052515666722816 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (811719827914752000 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    - (8131411584221184 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (125209197674496000 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (188263424273154048 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (616154708519682048 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (729696521284485120 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (1008634334766170112 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (101464978489344000 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    + (10237029755387904 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (128207290695155712 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (75614909629464576 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (458589622612525056 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (150048128995688448 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    - (9774991186329600 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (90553069154598912 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (86911066844430336 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    + (6564869615517696 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (24671362694381568 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    - (3435609780486144 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    + (187884909870336 : R) * h ^ 7 * a7 ^ 16 * lambda

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `3` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock3Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1459166279268040704 : R) * h ^ 111 * a5 * a3 * a0 * lambda
    - (1459166279268040704 : R) * h ^ 111 * a5 * a2 * a1 * lambda
    - (729583139634020352 : R) * h ^ 111 * a4 ^ 2 * a0 * lambda
    + (1094374709451030528 : R) * h ^ 103 * a7 * a6 * a3 * a0 * lambda
    + (1094374709451030528 : R) * h ^ 103 * a7 * a6 * a2 * a1 * lambda
    + (1641562064176545792 : R) * h ^ 103 * a7 * a5 * a4 * a0 * lambda
    + (729583139634020352 : R) * h ^ 103 * a7 * a5 * a3 * a1 * lambda
    + (364791569817010176 : R) * h ^ 103 * a7 * a5 * a2 ^ 2 * lambda
    + (91197892454252544 : R) * h ^ 103 * a7 * a4 ^ 2 * a1 * lambda
    + (516788057240764416 : R) * h ^ 103 * a5 ^ 3 * a1 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a5 ^ 2 * a4 * a2 * lambda
    + (775182085861146624 : R) * h ^ 103 * a5 ^ 2 * a3 ^ 2 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a5 * a4 ^ 2 * a3 * lambda
    + (129197014310191104 : R) * h ^ 103 * a4 ^ 4 * lambda
    - (319192623589883904 : R) * h ^ 95 * a7 ^ 3 * a3 * a0 * lambda
    - (319192623589883904 : R) * h ^ 95 * a7 ^ 3 * a2 * a1 * lambda
    - (889179451428962304 : R) * h ^ 95 * a7 ^ 2 * a6 * a4 * a0 * lambda
    - (547187354725515264 : R) * h ^ 95 * a7 ^ 2 * a6 * a3 * a1 * lambda
    - (273593677362757632 : R) * h ^ 95 * a7 ^ 2 * a6 * a2 ^ 2 * lambda
    - (512988145055170560 : R) * h ^ 95 * a7 ^ 2 * a5 ^ 2 * a0 * lambda
    - (341992096703447040 : R) * h ^ 95 * a7 ^ 2 * a5 * a4 * a1 * lambda
    - (227994731135631360 : R) * h ^ 95 * a7 ^ 2 * a5 * a3 * a2 * lambda
    - (11399736556781568 : R) * h ^ 95 * a7 ^ 2 * a4 ^ 2 * a2 * lambda
    - (1162773128791719936 : R) * h ^ 95 * a7 * a6 * a5 ^ 2 * a1 * lambda
    - (2325546257583439872 : R) * h ^ 95 * a7 * a6 * a5 * a4 * a2 * lambda
    - (1162773128791719936 : R) * h ^ 95 * a7 * a6 * a5 * a3 ^ 2 * lambda
    - (1162773128791719936 : R) * h ^ 95 * a7 * a6 * a4 ^ 2 * a3 * lambda
    - (1098174621636624384 : R) * h ^ 95 * a7 * a5 ^ 3 * a2 * lambda
    - (3294523864909873152 : R) * h ^ 95 * a7 * a5 ^ 2 * a4 * a3 * lambda
    - (1098174621636624384 : R) * h ^ 95 * a7 * a5 * a4 ^ 3 * lambda
    - (403740669719347200 : R) * h ^ 95 * a5 ^ 4 * a4 * lambda
    + (234407082948820992 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (159596311794941952 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (79798155897470976 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (441739791575285760 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (213745060439654400 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (170996048351723520 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (431765022088101888 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (749532678608388096 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (367641503956205568 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (340567129633849344 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (872079846593789952 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (872079846593789952 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (436039923296894976 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a3 ^ 2 * lambda
    + (2107526295934992384 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (4215052591869984768 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (702508765311664128 : R) * h ^ 87 * a7 ^ 2 * a6 * a4 ^ 3 * lambda
    + (1235446449341202432 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 3 * a3 * lambda
    + (1853169674011803648 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 2 * a4 ^ 2 * lambda
    + (1211222009158041600 : R) * h ^ 87 * a7 * a6 * a5 ^ 3 * a4 * lambda
    + (252337918574592000 : R) * h ^ 87 * a7 * a5 ^ 5 * lambda
    - (106605348894277632 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (59225193830154240 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (49873847435919360 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (82826210920366080 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (590648850348244992 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (556805882445299712 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (275731127967154176 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (605121172148846592 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (1190649047090724864 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (196244683616157696 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (218019961648447488 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (1308119769890684928 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (1308119769890684928 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (2068161580637356032 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (2068161580637356032 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (1331334858399547392 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    - (1362624760302796800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (851640475189248000 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 ^ 4 * lambda
    + (37483313463558144 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (94526526468390912 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (87824728219189248 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (43327904959954944 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (205128462690680832 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (738511448929468416 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (733345943302176768 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (556143495409041408 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (554584937676668928 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (258898704457531392 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (1102590535211679744 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (551295267605839872 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (2249844882011062272 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (394317425572577280 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (681312380151398400 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (1135520633585664000 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    - (4099737410076672 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (62079302677561344 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (103531372081053696 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (102562839775936512 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (214129133595131904 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (583171947941068800 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (291229732203134976 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (489986198593339392 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (184805983116066816 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (1280725334605430784 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (915253287349911552 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (127746071278387200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (745185415790592000 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    + (6092428557680640 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (58486792315207680 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (76650186729848832 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (38263429445713920 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (143256155961950208 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (518838824667709440 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (158155428650287104 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (250009706997743616 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (802647491185999872 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (239523883646976000 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    - (5269905041522688 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (36679828899889152 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (60015372417368064 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (139629084668854272 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (260594636181995520 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (314080128059572224 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (29940485455872000 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    + (3097369516179456 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (30770234193346560 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (26552991442010112 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (144735607594156032 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (45818714989264896 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    - (2372719973105664 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (28395290620329984 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (26891720815804416 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    + (2025294559690752 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (7657269592227840 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    - (1065656621869056 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    + (58278096508464 : R) * h ^ 7 * a7 ^ 16 * lambda

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `4` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock4Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (648518346341351424 : R) * h ^ 119 * a0 ^ 2 * lambda
    - (162129586585337856 : R) * h ^ 111 * a7 * a1 * a0 * lambda
    - (1459166279268040704 : R) * h ^ 111 * a4 * a3 * a1 * lambda
    - (729583139634020352 : R) * h ^ 111 * a4 * a2 ^ 2 * lambda
    - (729583139634020352 : R) * h ^ 111 * a3 ^ 2 * a2 * lambda
    + (20266198323167232 : R) * h ^ 103 * a7 ^ 2 * a2 * a0 * lambda
    + (10133099161583616 : R) * h ^ 103 * a7 ^ 2 * a1 ^ 2 * lambda
    + (911978924542525440 : R) * h ^ 103 * a7 * a5 * a3 * a1 * lambda
    + (455989462271262720 : R) * h ^ 103 * a7 * a5 * a2 ^ 2 * lambda
    + (729583139634020352 : R) * h ^ 103 * a7 * a4 ^ 2 * a1 * lambda
    + (1641562064176545792 : R) * h ^ 103 * a7 * a4 * a3 * a2 * lambda
    + (273593677362757632 : R) * h ^ 103 * a7 * a3 ^ 3 * lambda
    - (2533274790395904 : R) * h ^ 95 * a7 ^ 3 * a3 * a0 * lambda
    - (2533274790395904 : R) * h ^ 95 * a7 ^ 3 * a2 * a1 * lambda
    - (341992096703447040 : R) * h ^ 95 * a7 ^ 2 * a6 * a3 * a1 * lambda
    - (170996048351723520 : R) * h ^ 95 * a7 ^ 2 * a6 * a2 ^ 2 * lambda
    - (683984193406894080 : R) * h ^ 95 * a7 ^ 2 * a5 * a4 * a1 * lambda
    - (797981558974709760 : R) * h ^ 95 * a7 ^ 2 * a5 * a3 * a2 * lambda
    - (501588408498388992 : R) * h ^ 95 * a7 ^ 2 * a4 ^ 2 * a2 * lambda
    - (512988145055170560 : R) * h ^ 95 * a7 ^ 2 * a4 * a3 ^ 2 * lambda
    + (316659348799488 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (75127430502678528 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (37563715251339264 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (227994731135631360 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (270743743223562240 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (142496706959769600 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (398990779487354880 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (206620225091665920 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (233694599414022144 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (1264493347523788800 : R) * h ^ 80 * a6 ^ 6 * a3
    - (39582418599936 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (47419737482723328 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (56771083876958208 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (89060441849856000 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (122903409752801280 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (64123518131896320 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (71248353479884800 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (162090004166737920 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (29211824926752768 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (123365204636467200 : R) * h ^ 78 * a6 ^ 6 * b5
    - (3319295037249945600 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 5 * a3
    - (632246673761894400 : R) * h ^ 72 * a7 * a6 ^ 6 * a4
    - (1106431679083315200 : R) * h ^ 72 * a6 ^ 7 * a5
    + (4947802324992 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (17928361724608512 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (24630159973810176 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (12899539136544768 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (13359066277478400 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (41190454355558400 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (46355959982850048 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (25604877031833600 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (27163434764206080 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (284511003192852480 : R) * h ^ 71 * a7 * a6 ^ 6 * a5 * lambda
    + (323833662170726400 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 5 * b5
    + (92523903477350400 : R) * h ^ 70 * a7 * a6 ^ 6 * b6
    + (126449334752378880 : R) * h ^ 70 * a6 ^ 7 * b7
    + (1011594678019031040 : R) * h ^ 70 * a6 ^ 6 * a5 * b8
    + (3630478946992128000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (1659647518624972800 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 5 * a4
    + (2874746594761113600 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 6 * a5
    + (829823759312486400 : R) * h ^ 64 * a7 * a6 ^ 8
    - (541165879296 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (5260750822047744 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (7988226853699584 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (8956759158816768 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (5705434556006400 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (13804368486727680 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (7258426010763264 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (7792788661862400 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (746841383381237760 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 5 * a5 * lambda
    - (231165190094192640 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 7 * lambda
    - (354193067999232000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (242875246628044800 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 5 * b6
    - (427730295450501120 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 6 * b7
    - (2655436029799956480 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 5 * a5 * b8
    - (885145343266652160 : R) * h ^ 62 * a7 * a6 ^ 7 * b8
    - (2117779385745408000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (1815239473496064000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (3098873101182566400 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    - (2240030207429836800 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 7
    + (511469401669632 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (2161358539849728 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (2584047746285568 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (1353687792353280 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (1784687760506880 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (3952057107087360 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (695784701952000 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (816857763073228800 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (677773735121387520 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 6 * lambda
    + (206612622999552000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (265644800999424000 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (614524972978667520 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (2904383157593702400 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    + (2613607515102904320 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 6 * b8
    + (694896360947712000 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (1058889692872704000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (1767967612207104000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    + (2473790855656243200 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 6
    - (201905607278592 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (652416538116096 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (715798175809536 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (482048338821120 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (504443908915200 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (476500361792716800 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (849980349197844480 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (67794766921728000 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (154959467249664000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (486830992942694400 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (1694223508596326400 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (3302850359092838400 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    - (121606863165849600 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    - (347448180473856000 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    - (558398861475840000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (1381249197696614400 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (58779915780096 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (170664149385216 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (88876228018176 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (156469230777139200 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (590904030973132800 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (11864084211302400 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (50846075191296000 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (229937251142860800 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (555917088758169600 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (2315352706488729600 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    + (8867167105843200 : R) * h ^ 32 * a7 ^ 12 * a3
    + (60803431582924800 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    + (90119371810406400 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (356199960281088000 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (14893424050176 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (27402061591609344 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (245897257962700800 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (865089473740800 : R) * h ^ 30 * a7 ^ 12 * b5
    - (8898063158476800 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (64807560004239360 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (97285490532679680 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (972289948935782400 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    - (4433583552921600 : R) * h ^ 24 * a7 ^ 13 * a4
    - (4908610362163200 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (4817577349939200 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (1998555760115712 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (61234257993007104 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (648817105305600 : R) * h ^ 22 * a7 ^ 13 * b6
    + (10099919605923840 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (7093733684674560 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (244548435805470720 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (207824229043200 : R) * h ^ 16 * a7 ^ 14 * a5
    - (27143147740262400 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (8446515978507264 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (671796044451840 : R) * h ^ 14 * a7 ^ 14 * b7
    - (34106152502231040 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (6374543578233600 : R) * h ^ 8 * a7 ^ 15 * a6
    + (497678232594816 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (2034311965593600 : R) * h ^ 6 * a7 ^ 15 * b8
    - (496380990151200 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `5` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock5Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1480382455637606400 : R) * h ^ 88 * a6 ^ 5 * a1
    + (107664178591825920 : R) * h ^ 86 * a6 ^ 5 * b3
    + (3238336621707264000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 4 * a1
    + (370095613909401600 : R) * h ^ 80 * a7 * a6 ^ 5 * a2
    + (7586960085142732800 : R) * h ^ 80 * a6 ^ 5 * a5 * a4
    + (6322466737618944000 : R) * h ^ 80 * a6 ^ 4 * a5 ^ 3
    - (333086052518461440 : R) * h ^ 79 * a7 * a6 ^ 5 * a3 * lambda
    - (1665430262592307200 : R) * h ^ 79 * a7 * a6 ^ 4 * a5 * a4 * lambda
    - (235515390669619200 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 4 * b3
    - (53832089295912960 : R) * h ^ 78 * a7 * a6 ^ 5 * b4
    - (888229473382563840 : R) * h ^ 78 * a6 ^ 5 * a5 * b6
    - (1036267718946324480 : R) * h ^ 78 * a6 ^ 5 * a4 * b7
    - (1184305964510085120 : R) * h ^ 78 * a6 ^ 5 * a3 * b8
    - (2590669297365811200 : R) * h ^ 78 * a6 ^ 4 * a5 ^ 2 * b7
    - (5921529822550425600 : R) * h ^ 78 * a6 ^ 4 * a5 * a4 * b8
    - (2833544543993856000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (809584155426816000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 4 * a2
    + (763322203688140800 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 5 * a3
    - (12432899529768960000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 4 * a5 * a4
    - (11064316790833152000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 3 * a5 ^ 3
    - (5690220063857049600 : R) * h ^ 72 * a7 * a6 ^ 6 * a4
    - (18967400212856832000 : R) * h ^ 72 * a7 * a6 ^ 5 * a5 ^ 2
    + (728625739884134400 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (2914502959536537600 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (1561340871180288000 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 5 * a4 * lambda
    + (1405206784062259200 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 4 * a5 ^ 2 * lambda
    + (206075966835916800 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (117757695334809600 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 4 * b4
    + (16822527904972800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 5 * b5
    + (1943001973024358400 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a5 * b6
    + (2266835635195084800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a4 * b7
    + (2590669297365811200 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a3 * b8
    + (4533671270390169600 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2 * b7
    + (10362677189463244800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 * a4 * b8
    + (666172105036922880 : R) * h ^ 70 * a7 * a6 ^ 6 * b6
    + (5310872059599912960 : R) * h ^ 70 * a7 * a6 ^ 5 * a5 * b7
    + (6069568068114186240 : R) * h ^ 70 * a7 * a6 ^ 5 * a4 * b8
    + (6291625436459827200 : R) * h ^ 70 * a7 * a6 ^ 4 * a5 ^ 2 * b8
    + (1239675737997312000 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (708386135998464000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    - (1669767320567808000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (7235658389127168000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (7260957893984256000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    + (10093779594982195200 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 5 * a4
    + (35600017548902400000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 4 * a5 ^ 2
    + (16003743929597952000 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 6 * a5
    - (637547522398617600 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (1912642567195852800 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (3233276720735846400 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (2459111872108953600 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (1897029158484049920 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 5 * a5 * lambda
    - (90158235490713600 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (103037983417958400 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (36799279792128000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (1700126726396313600 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (1983481180795699200 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (2266835635195084800 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (2975221771193548800 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (6800506905585254400 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (1655757309046947840 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 5 * b6
    - (11050823721576038400 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a5 * b7
    - (12629512824658329600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    - (11010344513804697600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    - (2283027318303621120 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 6 * b7
    - (9270895128430510080 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 5 * a5 * b8
    - (271179067686912000 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    - (309918934499328000 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (1461046405496832000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (1571731739246592000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (2117779385745408000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (6198378689986560000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (25995241240657920000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    - (32672774481562828800 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    - (4000935982399488000 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 7
    + (278927041049395200 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (557854082098790400 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (2669730250044211200 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (1613792166071500800 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (3870824243134464000 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (572166373417943040 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 6 * lambda
    + (19722114013593600 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (45079117745356800 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (32199369818112000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (743805442798387200 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (867773016598118400 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (991740590397849600 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (867773016598118400 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (1983481180795699200 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (1709326546344345600 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (9173600461180108800 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (10484114812777267200 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (7225538587184332800 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (5430699714423029760 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (19004988048644505600 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    + (3078732888208834560 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 6 * b8
    + (23728168422604800 : R) * h ^ 48 * a7 ^ 10 * a1
    + (67794766921728000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (639207802404864000 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (4842483351552000 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    + (231632120315904000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (1057044937310208000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (9117704367636480000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (26514078742609920000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    + (8936169125865062400 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 6
    - (61015290229555200 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (61015290229555200 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (1098275224131993600 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (470689381770854400 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (3142910051824435200 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (1320571623513784320 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (1725684976189440 : R) * h ^ 46 * a7 ^ 10 * b3
    - (9861057006796800 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (14087224295424000 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (162707440612147200 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (189825347380838400 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (216943254149529600 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (94912673690419200 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (216943254149529600 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (937806645952512000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (3796506947616768000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (4338865082990592000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (2107448754595430400 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (5355862054089523200 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (15513656378366361600 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (7169557682800558080 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    - (5932042105651200 : R) * h ^ 40 * a7 ^ 11 * a2
    + (139826706776064000 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (30931362408038400 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (405557980692480000 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    - (1501169838981120000 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (10665050744291328000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (8102608068044390400 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (5338837895086080 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (224993882721484800 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (51481651131187200 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (1268246389771468800 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (1259704437807513600 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (862842488094720 : R) * h ^ 38 * a7 ^ 11 * b4
    + (3081580314624000 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (14236901053562880 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (16609717895823360 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (18982534738083840 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (288259827145113600 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (783029557945958400 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (894890923366809600 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (230502207533875200 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (2801684776904294400 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (6299102343698841600 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (6908274171445248000 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (12234836842905600 : R) * h ^ 32 * a7 ^ 12 * a3
    - (187388972944588800 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    + (88186161659904000 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    + (2113592655347712000 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (3748104200257536000 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (18352255264358400 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (254071481971507200 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (635093067261542400 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (269638277529600 : R) * h ^ 30 * a7 ^ 12 * b5
    - (47040323502735360 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (64362656846315520 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (73557322110074880 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (819392205658521600 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (1271151879782400000 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (3522774570526310400 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (21040211843481600 : R) * h ^ 24 * a7 ^ 13 * a4
    - (160532579192832000 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    - (886332495691776000 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (20187480790794240 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (178286273593344000 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (3181731674849280 : R) * h ^ 22 * a7 ^ 13 * b6
    + (126947386300170240 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (101882823164559360 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (1001821760284262400 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (1139774691686400 : R) * h ^ 16 * a7 ^ 14 * a5
    + (79862337321984000 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (26390767417620480 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (8133069873438720 : R) * h ^ 14 * a7 ^ 14 * b7
    - (150503660320849920 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (4849434202099200 : R) * h ^ 8 * a7 ^ 15 * a6
    + (1607101076730240 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (9321584843612160 : R) * h ^ 6 * a7 ^ 15 * b8
    - (1020690212539200 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `6` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock6Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (57420895248973824 : R) * h ^ 94 * a6 ^ 4 * b1
    - (7401912278188032000 : R) * h ^ 88 * a6 ^ 4 * a5 * a2
    - (7401912278188032000 : R) * h ^ 88 * a6 ^ 4 * a4 * a3
    + (403740669719347200 : R) * h ^ 87 * a7 * a6 ^ 4 * a1 * lambda
    + (100486566685704192 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 3 * b1
    + (14355223812243456 : R) * h ^ 86 * a7 * a6 ^ 4 * b2
    + (717761190612172800 : R) * h ^ 86 * a6 ^ 4 * a5 * b4
    + (897201488265216000 : R) * h ^ 86 * a6 ^ 4 * a4 * b5
    + (1076641785918259200 : R) * h ^ 86 * a6 ^ 4 * a3 * b6
    + (1256082083571302400 : R) * h ^ 86 * a6 ^ 4 * a2 * b7
    + (1435522381224345600 : R) * h ^ 86 * a6 ^ 4 * a1 * b8
    - (1009351674298368000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 4 * a1
    + (12953346486829056000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a5 * a2
    + (12953346486829056000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a4 * a3
    + (5551434208641024000 : R) * h ^ 80 * a7 * a6 ^ 5 * a2
    + (7401912278188032000 : R) * h ^ 80 * a7 * a6 ^ 4 * a5 * a3
    + (3700956139094016000 : R) * h ^ 80 * a7 * a6 ^ 4 * a4 ^ 2
    - (706546172008857600 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (277571710432051200 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 4 * a2 * lambda
    - (1110286841728204800 : R) * h ^ 79 * a7 * a6 ^ 3 * a5 ^ 3 * lambda
    - (65944309387493376 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (25121641671426048 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 3 * b2
    - (2691604464795648 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 4 * b3
    - (1256082083571302400 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a5 * b4
    - (1570102604464128000 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a4 * b5
    - (1884123125356953600 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a3 * b6
    - (2198143646249779200 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a2 * b7
    - (2512164167142604800 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a1 * b8
    - (538320892959129600 : R) * h ^ 78 * a7 * a6 ^ 5 * b4
    - (1009351674298368000 : R) * h ^ 78 * a7 * a6 ^ 4 * a5 * b5
    - (1211222009158041600 : R) * h ^ 78 * a7 * a6 ^ 4 * a4 * b6
    - (1413092344017715200 : R) * h ^ 78 * a7 * a6 ^ 4 * a3 * b7
    - (1614962678877388800 : R) * h ^ 78 * a7 * a6 ^ 4 * a2 * b8
    - (3947686548366950400 : R) * h ^ 78 * a6 ^ 3 * a5 ^ 3 * b8
    + (1766365430022144000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (8500633631981568000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (8500633631981568000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (10493051780726784000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 4 * a2
    - (12953346486829056000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    - (6476673243414528000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    - (3816611018440704000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 5 * a3
    - (4163575656480768000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 4 * a5 * a4
    + (2775717104320512000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 3 * a5 ^ 3
    + (463670925380812800 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (485750493256089600 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (129323183269478400 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (1457251479768268800 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (2498145393888460800 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 4 * a5 ^ 2 * lambda
    + (19233756904685568 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (16486077346873344 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (4710307813392384 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (824303867343667200 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (1030379834179584000 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (1236455801015500800 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (1442531767851417600 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (1648607734687334400 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (1099520423869022208 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 4 * b4
    + (1766365430022144000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (2119638516026572800 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (2472911602031001600 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (2826184688035430400 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (546732156911616000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 5 * b5
    + (757013755723776000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a5 * b6
    + (883182715011072000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a4 * b7
    + (1009351674298368000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a3 * b8
    + (5181338594731622400 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a5 ^ 3 * b8
    + (8882294733825638400 : R) * h ^ 70 * a7 * a6 ^ 4 * a5 ^ 2 * b8
    - (1159177313452032000 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (2479351475994624000 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    + (2479351475994624000 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (7737048576294912000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (8500633631981568000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (4250316815990784000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (7232044174147584000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (7286257398841344000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    - (3643128699420672000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    + (1676995750526976000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 5 * a4
    - (5377951889620992000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 4 * a5 ^ 2
    - (135237353236070400 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (318773761199308800 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (226315570721587200 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (637547522398617600 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (48693332724940800 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (4007441569362739200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (1873609045416345600 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 5 * a5 * lambda
    - (2103692161449984 : R) * h ^ 62 * a7 ^ 8 * b1
    - (4808439226171392 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (3091139502538752 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (240421961308569600 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (300527451635712000 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (360632941962854400 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (420738432289996800 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (480843922617139200 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (893780907591204864 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (1159177313452032000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (1391012776142438400 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (1622848238832844800 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (1854683701523251200 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (1100981880980766720 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (1324774072516608000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (1545569751269376000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (1766365430022144000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (2266835635195084800 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    - (325936478158848000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 5 * b6
    - (404792077713408000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a5 * b7
    - (462619517386752000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    - (14248681135511961600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    - (6661721050369228800 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 5 * a5 * b8
    + (338093383090176000 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    - (271179067686912000 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    - (271179067686912000 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (2753046119448576000 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    - (2479351475994624000 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    - (1239675737997312000 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    - (5350845277274112000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (4781606417989632000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    + (1593868805996544000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (3153402569687040000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    + (8500633631981568000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    + (4096712679358464000 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    + (14791585510195200 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (92975680349798400 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (148519593286041600 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (92975680349798400 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (85213332268646400 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (2390803208994816000 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (3567895528970649600 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (468402261354086400 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 6 * lambda
    + (525923040362496 : R) * h ^ 54 * a7 ^ 9 * b2
    + (901582354907136 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (26296152018124800 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (32870190022656000 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (39444228027187200 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (46018266031718400 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (52592304036249600 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (361148131879944192 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (338093383090176000 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (405712059708211200 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (473330736326246400 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (540949412944281600 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (880238772627701760 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (869382985089024000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (1014280149270528000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (1159177313452032000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (330580196799283200 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (649057811413598208 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (708386135998464000 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (809584155426816000 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (8500633631981568000 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (147197119168512000 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (12802995143678361600 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    + (1665430262592307200 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 6 * b8
    - (36978963775488000 : R) * h ^ 48 * a7 ^ 10 * a1
    + (463997950230528000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    + (271179067686912000 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    + (135589533843456000 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    + (1913472707198976000 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (1394635205246976000 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (232439200874496000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (2308579818209280000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    - (4980840018739200000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    - (7784567289151488000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    - (1082909163257856000 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 6
    - (10169215038259200 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (43318214708428800 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (55921249301299200 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (627585842361139200 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (2697459082356326400 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (1029210348139315200 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (98610570067968 : R) * h ^ 46 * a7 ^ 10 * b3
    - (72464681775661056 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (36978963775488000 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (44374756530585600 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (51770549285683200 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (59166342040780800 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (348739299736289280 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (253570037317632000 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (295831710203904000 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (338093383090176000 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (511988379747876864 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (464878401748992000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (531289601998848000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (2231416328395161600 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (290533763891331072 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (9795968280664473600 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (3698590471107379200 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    - (28504617910272000 : R) * h ^ 40 * a7 ^ 11 * a2
    - (325051694972928000 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    - (152538225573888000 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    - (812845419724800000 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (1278415604809728000 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (5881245443555328000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (2389263060566016000 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (4737929733734400 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (16310364379545600 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (61015290229555200 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (1011874629943296000 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (935362085146066944 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (5768718348976128 : R) * h ^ 38 * a7 ^ 11 * b4
    + (68331842347991040 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (27734222831616000 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (32356593303552000 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (36978963775488000 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (199522388847624192 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (135589533843456000 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (154959467249664000 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (216943254149529600 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (226689600901349376 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (3732309454041907200 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (3402691897926352896 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    + (20258983084032000 : R) * h ^ 32 * a7 ^ 12 * a3
    + (134681568215040000 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (120759428579328000 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (2209642447896576000 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (2183221717122416640 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (1783946104012800 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (188353342498406400 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (449940274966167552 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (5282984251883520 : R) * h ^ 30 * a7 ^ 12 * b5
    - (38292157215277056 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (14830105264128000 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (16948691730432000 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (87133444299030528 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (708939562667212800 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (1659482592686112768 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    - (8010905075712000 : R) * h ^ 24 * a7 ^ 13 * a4
    + (413398642212864000 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (1057468658346885120 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (13927599466905600 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (120796618320838656 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (2882144288636928 : R) * h ^ 22 * a7 ^ 13 * b6
    + (16425978669563904 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (53812096244121600 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (452270902009135104 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (30885018329088000 : R) * h ^ 16 * a7 ^ 14 * a5
    - (286300781982351360 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (17156538690859008 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (1206757684887552 : R) * h ^ 14 * a7 ^ 14 * b7
    - (65250702259126272 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (41063262151188480 : R) * h ^ 8 * a7 ^ 15 * a6
    + (1006569837189504 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (3886741477441536 : R) * h ^ 6 * a7 ^ 15 * b8
    - (2435063799114240 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `7` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock7Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (7177611906121728000 : R) * h ^ 96 * a6 ^ 3 * a5 * a0
    - (459367161991790592 : R) * h ^ 94 * a6 ^ 3 * a5 * b2
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a5 * a0
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 ^ 4 * a0
    - (897201488265216000 : R) * h ^ 88 * a7 * a6 ^ 3 * a5 * a1
    - (14803824556376064000 : R) * h ^ 88 * a6 ^ 3 * a5 ^ 2 * a3
    - (14803824556376064000 : R) * h ^ 88 * a6 ^ 3 * a5 * a4 ^ 2
    + (1614962678877388800 : R) * h ^ 87 * a7 * a6 ^ 3 * a5 * a2 * lambda
    + (602919400114225152 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a5 * b2
    + (344525371493842944 : R) * h ^ 86 * a7 * a6 ^ 4 * b2
    + (172262685746921472 : R) * h ^ 86 * a7 * a6 ^ 3 * a5 * b3
    + (1794402976530432000 : R) * h ^ 86 * a6 ^ 3 * a5 ^ 2 * b5
    + (4306567143673036800 : R) * h ^ 86 * a6 ^ 3 * a5 * a4 * b6
    + (5024328334285209600 : R) * h ^ 86 * a6 ^ 3 * a5 * a3 * b7
    + (5742089524897382400 : R) * h ^ 86 * a6 ^ 3 * a5 * a2 * b8
    + (2512164167142604800 : R) * h ^ 86 * a6 ^ 3 * a4 ^ 2 * b7
    + (4121519336718336000 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    + (8635564324552704000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 3 * a0
    + (1177576953348096000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    + (672901116198912000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 4 * a1
    - (3925256511160320000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a5 * a2
    + (19430019730243584000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a3
    + (19430019730243584000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 * a4 ^ 2
    + (22205736834564096000 : R) * h ^ 80 * a7 * a6 ^ 4 * a5 * a3
    + (11102868417282048000 : R) * h ^ 80 * a7 * a6 ^ 4 * a4 ^ 2
    + (25906692973658112000 : R) * h ^ 80 * a7 * a6 ^ 3 * a5 ^ 2 * a4
    - (2119638516026572800 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (1211222009158041600 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 4 * a2 * lambda
    - (1312157176587878400 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a5 * a3 * lambda
    - (353273086004428800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a4 ^ 2 * lambda
    - (263777237549973504 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (552676116771373056 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 3 * b2
    - (226094775042834432 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (129197014310191104 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 4 * b3
    - (43065671436730368 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a5 * b4
    - (2355153906696192000 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b5
    - (5652369376070860800 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b6
    - (6594430938749337600 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * b7
    - (7536492501427814400 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a2 * b8
    - (3297215469374668800 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * b7
    - (2691604464795648000 : R) * h ^ 78 * a7 * a6 ^ 4 * a5 * b5
    - (3229925357754777600 : R) * h ^ 78 * a7 * a6 ^ 4 * a4 * b6
    - (3768246250713907200 : R) * h ^ 78 * a7 * a6 ^ 4 * a3 * b7
    - (4306567143673036800 : R) * h ^ 78 * a7 * a6 ^ 4 * a2 * b8
    - (4037406697193472000 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 ^ 2 * b6
    - (9420615626784768000 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 * a4 * b7
    - (7177611906121728000 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 * a3 * b8
    - (2512164167142604800 : R) * h ^ 78 * a7 * a6 ^ 3 * a4 ^ 2 * b8
    - (601054903271424000 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    - (5151899170897920000 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    - (515189917089792000 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (1079445540569088000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    + (5151899170897920000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (8500633631981568000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (8500633631981568000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    + (2943942383370240000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 4 * a2
    - (31766540193890304000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    - (16633274466041856000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    - (34002534527926272000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    - (8327151312961536000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 5 * a3
    - (31920746699685888000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 4 * a5 * a4
    - (8095841554268160000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 3 * a5 ^ 3
    + (927341850761625600 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (1943001973024358400 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (1722206294271590400 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (463670925380812800 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (984117882440908800 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (1122903737656934400 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (38467513809371136 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (329721546937466880 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (98916464081240064 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (207253543789264896 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (56523693760708608 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (1030379834179584000 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (2472911602031001600 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (2885063535702835200 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (3297215469374668800 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (1442531767851417600 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (32299253577547776 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 4 * b4
    + (4326754177159004160 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (5181338594731622400 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (6044895027186892800 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (6908451459642163200 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (5299096290066432000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b6
    + (12364558010155008000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (9420615626784768000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (3297215469374668800 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (1009351674298368000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 5 * b5
    + (5046758371491840000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a5 * b6
    + (5887884766740480000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a4 * b7
    + (5383208929591296000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a3 * b8
    + (4710307813392384000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2 * b7
    + (8074813394386944000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 * a4 * b8
    + (1352373532360704000 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    + (75131862908928000 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    + (643987396362240000 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (2253955887267840000 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    + (1239675737997312000 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    + (1239675737997312000 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    - (4722574239989760000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (16191683108536320000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (9080222288707584000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (14876108855967744000 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (12895519047155712000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (47011518021107712000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (10625792039976960000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    + (9368045227081728000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 5 * a4
    + (12722036728135680000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 4 * a5 ^ 2
    - (135237353236070400 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (1159177313452032000 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (753465253743820800 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (202856029854105600 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (1578689103082291200 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (1473811155674726400 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (676581044178124800 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (404134947717120000 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (86551906071085056 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (14425317678514176 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (123645580101550080 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (24729116020310016 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (150263725817856000 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (360632941962854400 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (420738432289996800 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (480843922617139200 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (210369216144998400 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (51813385947316224 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (2587725354982440960 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (3091139502538752000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (3606329419628544000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (4121519336718336000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (2318354626904064000 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (5409494129442816000 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (4121519336718336000 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (1442531767851417600 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (1920291560352645120 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (8023925247474401280 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (9359283493797888000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (8635564324552704000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (6182279005077504000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (10598192580132864000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (1514027511447552000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 5 * b6
    - (5053767758118912000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a5 * b7
    - (4878533092442112000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    - (3252355394961408000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    - (131480760090624000 : R) * h ^ 56 * a7 ^ 9 * a0
    - (169046691545088000 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (328701900226560000 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (2817444859084800000 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    - (3364834145992704000 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    - (2113083644313600000 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    - (2169432541495296000 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    - (7227225220841472000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (25043634864783360000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (4648784017489920000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (15166231749328896000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (18648746925490176000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    - (6234520839782400000 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    + (304284044781158400 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (109880349504307200 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (29583171020390400 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (941831567179776000 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (644792380607692800 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (1073273994687283200 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (530427118878720000 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (388363827806208000 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (8414768645799936 : R) * h ^ 54 * a7 ^ 9 * b2
    + (32456964776656896 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (3606329419628544 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (30911395025387520 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (681338665351249920 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (811424119416422400 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (946661472652492800 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (1081898825888563200 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (338093383090176000 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (788884560543744000 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (601054903271424000 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (210369216144998400 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (1449032973948026880 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (4735515320049991680 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (5522191923806208000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (5151899170897920000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (2704747064721408000 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (4636709253808128000 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (2816406593690664960 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (7966418487239245824 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (7740115182944256000 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (4268716455886848000 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (1278774972776448000 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (3245346008334336000 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    + (16435095011328000 : R) * h ^ 48 * a7 ^ 10 * a1
    - (739579275509760000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    + (219525911937024000 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    + (172568497618944000 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    + (1649211472871424000 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (5610488633229312000 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    + (677947669217280000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (9227658986520576000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (9866016284737536000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (10027379346898944000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    + (935178125967360000 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 6
    - (29583171020390400 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (247230786384691200 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (94032222171955200 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (631661075103744000 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (232061864509440000 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (608354440172273664 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (83352832966656000 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (3155538242174976 : R) * h ^ 46 * a7 ^ 10 * b3
    - (8114241194164224 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (66491698674401280 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (78888456054374400 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (92036532063436800 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (105184608072499200 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (541754397189734400 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (1226554494796431360 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (1429853265985536000 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (1352373532360704000 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (394442280271872000 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (676186766180352000 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (2070833471202263040 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (4651987854786822144 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (4556210829262848000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (1867563449450496000 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (2338968356800954368 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (5094296031596642304 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (742556895805440000 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    + (71903540674560000 : R) * h ^ 40 * a7 ^ 11 * a2
    - (87164700327936000 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    - (428376349212672000 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    - (2538656174702592000 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    - (2185689449889792000 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (6062285651674398720 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (1626571290968064000 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (24036326454067200 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (163037609931571200 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (33842355240960000 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (352453619229917184 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (149868701703733248 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (788884560543744 : R) * h ^ 38 * a7 ^ 11 * b4
    + (100301036983418880 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (117240924198666240 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (136616727281664000 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (131480760090624000 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (751352170099507200 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (1188837293385842688 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (1176283228667904000 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (272353003044864000 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (1685919928399429632 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (2959186485024129024 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (1344053828521033728 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (11299127820288000 : R) * h ^ 32 * a7 ^ 12 * a3
    + (286669511589888000 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    + (163383370579968000 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    + (1661733812510392320 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (1085876437820375040 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (15513830896435200 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (89155102486560768 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (105792748888522752 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (7354705017569280 : R) * h ^ 30 * a7 ^ 12 * b5
    - (134365706232791040 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (111654899539771392 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (111964084764672000 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (597460093092495360 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (751112016466280448 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (956610910221238272 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    - (6748981886976000 : R) * h ^ 24 * a7 ^ 13 * a4
    - (189668866612592640 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    - (336512163568680960 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (8259041076314112 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (36538003487784960 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (9468155516682240 : R) * h ^ 22 * a7 ^ 13 * b6
    + (103905527543365632 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (69904622243807232 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (333808885888450560 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    + (5133928352501760 : R) * h ^ 16 * a7 ^ 14 * a5
    + (42782871811276800 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (6154014982090752 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (7085855191252992 : R) * h ^ 14 * a7 ^ 14 * b7
    - (56961503425462272 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (92109483863040 : R) * h ^ 8 * a7 ^ 15 * a6
    + (403259222483712 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (3795144712568832 : R) * h ^ 6 * a7 ^ 15 * b8
    - (318677532378240 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `8` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock8Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (7177611906121728000 : R) * h ^ 96 * a6 ^ 3 * a4 * a1
    + (7177611906121728000 : R) * h ^ 96 * a6 ^ 3 * a3 * a2
    - (689050742987685888 : R) * h ^ 94 * a6 ^ 3 * a4 * b3
    - (918734323983581184 : R) * h ^ 94 * a6 ^ 3 * a3 * b4
    - (1148417904979476480 : R) * h ^ 94 * a6 ^ 3 * a2 * b5
    - (1378101485975371776 : R) * h ^ 94 * a6 ^ 3 * a1 * b6
    - (1607785066971267072 : R) * h ^ 94 * a6 ^ 3 * a0 * b7
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    - (4486007441326080000 : R) * h ^ 88 * a7 * a6 ^ 3 * a5 * a1
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 ^ 3 * a4 * a2
    - (2691604464795648000 : R) * h ^ 88 * a7 * a6 ^ 3 * a3 ^ 2
    - (14803824556376064000 : R) * h ^ 88 * a6 ^ 2 * a5 ^ 3 * a4
    + (226094775042834432 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 3 * a0 * lambda
    + (1614962678877388800 : R) * h ^ 87 * a7 * a6 ^ 3 * a4 * a3 * lambda
    + (904379100171337728 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (1205838800228450304 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a3 * b4
    + (1507298500285562880 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a2 * b5
    + (1808758200342675456 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a1 * b6
    + (2110217900399788032 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a0 * b7
    + (430656714367303680 : R) * h ^ 86 * a7 * a6 ^ 3 * a5 * b3
    + (803892533485633536 : R) * h ^ 86 * a7 * a6 ^ 3 * a4 * b4
    + (1004865666857041920 : R) * h ^ 86 * a7 * a6 ^ 3 * a3 * b5
    + (1205838800228450304 : R) * h ^ 86 * a7 * a6 ^ 3 * a2 * b6
    + (1406811933599858688 : R) * h ^ 86 * a7 * a6 ^ 3 * a1 * b7
    + (1607785066971267072 : R) * h ^ 86 * a7 * a6 ^ 3 * a0 * b8
    + (5742089524897382400 : R) * h ^ 86 * a6 ^ 3 * a4 * a3 * b8
    + (4121519336718336000 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    + (4121519336718336000 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    - (753649250142781440 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 3 * a0
    + (5887884766740480000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    + (7065461720088576000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (3532730860044288000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    + (1682252790497280000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 4 * a1
    + (2243003720663040000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a5 * a2
    - (1682252790497280000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a4 * a3
    + (12953346486829056000 : R) * h ^ 80 * a7 ^ 2 * a6 * a5 ^ 3 * a4
    + (33308605251846144000 : R) * h ^ 80 * a7 * a6 ^ 3 * a5 ^ 2 * a4
    + (9252390347735040000 : R) * h ^ 80 * a7 * a6 ^ 2 * a5 ^ 4
    - (296749392243720192 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (84785540641062912 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (2119638516026572800 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (1009351674298368000 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a5 * a3 * lambda
    - (807481339438694400 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a4 ^ 2 * lambda
    - (395665856324960256 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (527554475099947008 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (659443093874933760 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (791331712649920512 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (923220331424907264 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (565236937607086080 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (1318886187749867520 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (1582663425299841024 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (1846440662849814528 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (2110217900399788032 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (161496267887738880 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 4 * b3
    - (358880595306086400 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a5 * b4
    - (502432833428520960 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a4 * b5
    - (602919400114225152 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a3 * b6
    - (703405966799929344 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a2 * b7
    - (803892533485633536 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a1 * b8
    - (7536492501427814400 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 * a3 * b8
    - (3588805953060864000 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 * a3 * b8
    - (2871044762448691200 : R) * h ^ 78 * a7 * a6 ^ 3 * a4 ^ 2 * b8
    - (601054903271424000 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    - (601054903271424000 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    + (989164640812400640 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    - (2575949585448960000 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (3091139502538752000 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    - (1545569751269376000 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    - (2269779577578455040 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (2943942383370240000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    + (2207956787527680000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (2833544543993856000 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    - (700938662707200000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 4 * a2
    + (1752346656768000000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    + (1626177697480704000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    - (38860039460487168000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    - (8095841554268160000 : R) * h ^ 72 * a7 ^ 3 * a6 * a5 ^ 4
    - (24981453938884608000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 4 * a5 * a4
    - (24287524662804480000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 3 * a5 ^ 3
    + (129827859106627584 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (111281022091395072 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (927341850761625600 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (26495481450332160 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (1324774072516608000 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (1059819258013286400 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (378506877861888000 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (757013755723776000 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (57701270714056704 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (76935027618742272 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (96168784523427840 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (115402541428113408 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (134636298332798976 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (247291160203100160 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (461610165712453632 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (577012707140567040 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (692415248568680448 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (807817789996793856 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (923220331424907264 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (247291160203100160 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (471030781339238400 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (659443093874933760 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (791331712649920512 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (923220331424907264 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (1055108950199894016 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (3297215469374668800 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (116636193474478080 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 4 * b4
    + (179440297653043200 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (226094775042834432 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (263777237549973504 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (301459700057112576 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (4710307813392384000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (3768246250713907200 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (1345802232397824000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a3 * b8
    + (2691604464795648000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 * a4 * b8
    - (432759530355425280 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    + (375659314544640000 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    + (450791177453568000 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    + (225395588726784000 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    + (1047123506485002240 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (1287974792724480000 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (965981094543360000 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (960951859638435840 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    - (2299954987008000000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    - (2134358227943424000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (14876108855967744000 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (1770965339996160000 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    - (735985595842560000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (34757795936993280000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (28082450391367680000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    + (6245363484721152000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 5 * a4
    + (23420113067704320000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 4 * a5 ^ 2
    - (18933229453049856 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (48685447164985344 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (135237353236070400 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (34775319403560960 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (579588656726016000 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (463670925380812800 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (586874914124857344 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (993580554387456000 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (252337918574592000 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (157711199109120000 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (36063294196285440 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (67318149166399488 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (84147686457999360 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (100977223749599232 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (117806761041199104 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (134636298332798976 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (139101277614243840 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (206075966835916800 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (288506353570283520 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (346207624284340224 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (403908894998396928 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (461610165712453632 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (480843922617139200 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (177029068653330432 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (235515390669619200 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (296749392243720192 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (346207624284340224 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (395665856324960256 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (2060759668359168000 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (1648607734687334400 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (51869461040332800 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (68972364410388480 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (82430386734366720 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (2154965824627015680 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (3532730860044288000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (897201488265216000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    - (560750930165760000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    + (63110764843499520 : R) * h ^ 56 * a7 ^ 9 * a0
    - (176372048178708480 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    - (187829657272320000 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (140872242954240000 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (456265070322647040 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (1006230306816000000 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (933781724725248000 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    - (1859513606995968000 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    + (1161829928203714560 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (17461258261364736000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (10625792039976960000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (10352425961521152000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (33218195116523520000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    - (9758380444876800000 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    + (7099961044893696 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (15214202239057920 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (84523345772544000 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (67618676618035200 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (335581832244363264 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (434691492544512000 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (385454056182644736 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (206995948830720000 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (98569499443200000 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (33809338309017600 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (30052745163571200 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (42073843228999680 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (50488611874799616 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (58903380520599552 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (67318149166399488 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (98401274164150272 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (103037983417958400 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (129827859106627584 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (151465835624398848 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (173103812142170112 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (300527451635712000 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (240421961308569600 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (78137137425285120 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (90526228288634880 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (108189882588856320 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (1282822893553582080 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (1545569751269376000 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (18126273817608192 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (22373962113613824 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (1389933330601869312 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (735985595842560000 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (350469331353600000 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    + (5177054928568320 : R) * h ^ 48 * a7 ^ 10 * a1
    + (82222432470958080 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (146741919744000000 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (136176501522432000 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (679668323041935360 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (3687834074480640000 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    + (1307470504919040000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (6684846550155264000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (17283442991431680000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (16416270974976000000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    + (1463757066731520000 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 6
    - (2218737826529280 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (83424542277500928 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (63392509329408000 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (216114120376713216 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (90560727613440000 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (149630471544766464 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (14785424916480000 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (2958317102039040 : R) * h ^ 46 * a7 ^ 10 * b3
    - (23516273090494464 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (15026372581785600 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (18933229453049856 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (22088767695224832 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (25244305937399808 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (42986158707179520 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (39605224876277760 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (47333073632624640 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (335839427202908160 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (225395588726784000 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (27134211806724096 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (29365825274118144 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (793907662235369472 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (321993698181120000 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (5440160195936256 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (536950557873537024 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (52570399703040000 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    - (3430826083614720 : R) * h ^ 40 * a7 ^ 11 * a2
    + (174091678745886720 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    - (266630068174848000 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    - (2095258993164288000 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    - (3893325169950720000 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (10850631908925112320 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (2846142958141440000 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (7543708610199552 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (52288254778540032 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (13206772776960000 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (83189084385705984 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (25318623232917504 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (2005081591382016 : R) * h ^ 38 * a7 ^ 11 * b4
    + (10119322785546240 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (5775761961123840 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (6902739904757760 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (32541488122429440 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (14796760408915968 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (12847548557426688 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (197070876410118144 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (46957414318080000 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (8100920621531136 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (302255484482617344 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (91164082471698432 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (16400427232788480 : R) * h ^ 32 * a7 ^ 12 * a3
    + (318409002713088000 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    + (318842677493760000 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    + (3520738661152849920 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (2273516653620756480 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (4543790173913088 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (19886758447546368 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (16831533281181696 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (842298619330560 : R) * h ^ 30 * a7 ^ 12 * b5
    - (3437785843236864 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (1873600831291392 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (17782772802256896 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (4384774340739072 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (73540006563545088 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (61540758070493184 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    - (18876972269568000 : R) * h ^ 24 * a7 ^ 13 * a4
    - (561262222143651840 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    - (955574599318241280 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (1696409963200512 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (5395880540897280 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (279983582871552 : R) * h ^ 22 * a7 ^ 13 * b6
    + (1007218194382848 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (6444611631316992 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (20098569927131136 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    + (35274272638402560 : R) * h ^ 16 * a7 ^ 14 * a5
    + (223158951989084160 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (828743047888896 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (80450111078400 : R) * h ^ 14 * a7 ^ 14 * b7
    - (3154859560796160 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    - (27503156613488640 : R) * h ^ 8 * a7 ^ 15 * a6
    + (48651126322176 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (189396815118336 : R) * h ^ 6 * a7 ^ 15 * b8
    + (1399936633267200 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `9` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock9Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (10766417859182592000 : R) * h ^ 96 * a6 ^ 2 * a5 ^ 2 * a1
    + (21532835718365184000 : R) * h ^ 96 * a6 ^ 2 * a5 * a4 * a2
    + (10766417859182592000 : R) * h ^ 96 * a6 ^ 2 * a5 * a3 ^ 2
    - (1033576114481528832 : R) * h ^ 94 * a6 ^ 2 * a5 ^ 2 * b3
    - (2756202971950743552 : R) * h ^ 94 * a6 ^ 2 * a5 * a4 * b4
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 ^ 2 * a1
    - (18841231253569536000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    - (16149626788773888000 : R) * h ^ 88 * a7 * a6 ^ 3 * a5 * a1
    - (16149626788773888000 : R) * h ^ 88 * a7 * a6 ^ 3 * a4 * a2
    - (8074813394386944000 : R) * h ^ 88 * a7 * a6 ^ 3 * a3 ^ 2
    - (16149626788773888000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 ^ 2 * a2
    - (18841231253569536000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 * a4 * a3
    + (2422444018316083200 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 ^ 2 * a3 * lambda
    + (2422444018316083200 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 * a4 ^ 2 * lambda
    + (904379100171337728 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 ^ 2 * b3
    + (2411677600456900608 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a4 * b4
    + (1550364171722293248 : R) * h ^ 86 * a7 * a6 ^ 3 * a5 * b3
    + (2067152228963057664 : R) * h ^ 86 * a7 * a6 ^ 3 * a4 * b4
    + (2239414914709979136 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 ^ 2 * b4
    + (1722626857469214720 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a4 * b5
    + (2153283571836518400 : R) * h ^ 86 * a6 ^ 2 * a5 ^ 3 * b6
    + (7536492501427814400 : R) * h ^ 86 * a6 ^ 2 * a5 ^ 2 * a4 * b7
    + (8613134287346073600 : R) * h ^ 86 * a6 ^ 2 * a5 ^ 2 * a3 * b8
    + (8613134287346073600 : R) * h ^ 86 * a6 ^ 2 * a5 * a4 ^ 2 * b8
    + (2060759668359168000 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    + (4121519336718336000 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    + (2060759668359168000 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    + (18841231253569536000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    + (18841231253569536000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (9420615626784768000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    + (14130923440177152000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    + (16486077346873344000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (6056110045790208000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 4 * a1
    + (19177681811668992000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a5 * a2
    + (14130923440177152000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a4 * a3
    + (2859829743845376000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a3
    - (1345802232397824000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 * a4 ^ 2
    - (2119638516026572800 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (2119638516026572800 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (3633666027474124800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a5 * a3 * lambda
    - (1816833013737062400 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a4 ^ 2 * lambda
    - (5299096290066432000 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (197832928162480128 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (527554475099947008 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (1808758200342675456 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (2411677600456900608 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (1959488050371231744 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (1507298500285562880 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (581386564395859968 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 4 * b3
    - (2713137300514013184 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a5 * b4
    - (1291970143101911040 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a4 * b5
    - (1238138053805998080 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b5
    - (645985071550955520 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b6
    - (1884123125356953600 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 3 * b6
    - (6594430938749337600 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a4 * b7
    - (7536492501427814400 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a3 * b8
    - (7536492501427814400 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * a4 ^ 2 * b8
    - (4844888036632166400 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 ^ 2 * b6
    - (11304738752141721600 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 * a4 * b7
    - (12919701431019110400 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 * a3 * b8
    - (6459850715509555200 : R) * h ^ 78 * a7 * a6 ^ 3 * a4 ^ 2 * b8
    - (6594430938749337600 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 ^ 3 * b7
    - (22609477504283443200 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 ^ 2 * a4 * b8
    - (7212658839257088000 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (7212658839257088000 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    - (3606329419628544000 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    - (3091139502538752000 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    - (3606329419628544000 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    - (8831827150110720000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (22005969315692544000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (16486077346873344000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (2502351025864704000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    + (1177576953348096000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (5299096290066432000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 4 * a2
    - (714957435961344000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    + (1009351674298368000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    + (10682305219657728000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    + (463670925380812800 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (463670925380812800 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (4239277032053145600 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (2119638516026572800 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (4636709253808128000 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (1362624760302796800 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (6813123801513984000 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (2075479380276019200 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (692415248568680448 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (923220331424907264 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (428638011018706944 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (329721546937466880 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (847855406410629120 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (3118223772465758208 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (1507298500285562880 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (1083370797080248320 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (565236937607086080 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (412151933671833600 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (1442531767851417600 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (1648607734687334400 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (1648607734687334400 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (775182085861146624 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 4 * b4
    + (1453466410989649920 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (484488803663216640 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (6096484112762142720 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b6
    + (13377274190034370560 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (15072985002855628800 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (7536492501427814400 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (5770127071405670400 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 3 * b7
    + (19783292816248012800 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 2 * a4 * b8
    + (3633666027474124800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a5 * b6
    + (4239277032053145600 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a4 * b7
    + (4844888036632166400 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a3 * b8
    + (13071104182163865600 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2 * b7
    + (29876809559231692800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 * a4 * b8
    + (10362677189463244800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a5 ^ 3 * b8
    + (901582354907136000 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    + (901582354907136000 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    + (450791177453568000 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    + (4765506733080576000 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (8243038673436672000 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    + (6311076484349952000 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (547389286907904000 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    - (257594958544896000 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (7451854157905920000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (597988296622080000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    - (1177576953348096000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    - (9347017067200512000 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    - (1072436153942016000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    - (14735483036762112000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    - (5312238889992192000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    - (1622848238832844800 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (811424119416422400 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (1014280149270528000 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (1987161108774912000 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (7868495603712393216 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (1816044457741516800 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (2129101187973120000 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (3522479632102195200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (86551906071085056 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (115402541428113408 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (457488646375735296 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (1170511491628007424 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (577012707140567040 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (236987361861304320 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (123645580101550080 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (1095146566613729280 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (1666271388987555840 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (565236937607086080 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (2552398046381998080 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (5213721960948695040 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (5770127071405670400 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (2885063535702835200 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (1262215296869990400 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (4327595303554252800 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (393647152976363520 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (5813865643958599680 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (6323588239479275520 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (7065461720088576000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (15247413589070315520 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (34608986658900541440 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (9067342540780339200 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    - (908416506868531200 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 5 * b6
    - (8478554064106291200 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a5 * b7
    - (9689776073264332800 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    - (18353377944325324800 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    - (1126977943633920000 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    - (1000192924975104000 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    - (788884560543744000 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (3847824693264384000 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    - (112697794363392000 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (450791177453568000 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (2044659983450112000 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    + (1741065925165056000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    + (17090505517459046400 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    + (4648209028743168000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    + (5042815591514112000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    + (9394330426933248000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    + (202856029854105600 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (101428014927052800 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (1072239014943129600 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (2972710220347736064 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (397259725130956800 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (3044827608920358912 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (4030397420088066048 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (1914416818185830400 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (108189882588856320 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (142450012075327488 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (72126588392570880 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (568769668467130368 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (623379799678648320 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (216379765177712640 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (355481042791956480 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (667170942631280640 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (721265883925708800 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (360632941962854400 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (551989196881920000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (3448828502118236160 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (3500715486625136640 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (3812405386464460800 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (5835813785834618880 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (13127039087447900160 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (1983481180795699200 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (1725991363050209280 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (12317086939223162880 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (13945455070024826880 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (21091433614298578944 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (1788444997897420800 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (10516182756596121600 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    + (98610570067968000 : R) * h ^ 48 * a7 ^ 10 * a1
    + (862842488094720000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (5282709110784000 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (56348897181696000 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (1050504440315904000 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (6492801677760921600 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (1016795725037568000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    - (7278437551885516800 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    - (10779997450555883520 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    - (5338606231093248000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    - (253570037317632000 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (365014068718731264 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (1605243233384792064 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (1503923891330875392 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (2691899516163981312 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (330010684135833600 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (9466614726524928 : R) * h ^ 46 * a7 ^ 10 * b3
    - (128475485574266880 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (75507522223472640 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (27047470647214080 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (283998441795747840 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (896430455736238080 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (851995325387243520 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (901582354907136000 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (729295601774100480 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (1620594282945576960 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (1291654720703692800 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (6613106573243842560 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (7408431007751208960 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (7916150671043198976 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (3095417418814586880 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (14912797737920495616 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (1935116413068902400 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    - (70876347236352000 : R) * h ^ 40 * a7 ^ 11 * a2
    + (278662905593856000 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (803323965446553600 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (3879873128536473600 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (4038097094395822080 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (7546907909192417280 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (960744589885440000 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (22187378265292800 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (369356455607795712 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (181496716241928192 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (1390484127894994944 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (547078649237471232 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (10649941567340544 : R) * h ^ 38 * a7 ^ 11 * b4
    + (63392509329408000 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (85791195959132160 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (76916244653015040 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (78888456054374400 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (475101701666242560 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (1553750403663790080 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (1720331830957178880 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (963199873975320576 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (2115498597049958400 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (7782962002711805952 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (3249450004204486656 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (27349025292288000 : R) * h ^ 32 * a7 ^ 12 * a3
    - (904619912645836800 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (489992023525294080 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (3923748992487260160 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (1603664175672852480 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (31311937576894464 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (312189288796127232 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (356156946555863040 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (5177054928568320 : R) * h ^ 30 * a7 ^ 12 * b5
    - (85755977898393600 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (134788322961653760 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (147422802251612160 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (713421060896194560 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (1769394111372066816 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (2147310568199946240 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (77886942452121600 : R) * h ^ 24 * a7 ^ 13 * a4
    + (887928890555105280 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (1052299258704691200 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (25718508183158784 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (113778741201076224 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (6070713219809280 : R) * h ^ 22 * a7 ^ 13 * b6
    + (118717881620889600 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (147928951818289152 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (697923353268191232 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (73831586197340160 : R) * h ^ 16 * a7 ^ 14 * a5
    - (339206687503810560 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (17842440302346240 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (7799287177543680 : R) * h ^ 14 * a7 ^ 14 * b7
    - (111617727977226240 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (53729854849843200 : R) * h ^ 8 * a7 ^ 15 * a6
    + (1099350015547392 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (7030986610507776 : R) * h ^ 6 * a7 ^ 15 * b8
    - (3347114583214080 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `10` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock10Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (10766417859182592000 : R) * h ^ 96 * a6 ^ 2 * a4 ^ 2 * a3
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 ^ 2 * a5 * a0 * lambda
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 ^ 2 * a4 * a1 * lambda
    - (3445253714938429440 : R) * h ^ 94 * a6 ^ 2 * a5 * a3 * b5
    - (4134304457926115328 : R) * h ^ 94 * a6 ^ 2 * a5 * a2 * b6
    - (4823355200913801216 : R) * h ^ 94 * a6 ^ 2 * a5 * a1 * b7
    - (5512405943901487104 : R) * h ^ 94 * a6 ^ 2 * a5 * a0 * b8
    - (1722626857469214720 : R) * h ^ 94 * a6 ^ 2 * a4 ^ 2 * b5
    - (4134304457926115328 : R) * h ^ 94 * a6 ^ 2 * a4 * a3 * b6
    - (4823355200913801216 : R) * h ^ 94 * a6 ^ 2 * a4 * a2 * b7
    - (5512405943901487104 : R) * h ^ 94 * a6 ^ 2 * a4 * a1 * b8
    + (3875910429305733120 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a5 * a0
    + (3875910429305733120 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 * a4 ^ 2 * a3
    - (13458022323978240000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 * a4 * a3
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 ^ 2 * a4 ^ 3
    + (1356568650257006592 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (1356568650257006592 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (1162773128791719936 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 3 * a0 * lambda
    + (1841057453920223232 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (1065875368059076608 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (3014597000571125760 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a3 * b5
    + (3617516400685350912 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a2 * b6
    + (4220435800799576064 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a1 * b7
    + (4823355200913801216 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a0 * b8
    + (1507298500285562880 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 ^ 2 * b5
    + (3617516400685350912 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a3 * b6
    + (4220435800799576064 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a2 * b7
    + (4823355200913801216 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a1 * b8
    + (2583940286203822080 : R) * h ^ 86 * a7 * a6 ^ 3 * a3 * b5
    + (3100728343444586496 : R) * h ^ 86 * a7 * a6 ^ 3 * a2 * b6
    + (3617516400685350912 : R) * h ^ 86 * a7 * a6 ^ 3 * a1 * b7
    + (4134304457926115328 : R) * h ^ 86 * a7 * a6 ^ 3 * a0 * b8
    + (3875910429305733120 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a4 * b5
    + (6718244744129937408 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a3 * b6
    + (7837952201484926976 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a2 * b7
    + (8957659658839916544 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a1 * b8
    + (3359122372064968704 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 ^ 2 * b6
    + (5426274601028026368 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a3 * b7
    + (6201456686889172992 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a2 * b8
    - (3391421625642516480 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    - (3391421625642516480 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    + (2060759668359168000 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    - (2906932821979299840 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 3 * a0
    - (5167880572407644160 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    - (3229925357754777600 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (11775769533480960000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (4710307813392384000 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    + (5046758371491840000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a4 * a3
    + (4205631976243200000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a3
    + (8411263952486400000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 * a4 ^ 2
    - (296749392243720192 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (296749392243720192 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (1356568650257006592 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (1610925272180195328 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (932640947051692032 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (1017426487692754944 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (1029538707784335360 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (496601023754797056 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (659443093874933760 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (791331712649920512 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (923220331424907264 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (329721546937466880 : R) * h ^ 78 * a7 ^ 4 * a4 ^ 2 * b5
    - (791331712649920512 : R) * h ^ 78 * a7 ^ 4 * a4 * a3 * b6
    - (923220331424907264 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (3014597000571125760 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (3617516400685350912 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (4220435800799576064 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (4823355200913801216 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (3391421625642516480 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (5878464151113695232 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (6858208176299311104 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (7837952201484926976 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (2939232075556847616 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 ^ 2 * b6
    - (4747990275899523072 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (5426274601028026368 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (2099451482540605440 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a4 * b5
    - (4069705950771019776 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a3 * b6
    - (4747990275899523072 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a2 * b7
    - (5426274601028026368 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a1 * b8
    - (1211222009158041600 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b5
    - (5232479079562739712 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b6
    - (6104558926156529664 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * b7
    - (6976638772750319616 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a2 * b8
    - (2826184688035430400 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * b7
    - (3875910429305733120 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 * a3 * b8
    + (741873480609300480 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (741873480609300480 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (3391421625642516480 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    + (4521895500856688640 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    + (2826184688035430400 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    - (2575949585448960000 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    - (1030379834179584000 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    + (2967493922437201920 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    + (3280392941469696000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (3854461706226892800 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (3679927979212800000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (7359855958425600000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (3154223982182400000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    - (2943942383370240000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    - (4205631976243200000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    + (519311436426510336 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (352389903289417728 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (204015207167557632 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (1160502087524548608 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (900846369311293440 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (434525895785447424 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (522339491449405440 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (435282909541171200 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (173734656938606592 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (1154025414281134080 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (1384830497137360896 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (1615635579993587712 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (1846440662849814528 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (741873480609300480 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (1285914033056120832 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (1500233038565474304 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (1714552044074827776 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (642957016528060416 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (1038622872853020672 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (1186997568974880768 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (2390481215296634880 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (4677335658698637312 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (5456891601815076864 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (6236447544931516416 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (1059819258013286400 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (4578419194617397248 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (5341489060386963456 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (6104558926156529664 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (2472911602031001600 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (3391421625642516480 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (1042996730108313600 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (2511266965654339584 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (3306636085001453568 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (3779012668573089792 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (1392905310531747840 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b6
    + (3721143172579983360 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (3714414161417994240 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (1588046634229432320 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    - (1298278591066275840 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (989164640812400640 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (618227900507750400 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (3395837539217571840 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (2870343823785984000 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    + (474710709318451200 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (804984245452800000 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    + (1609968490905600000 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    - (1703280950378496000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (1951045244178923520 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (2588356199778877440 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (3679927979212800000 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (591416996659200000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (2891371983667200000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (657129996288000000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    - (64913929553313792 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (431213960604155904 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (197060143286845440 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (95052539703066624 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (591180429860536320 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (380872545848524800 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (152017824821280768 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (210071317213347840 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (193322387867959296 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (144253176785141760 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (173103812142170112 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (201954447499198464 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (230805082856226816 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (886126657394442240 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (1755767237442011136 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (2048395110349012992 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (2341022983256014848 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (231835462690406400 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (1001529198822555648 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (1168450731959648256 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (1335372265096740864 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (540949412944281600 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (741873480609300480 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (1164329212622929920 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (2831483784325496832 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (3765007914092199936 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (4302866187533942784 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (1218792146715279360 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (3256000276007485440 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (3250112391240744960 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (1389540804950753280 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (195561886895308800 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (1110286841728204800 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (1660383504220815360 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (1877394114194964480 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (886126657394442240 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (1890852136518942720 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    + (162284823883284480 : R) * h ^ 56 * a7 ^ 9 * a0
    + (1267367196040888320 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (627887711453184000 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (107465396767948800 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (1931962189086720000 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (104049963612241920 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    - (574344759355637760 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    - (804984245452800000 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    - (42404598660464640 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (2443616746796482560 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (574988746752000000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (492847497216000000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (657129996288000000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    + (51728287612796928 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (217345746272256000 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (83315869404364800 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (33253899179655168 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (236596369513512960 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (169157089384464384 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (79332675931865088 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (39524397886734336 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (105935926701588480 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (213675018112991232 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (249287521131823104 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (284900024150654976 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (419879782428180480 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (1035531733350481920 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (1395649485396246528 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (1595027983309996032 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (266610782093967360 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (712250060376637440 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (710962085583912960 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (303962051082977280 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (259618918933463040 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (1230935909046681600 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (1860093195652694016 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (2124054429601628160 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (775360825220136960 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (1654495619454074880 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (195877309293527040 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (667686132548370432 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (803443932741500928 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (413581848543756288 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    - (152987255848304640 : R) * h ^ 48 * a7 ^ 10 * a1
    - (712411057225728000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (154828657309777920 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    + (2374703524085760 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (459770345470033920 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (477884647200522240 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    + (125778788352000000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (349862581323694080 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (566335987525877760 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (215620780032000000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    - (25673966278410240 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (86394934143221760 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (37003113302851584 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (88176947481280512 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (34583848150892544 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (27540810991927296 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (48178307090350080 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (121375524529373184 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (166849084555001856 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (190684668062859264 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (124551187377684480 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (439521398017228800 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (674158205881810944 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (780512724391034880 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (169610180516904960 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (361920916755578880 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (257640957644636160 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (736477786209779712 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (896004635498643456 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (361884117475786752 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (112026207507185664 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (298368560554573824 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    + (84523345772544000 : R) * h ^ 40 * a7 ^ 11 * a2
    + (228546976268943360 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (16524817213685760 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (23676547781099520 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    - (118207624029143040 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (175407504556032000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (23102226432000000 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (10103181174374400 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (31600519038369792 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (7565216783007744 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (30164346029998080 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (4268459764482048 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (25409830822871040 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (49657465641369600 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (77951655638728704 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (92130446892072960 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (122151328095928320 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (261020166509297664 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (322651485307404288 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (79162150697828352 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (146235737983942656 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (327815541383233536 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (47971803989016576 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (30102774986833920 : R) * h ^ 32 * a7 ^ 12 * a3
    - (56529973715927040 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (1656192195624960 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    + (16196768806993920 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (18351946633052160 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (3590945101578240 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (10579352714477568 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (5506282832265216 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (1852800164167680 : R) * h ^ 30 * a7 ^ 12 * b5
    - (24551390592368640 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (29142064809639936 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (36939720793522176 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (68651634917376000 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (115509776829382656 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (62222078664769536 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (8958584373903360 : R) * h ^ 24 * a7 ^ 13 * a4
    + (14325566676664320 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (1010946209218560 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (1161096422621184 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (2544580201218048 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (1759389760880640 : R) * h ^ 22 * a7 ^ 13 * b6
    + (13623281373413376 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (12775037085941760 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (28965174912221184 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (2578491569848320 : R) * h ^ 16 * a7 ^ 14 * a5
    - (4163860463616000 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (494464115367936 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (961416945893376 : R) * h ^ 14 * a7 ^ 14 * b7
    - (5684124252635136 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (1147594947932160 : R) * h ^ 8 * a7 ^ 15 * a6
    + (33996114512640 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (395668377796608 : R) * h ^ 6 * a7 ^ 15 * b8
    - (91797307983360 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `11` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock11Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (6890507429876858880 : R) * h ^ 104 * a6 ^ 2 * a3 * a0
    - (6890507429876858880 : R) * h ^ 104 * a6 ^ 2 * a2 * a1
    + (324259173170675712 : R) * h ^ 102 * a6 ^ 2 * a4 * b1
    + (648518346341351424 : R) * h ^ 102 * a6 ^ 2 * a3 * b2
    + (972777519512027136 : R) * h ^ 102 * a6 ^ 2 * a2 * b3
    + (1297036692682702848 : R) * h ^ 102 * a6 ^ 2 * a1 * b4
    + (1621295865853378560 : R) * h ^ 102 * a6 ^ 2 * a0 * b5
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a6 * a3 * a0
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a6 * a2 * a1
    + (3445253714938429440 : R) * h ^ 96 * a7 * a6 ^ 2 * a4 * a0
    + (3445253714938429440 : R) * h ^ 96 * a7 * a6 ^ 2 * a3 * a1
    + (1722626857469214720 : R) * h ^ 96 * a7 * a6 ^ 2 * a2 ^ 2
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 ^ 2 * a3 * a2 * lambda
    - (283726776524341248 : R) * h ^ 94 * a7 ^ 2 * a6 * a4 * b1
    - (567453553048682496 : R) * h ^ 94 * a7 ^ 2 * a6 * a3 * b2
    - (851180329573023744 : R) * h ^ 94 * a7 ^ 2 * a6 * a2 * b3
    - (1134907106097364992 : R) * h ^ 94 * a7 ^ 2 * a6 * a1 * b4
    - (1418633882621706240 : R) * h ^ 94 * a7 ^ 2 * a6 * a0 * b5
    - (202661983231672320 : R) * h ^ 94 * a7 * a6 ^ 2 * a5 * b1
    - (405323966463344640 : R) * h ^ 94 * a7 * a6 ^ 2 * a4 * b2
    - (607985949695016960 : R) * h ^ 94 * a7 * a6 ^ 2 * a3 * b3
    - (810647932926689280 : R) * h ^ 94 * a7 * a6 ^ 2 * a2 * b4
    - (1013309916158361600 : R) * h ^ 94 * a7 * a6 ^ 2 * a1 * b5
    - (1215971899390033920 : R) * h ^ 94 * a7 * a6 ^ 2 * a0 * b6
    - (2411677600456900608 : R) * h ^ 94 * a6 ^ 2 * a3 ^ 2 * b7
    - (5512405943901487104 : R) * h ^ 94 * a6 ^ 2 * a3 * a2 * b8
    - (1318886187749867520 : R) * h ^ 88 * a7 ^ 4 * a3 * a0
    - (1318886187749867520 : R) * h ^ 88 * a7 ^ 4 * a2 * a1
    - (3014597000571125760 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    - (3014597000571125760 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    - (1507298500285562880 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    - (1076641785918259200 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a5 * a0
    - (1076641785918259200 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    + (2799268643387473920 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    + (1356568650257006592 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (775182085861146624 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (920528726960111616 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a3 ^ 2 * lambda
    + (62065232364699648 : R) * h ^ 86 * a7 ^ 4 * a4 * b1
    + (124130464729399296 : R) * h ^ 86 * a7 ^ 4 * a3 * b2
    + (186195697094098944 : R) * h ^ 86 * a7 ^ 4 * a2 * b3
    + (248260929458798592 : R) * h ^ 86 * a7 ^ 4 * a1 * b4
    + (310326161823498240 : R) * h ^ 86 * a7 ^ 4 * a0 * b5
    + (177329235327713280 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (354658470655426560 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (531987705983139840 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (709316941310853120 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (886646176638566400 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6
    + (75998243711877120 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 3 * b1
    + (151996487423754240 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a5 * b2
    + (227994731135631360 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (303992974847508480 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a3 * b4
    + (379991218559385600 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a2 * b5
    + (455989462271262720 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a1 * b6
    + (531987705983139840 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a0 * b7
    + (2110217900399788032 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 ^ 2 * b7
    + (4823355200913801216 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 * a2 * b8
    + (2411677600456900608 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a3 * b7
    + (2756202971950743552 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a2 * b8
    + (4478829829419958272 : R) * h ^ 86 * a7 * a6 ^ 2 * a3 ^ 2 * b8
    + (659443093874933760 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    + (659443093874933760 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    + (329721546937466880 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    + (942061562678476800 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    + (942061562678476800 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    - (2449360062964039680 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    + (269160446479564800 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 3 * a0
    + (269160446479564800 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    - (1668794768173301760 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    - (2449360062964039680 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    - (296749392243720192 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (12468461858979840 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (678284325128503296 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (805462636090097664 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (242244401831608320 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (775182085861146624 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (38790770227937280 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (77581540455874560 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (116372310683811840 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (155163080911749120 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (193953851139686400 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (232744621367623680 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (83123079059865600 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (132996926495784960 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (199495389743677440 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (265993852991569920 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (332492316239462400 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (398990779487354880 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (465489242735247360 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (461610165712453632 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (44332308831928320 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 3 * b2
    - (66498463247892480 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (88664617663856640 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (110830772079820800 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (132996926495784960 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (155163080911749120 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (177329235327713280 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (2110217900399788032 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (2411677600456900608 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (3918976100742463488 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (753649250142781440 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * b7
    - (861313428734607360 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a2 * b8
    - (602919400114225152 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * b7
    - (3962041772179193856 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 * a3 * b8
    - (206075966835916800 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    - (206075966835916800 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (535797513773383680 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    - (232744621367623680 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    - (235515390669619200 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    + (1460195422151639040 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    + (2143190055093534720 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    - (58878847667404800 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    + (546732156911616000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    + (2161694835789004800 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    + (10909904126607360 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (148374696121860096 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (176194951644708864 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (2805403918270464 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (211963851602657280 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (678284325128503296 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (60561100457902080 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (227104126717132800 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (157458861190545408 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (29093077670952960 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (29093077670952960 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (43639616506429440 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (58186155341905920 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (72732694177382400 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (87279233012858880 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (101825771848335360 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (47380155064123392 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (58186155341905920 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (77581540455874560 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (96976925569843200 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (116372310683811840 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (135767695797780480 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (155163080911749120 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (461610165712453632 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (527554475099947008 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (857276022037413888 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (16624615811973120 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (22166154415964160 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (27707693019955200 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (33249231623946240 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (38790770227937280 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (44332308831928320 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (659443093874933760 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (753649250142781440 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (527554475099947008 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (3466786550656794624 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (188412312535695360 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (215328357183651840 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (376824625071390720 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (1184305964510085120 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (861313428734607360 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (49094568569733120 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    + (51518991708979200 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (319417748595671040 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (468822824551710720 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    + (49657381084200960 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (478390637297664000 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (1891482981315379200 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    - (139626981611274240 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    - (644302818760458240 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    - (458413885410508800 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    - (2386541527695360 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (2454728428486656 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (46367092538081280 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (148374696121860096 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (64173614630436864 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (198716110877491200 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (137776503541727232 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (54883497289973760 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (90841650686853120 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (3182055370260480 : R) * h ^ 62 * a7 ^ 8 * b1
    - (16001192719024128 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (12728221481041920 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (16970961974722560 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (21213702468403200 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (25456442962083840 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (29699183455764480 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (33941923949445120 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (17507798526984192 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (19395385113968640 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (24244231392460800 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (29093077670952960 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (33941923949445120 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (38790770227937280 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (144253176785141760 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (164860773468733440 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (115402541428113408 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (758359557956173824 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (4987384743591936 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (6234230929489920 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (7481077115387904 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (206560851463766016 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (236069544530018304 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (329721546937466880 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (1036267718946324480 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (753649250142781440 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (94206156267847680 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (289347479965532160 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (58878847667404800 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (511404848311173120 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    + (530342561710080 : R) * h ^ 56 * a7 ^ 9 * a0
    - (9640870139658240 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (104647951908864000 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (413761902162739200 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (149267465203875840 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (563764966415400960 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (401112149734195200 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (157080354312683520 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    + (269055305680158720 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    + (536971843731456 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (21376593398071296 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (43469149254451200 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (30138610149752832 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (57576879871229952 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (79486444350996480 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (21764145477058560 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (13011173926502400 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (1644061941301248 : R) * h ^ 54 * a7 ^ 9 * b2
    + (5773157600329728 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (4242740493680640 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (5303425617100800 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (6364110740520960 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (7424795863941120 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (8485480987361280 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (5198903292985344 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (5454952063303680 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (6545942475964416 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (72550862441938944 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (82915271362215936 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (72126588392570880 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (226683563519508480 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (164860773468733440 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (1298798110310400 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (1558557732372480 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (100734781435674624 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (305304142463631360 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (51518991708979200 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (447479242272276480 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (29439423833702400 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (124486706496798720 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (75701375572377600 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    - (356323908648960 : R) * h ^ 48 * a7 ^ 10 * a1
    - (50432601206292480 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (123323586403368960 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (87743282754355200 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (165058613084160000 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (235423392470138880 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (65055869632512000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    - (39230660778393600 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    - (2140429432651776 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (18864636677849088 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (17387659701780480 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (22791080210595840 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (11384777185689600 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (6209878464921600 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (566803612827648 : R) * h ^ 46 * a7 ^ 10 * b3
    - (1685190548127744 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (1193270763847680 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (1431924916617216 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (7981655553736704 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (9121892061413376 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (1343734205644800 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (1363738015825920 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (34047992461787136 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (100992376394219520 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (11269779436339200 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (97886084247060480 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (306145268858880 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (31268564505722880 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (130824841275113472 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (66238703625830400 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (3679927979212800 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (36799279792128000 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    + (5185933431275520 : R) * h ^ 40 * a7 ^ 11 * a2
    + (54227801745653760 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (51498867102842880 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (68204549080350720 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (34326828181094400 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (18906862111948800 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (1828660810088448 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (7444814773616640 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (2490420009369600 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (6498384504422400 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (739271245824000 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (159813048729600 : R) * h ^ 38 * a7 ^ 11 * b4
    + (429973202534400 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (298317690961920 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (3503575548297216 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (9977069442170880 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (314915055206400 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (10455324787998720 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (42989135119515648 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (14489716418150400 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (4574881052098560 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (38623781899468800 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (4468483974758400 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (5285358788935680 : R) * h ^ 32 * a7 ^ 12 * a3
    - (22322680304762880 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (7508993664614400 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (19806329178685440 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (2273772463718400 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (717285910118400 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (2120257791590400 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (899818809458688 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (39675808972800 : R) * h ^ 30 * a7 ^ 12 * b5
    - (99756319703040 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (1054470171525120 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (4191600318087168 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (2012610702606336 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (12664972718899200 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (5464712376483840 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (2159189431418880 : R) * h ^ 24 * a7 ^ 13 * a4
    + (6473863303004160 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (2772518389678080 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (203798052864000 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (384442833567744 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (9003356651520 : R) * h ^ 22 * a7 ^ 13 * b6
    + (366684011495424 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (1229672624947200 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (2350564566368256 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (624525065256960 : R) * h ^ 16 * a7 ^ 14 * a5
    - (1187595359354880 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (67321636945920 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (23480460509184 : R) * h ^ 14 * a7 ^ 14 * b7
    - (415571267026944 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (208738851471360 : R) * h ^ 8 * a7 ^ 15 * a6
    + (4135291066368 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (25807021277184 : R) * h ^ 6 * a7 ^ 15 * b8
    - (12878683453440 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `12` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock12Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (7177611906121728000 : R) * h ^ 96 * a6 * a5 ^ 3 * a2
    + (21532835718365184000 : R) * h ^ 96 * a6 * a5 ^ 2 * a4 * a3
    - (918734323983581184 : R) * h ^ 94 * a6 * a5 ^ 3 * b4
    - (3445253714938429440 : R) * h ^ 94 * a6 * a5 ^ 2 * a4 * b5
    - (4134304457926115328 : R) * h ^ 94 * a6 * a5 ^ 2 * a3 * b6
    - (4823355200913801216 : R) * h ^ 94 * a6 * a5 ^ 2 * a2 * b7
    - (3140205208928256000 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 3 * a2
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 2 * a4 * a3
    - (16149626788773888000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 ^ 2 * a2
    - (32299253577547776000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 * a4 * a3
    - (16149626788773888000 : R) * h ^ 88 * a7 * a6 * a5 ^ 3 * a3
    - (10766417859182592000 : R) * h ^ 88 * a7 * a6 * a5 ^ 2 * a4 ^ 2
    - (1480382455637606400 : R) * h ^ 88 * a6 * a5 ^ 5
    + (678284325128503296 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (1614962678877388800 : R) * h ^ 87 * a7 * a6 * a5 ^ 3 * a4 * lambda
    + (401946266742816768 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 3 * b4
    + (1507298500285562880 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a4 * b5
    + (1808758200342675456 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a3 * b6
    + (2110217900399788032 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a2 * b7
    + (2067152228963057664 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 ^ 2 * b4
    + (5167880572407644160 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a4 * b5
    + (6201456686889172992 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a3 * b6
    + (7235032801370701824 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a2 * b7
    + (2727492524326256640 : R) * h ^ 86 * a7 * a6 * a5 ^ 3 * b5
    + (4651092515166879744 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a4 * b6
    + (5426274601028026368 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a3 * b7
    + (4823355200913801216 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a2 * b8
    + (1256082083571302400 : R) * h ^ 86 * a6 * a5 ^ 4 * b7
    + (5742089524897382400 : R) * h ^ 86 * a6 * a5 ^ 3 * a4 * b8
    + (9514821783052615680 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    + (23551539066961920000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (7065461720088576000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 3 * a3
    + (4710307813392384000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 2 * a4 ^ 2
    + (12112220091580416000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a5 * a2
    + (12112220091580416000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a4 * a3
    + (31289901903249408000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a3
    + (16149626788773888000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 * a4 ^ 2
    + (6729011161989120000 : R) * h ^ 80 * a7 ^ 2 * a6 * a5 ^ 3 * a4
    + (647667324341452800 : R) * h ^ 80 * a7 ^ 2 * a5 ^ 5
    + (5551434208641024000 : R) * h ^ 80 * a7 * a6 ^ 2 * a5 ^ 4
    - (296749392243720192 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (1017426487692754944 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (423927703205314560 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (706546172008857600 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    - (3633666027474124800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (1185988217300582400 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 ^ 4 * lambda
    - (1507298500285562880 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (3768246250713907200 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (4521895500856688640 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (5275544750999470080 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (1193277979392737280 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 3 * b5
    - (2034852975385509888 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a4 * b6
    - (2373995137949761536 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a3 * b7
    - (2110217900399788032 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (1550364171722293248 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a5 * b4
    - (1937955214652866560 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a4 * b5
    - (2325546257583439872 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a3 * b6
    - (2713137300514013184 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a2 * b7
    - (5329376840295383040 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b5
    - (6976638772750319616 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b6
    - (8139411901542039552 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * b7
    - (7235032801370701824 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a2 * b8
    - (2476276107611996160 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 3 * b6
    - (3391421625642516480 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a4 * b7
    - (3617516400685350912 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a3 * b8
    - (549535911562444800 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 4 * b7
    - (2512164167142604800 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 3 * a4 * b8
    - (3768246250713907200 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 ^ 3 * b7
    - (12919701431019110400 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 ^ 2 * a4 * b8
    - (4844888036632166400 : R) * h ^ 78 * a7 * a6 * a5 ^ 4 * b8
    - (1071595027546767360 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    - (4121519336718336000 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    - (8973136384512491520 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (12364558010155008000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (20963813711979479040 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (11775769533480960000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (2943942383370240000 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    - (3028055022895104000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 4 * a2
    - (19682357648818176000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    - (6056110045790208000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    - (10934643138232320000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    - (3178756835377152000 : R) * h ^ 72 * a7 ^ 3 * a6 * a5 ^ 4
    - (8327151312961536000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 3 * a5 ^ 3
    + (741873480609300480 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (185468370152325120 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (381534932884783104 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (635891554807971840 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (2824418322605408256 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (518869845069004800 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (2725249520605593600 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (3179457774039859200 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (263777237549973504 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (659443093874933760 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (791331712649920512 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (923220331424907264 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (1582663425299841024 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (1978329281624801280 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (2373995137949761536 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (2769660994274721792 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (3827125098381312000 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (5087132438463774720 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (5934987844874403840 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (5275544750999470080 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (1083370797080248320 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (1483746961218600960 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (1582663425299841024 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (387591042930573312 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 4 * b4
    + (3391421625642516480 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (2616239539781369856 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (3052279463078264832 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (2713137300514013184 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (4643017701772492800 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b6
    + (5087132438463774720 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (5426274601028026368 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (4176472927874580480 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 3 * b7
    + (11154008902113165312 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 2 * a4 * b8
    + (2119638516026572800 : R) * h ^ 70 * a7 ^ 3 * a5 ^ 4 * b8
    + (4239277032053145600 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2 * b7
    + (9689776073264332800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 * a4 * b8
    + (13188861877498675200 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a5 ^ 3 * b8
    + (1648607734687334400 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    + (4121519336718336000 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (3182585712822190080 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    + (2060759668359168000 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (2702539107933880320 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (17314797127792066560 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (6182279005077504000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (7055157921746780160 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (328126911479808000 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    + (3974322217549824000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (5046758371491840000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (4920589412204544000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    + (6245363484721152000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 4 * a5 ^ 2
    - (129827859106627584 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (389483577319882752 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (463670925380812800 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (540176628068646912 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (238459333052989440 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (3044330818643165184 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (2347941247856934912 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (681312380151398400 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (3151069758200217600 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (527554475099947008 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (659443093874933760 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (791331712649920512 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (923220331424907264 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (654291194704035840 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (890248176731160576 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (1038622872853020672 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (923220331424907264 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (508713243846377472 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (3373757971342295040 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (2670744530193481728 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (3115868618559062016 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (2769660994274721792 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (3322533373871652864 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (3709367403046502400 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (3956658563249602560 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (1105941022019420160 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (2406967292643508224 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (696452655265873920 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (2785810621063495680 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (1907674664423915520 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (2034852975385509888 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (6941816139987025920 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (12491736321116602368 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (10146788081349427200 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    - (2119638516026572800 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a5 * b7
    - (2422444018316083200 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    - (13323442100738457600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    - (18031647098142720 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    - (450791177453568000 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (633683598020444160 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    - (4672128560608051200 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    - (2060759668359168000 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    - (993672552586936320 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    - (4174694296017960960 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (3774870121076490240 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    + (44005805418086400 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (473133597327360000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (3469646380400640000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    - (2342011306770432000 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    + (129827859106627584 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (81142411941642240 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (243427235824926720 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (1118606107481210880 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (418656206375092224 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (992586973833068544 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (3256377468625354752 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (1362624760302796800 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (57701270714056704 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (72126588392570880 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (86551906071085056 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (100977223749599232 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (247291160203100160 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (1089626674644910080 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (890248176731160576 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (1038622872853020672 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (923220331424907264 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (564905744088956928 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (649139295533137920 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (692415248568680448 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (880974758223544320 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (2749347791829467136 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (1947417886599413760 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (2077245745706041344 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (3310352812260458496 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (5193114364265103360 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (1914789191850393600 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (522339491449405440 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (4292267994953809920 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (4154491491412082688 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (14510692007631912960 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (397432221754982400 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (5904707294645452800 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    - (19534284356321280 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    + (378101100089180160 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    + (225395588726784000 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    + (1472396683357716480 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (713216041471180800 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (263766504426700800 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (104601952809123840 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    - (1291079731956940800 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (1240497150492672000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    + (351301696015564800 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 6
    - (14199922089787392 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (81142411941642240 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (134899259852980224 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (535105227322294272 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (1099570242536865792 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (1798008210733400064 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (215571495282278400 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (52892831487885312 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (114951750250659840 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (97370894329970688 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (113599376718299136 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (100977223749599232 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (410541965180928000 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (879042796034457600 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (649139295533137920 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (692415248568680448 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (474570412064243712 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (692415248568680448 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (650132876087525376 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (2836506886017122304 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (2540916671086854144 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (5179719426420768768 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (902502336901939200 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (8220223119965552640 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (965192538547814400 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    + (14462883609968640 : R) * h ^ 40 * a7 ^ 11 * a2
    - (187923572100956160 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    - (12115012894064640 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (225274841089966080 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (1076787175929937920 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (1136149014144614400 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (202486394231193600 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (8874951306117120 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (126446925275725824 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (121642301339467776 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (876763684389519360 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (343157883971567616 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (4207384322899968 : R) * h ^ 38 * a7 ^ 11 * b4
    + (83772027143454720 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (91623306817437696 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (70999610448936960 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (75732917812199424 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (297087485626810368 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (761179686096076800 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (662362503405109248 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (604398271170871296 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (731875576280776704 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (4221530579373391872 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (1612912433288970240 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    + (4375844046766080 : R) * h ^ 32 * a7 ^ 12 * a3
    - (111148199690895360 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (162231996792176640 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (1067489607894958080 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (248265766128844800 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (11056710168870912 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (187468818891669504 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (215685088929644544 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (6327511579361280 : R) * h ^ 30 * a7 ^ 12 * b5
    - (59222690937962496 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (71870670484537344 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (62584841803137024 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (275200970223255552 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (946943217138401280 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (1060357447480246272 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (14082822037831680 : R) * h ^ 24 * a7 ^ 13 * a4
    + (292713444409344000 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (287334095262842880 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (14843587178004480 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (66928127486459904 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (4351191404249088 : R) * h ^ 22 * a7 ^ 13 * b6
    + (48943712943734784 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (78296792633966592 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (342622425701154816 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (26787920876666880 : R) * h ^ 16 * a7 ^ 14 * a5
    - (111969220731863040 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (10254151095681024 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (3330931521748992 : R) * h ^ 14 * a7 ^ 14 * b7
    - (54404273261248512 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (19502872414126080 : R) * h ^ 8 * a7 ^ 15 * a6
    + (620462955184128 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (3395644708356096 : R) * h ^ 6 * a7 ^ 15 * b8
    - (1284714043146240 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `13` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock13Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (13781014859753717760 : R) * h ^ 104 * a6 * a5 * a4 * a0
    + (324259173170675712 : R) * h ^ 102 * a6 * a5 ^ 2 * b1
    + (1297036692682702848 : R) * h ^ 102 * a6 * a5 * a4 * b2
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a5 * a4 * a0
    + (10335761144815288320 : R) * h ^ 96 * a7 * a6 ^ 2 * a4 * a0
    + (8613134287346073600 : R) * h ^ 96 * a7 * a6 * a5 ^ 2 * a0
    + (1722626857469214720 : R) * h ^ 96 * a7 * a6 * a5 * a4 * a1
    + (7177611906121728000 : R) * h ^ 96 * a6 * a5 * a4 ^ 3
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 * a5 ^ 2 * a1 * lambda
    - (3100728343444586496 : R) * h ^ 95 * a7 * a6 * a5 * a4 * a2 * lambda
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 * a5 * a3 ^ 2 * lambda
    - (141863388262170624 : R) * h ^ 94 * a7 ^ 2 * a5 ^ 2 * b1
    - (567453553048682496 : R) * h ^ 94 * a7 ^ 2 * a5 * a4 * b2
    - (486388759756013568 : R) * h ^ 94 * a7 * a6 ^ 2 * a5 * b1
    - (972777519512027136 : R) * h ^ 94 * a7 * a6 ^ 2 * a4 * b2
    - (891712726219358208 : R) * h ^ 94 * a7 * a6 * a5 ^ 2 * b2
    - (486388759756013568 : R) * h ^ 94 * a7 * a6 * a5 * a4 * b3
    - (5512405943901487104 : R) * h ^ 94 * a6 * a5 ^ 2 * a1 * b8
    - (4134304457926115328 : R) * h ^ 94 * a6 * a5 * a4 ^ 2 * b6
    - (9646710401827602432 : R) * h ^ 94 * a6 * a5 * a4 * a3 * b7
    - (11024811887802974208 : R) * h ^ 94 * a6 * a5 * a4 * a2 * b8
    - (5512405943901487104 : R) * h ^ 94 * a6 * a5 * a3 ^ 2 * b8
    - (7536492501427814400 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    - (3768246250713907200 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    - (753649250142781440 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    - (9689776073264332800 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a5 * a0
    - (1291970143101911040 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    + (2799268643387473920 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 ^ 2 * a1
    + (7536492501427814400 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    + (3875910429305733120 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    - (3140205208928256000 : R) * h ^ 88 * a7 ^ 2 * a5 * a4 ^ 3
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 ^ 2 * a4 ^ 3
    - (13458022323978240000 : R) * h ^ 88 * a7 * a6 * a5 ^ 2 * a4 ^ 2
    + (678284325128503296 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (1356568650257006592 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (678284325128503296 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (2325546257583439872 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (2325546257583439872 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (1162773128791719936 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a3 ^ 2 * lambda
    + (2325546257583439872 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (4069705950771019776 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (354658470655426560 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (709316941310853120 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (390124317720969216 : R) * h ^ 86 * a7 ^ 3 * a5 ^ 2 * b2
    + (212795082393255936 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (182395784908505088 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 3 * b1
    + (1033576114481528832 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a5 * b2
    + (364791569817010176 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (319192623589883904 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 ^ 2 * b3
    + (121597189939003392 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a4 * b4
    + (2411677600456900608 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a1 * b8
    + (1808758200342675456 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 ^ 2 * b6
    + (4220435800799576064 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a3 * b7
    + (4823355200913801216 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a2 * b8
    + (2411677600456900608 : R) * h ^ 86 * a7 ^ 2 * a5 * a3 ^ 2 * b8
    + (8268608915852230656 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a1 * b8
    + (3100728343444586496 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 ^ 2 * b6
    + (7235032801370701824 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a3 * b7
    + (8268608915852230656 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a2 * b8
    + (4134304457926115328 : R) * h ^ 86 * a7 * a6 ^ 2 * a3 ^ 2 * b8
    + (5167880572407644160 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a4 * b6
    + (6029194001142251520 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a3 * b7
    + (8268608915852230656 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a2 * b8
    + (8440871601599152128 : R) * h ^ 86 * a7 * a6 * a5 * a4 ^ 2 * b7
    + (19293420803655204864 : R) * h ^ 86 * a7 * a6 * a5 * a4 * a3 * b8
    + (1318886187749867520 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    + (6829946329418956800 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    + (942061562678476800 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    - (1224680031482019840 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    - (3297215469374668800 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    - (1695710812821258240 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    + (2422444018316083200 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 3 * a0
    - (4602643634800558080 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    - (5652369376070860800 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    - (2906932821979299840 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    - (5679285420718817280 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    - (11277822707493765120 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (3925256511160320000 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    + (5887884766740480000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 2 * a4 ^ 2
    + (15140275114475520000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 * a4 ^ 2
    + (8411263952486400000 : R) * h ^ 80 * a7 ^ 2 * a6 * a5 ^ 3 * a4
    - (1695710812821258240 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (1695710812821258240 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (847855406410629120 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (1017426487692754944 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (1780496353462321152 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (872079846593789952 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (2761586180880334848 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (3052279463078264832 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (2131750736118153216 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (1526139731539132416 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (62065232364699648 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (124130464729399296 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (186195697094098944 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (731483095726817280 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (265993852991569920 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (139646772820574208 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (53198770598313984 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (273593677362757632 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 3 * b2
    - (364791569817010176 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (91197892454252544 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (78531518502273024 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (25332747903959040 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (6029194001142251520 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (2260947750428344320 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 ^ 2 * b6
    - (5275544750999470080 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (6029194001142251520 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (3014597000571125760 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (2260947750428344320 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a4 * b6
    - (2637772375499735040 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a3 * b7
    - (3617516400685350912 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (3692881325699629056 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 ^ 2 * b7
    - (8440871601599152128 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 * a3 * b8
    - (3100728343444586496 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a1 * b8
    - (5813865643958599680 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b6
    - (6782843251285032960 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * b7
    - (9818973087574523904 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a2 * b8
    - (6330653701199364096 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * b7
    - (14470065602741403648 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 * a3 * b8
    - (1614962678877388800 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 3 * b6
    - (9043791001713377280 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a4 * b7
    - (10594155173435670528 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a3 * b8
    - (9043791001713377280 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * a4 ^ 2 * b8
    - (1133417817597542400 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    - (164860773468733440 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    - (2296275059028787200 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    + (3385533740875776000 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    + (4121519336718336000 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    + (2119638516026572800 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    + (2484687371564482560 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    + (4934047434528522240 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    - (686919889453056000 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    + (1877394114194964480 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    + (6752562701056081920 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    + (8458367030620323840 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    + (6019100484399267840 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (6082605527240540160 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (3679927979212800000 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    - (3785068778618880000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    - (12616895928729600000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    - (1752346656768000000 : R) * h ^ 72 * a7 ^ 3 * a6 * a5 ^ 4
    + (296749392243720192 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (296749392243720192 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (148374696121860096 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (890248176731160576 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (1960665627324579840 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (2225620441827901440 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (932640947051692032 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (667686132548370432 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (763069865769566208 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (2364910972881076224 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (1144604798654349312 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (1344456430165426176 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (62065232364699648 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (122190926218002432 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (46548924273524736 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (262668929829175296 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (257681545085583360 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (66498463247892480 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (34357539344744448 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (11083077207982080 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (1055108950199894016 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (395665856324960256 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (923220331424907264 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (1055108950199894016 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (527554475099947008 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (94047826593447936 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (89297936361455616 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (18999560927969280 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (3165326850599682048 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (16228791625973760 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (4102717687883366400 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (4780962430593269760 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (6971255563820728320 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (4616101657124536320 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (10551089501998940160 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (706546172008857600 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (3956658563249602560 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (4634942888378105856 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (3956658563249602560 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (1453466410989649920 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (1695710812821258240 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (2713137300514013184 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (2422444018316083200 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b6
    + (9985852564391854080 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (11799993973664120832 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (6782843251285032960 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (2355153906696192000 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 3 * b7
    + (8548535780190978048 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 2 * a4 * b8
    + (695506388071219200 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (600196253409607680 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (721265883925708800 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (370936740304650240 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    - (1938586059449303040 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (4794946156914278400 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (6167559293160652800 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    - (2633356461924679680 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    - (236803365462343680 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    - (1869823976637726720 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    - (6688216531819560960 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (146040570375045120 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (4586346810892615680 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (766651662336000000 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    + (5914169966592000000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (3285649981440000000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    - (296749392243720192 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (329206357020377088 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (389483577319882752 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (739223932464267264 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (1667228170262151168 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (834607665685463040 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (588199688197373952 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (574573440594345984 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (1448924328455307264 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (276310020839178240 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (6788384789889024 : R) * h ^ 62 * a7 ^ 8 * b1
    - (80975732850819072 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (42912289564655616 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (11637231068381184 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (89772925384654848 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (63035001620398080 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (13853846509977600 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (1055108950199894016 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (7100096336363520 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (682128767535022080 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (793392472318279680 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (1170511491628007424 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (807817789996793856 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (1846440662849814528 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (22799473113563136 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (18405824648970240 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (1381327453091266560 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (1607392541320151040 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (2628351759872950272 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (1681075213543931904 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (7032143219232079872 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (8318403598450950144 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (4945823204062003200 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (1030379834179584000 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (3739984403833552896 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (1135520633585664000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (2402256984830115840 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (2890783195190525952 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (3414973164709478400 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (9296801821404168192 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (1924497192328888320 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    - (67618676618035200 : R) * h ^ 56 * a7 ^ 9 * a0
    + (654935182100398080 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (805306239150981120 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (1079322876303114240 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (1812180533363343360 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (4714999721565880320 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (1422982150461849600 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (408426006592880640 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    + (1630418376390082560 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (1028171877392056320 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (1368330839103897600 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (887125494988800000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (2217813737472000000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    + (32456964776656896 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (230676285376954368 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (276753583586672640 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (146056341494956032 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (543654160009003008 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (1019253618320080896 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (120885634117140480 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (330436504373428224 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (381629559604248576 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (8061206937993216 : R) * h ^ 54 * a7 ^ 9 * b2
    + (27456592051961856 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (10485630077239296 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (2424423139246080 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (115402541428113408 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (21715904404389888 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (12987981103104000 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (419901429063352320 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (486854471649853440 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (820182348006948864 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (271799480544657408 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (1165208066010906624 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (1380708977800642560 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (865519060710850560 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (4675673197117440 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (1063248085024505856 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (2265398298619674624 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (2736688839580975104 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (2360097998169440256 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (6542167302790447104 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (841967521643888640 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (170328095037849600 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (1523490183394099200 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (2164049989695700992 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (2711118597165416448 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    - (72690077364387840 : R) * h ^ 48 * a7 ^ 10 * a1
    - (565823426128773120 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (782645932641484800 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (333545222103367680 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (1543016801233797120 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (1518686067857817600 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (30249199652044800 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (2523379185745920 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (818657477850562560 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (646862340096000000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    - (23328443433222144 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (164240935599734784 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (168590285771636736 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (309380319830605824 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (262841064065335296 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (157772312198774784 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (2704747064721408 : R) * h ^ 46 * a7 ^ 10 * b3
    - (6621705699065856 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (2159251858391040 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (41025785309429760 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (47333073632624640 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (82945576651456512 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (4448383527813120 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (317570343575224320 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (681149257293496320 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (827395006846205952 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (378895666891456512 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (1082732221342679040 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (199584450185527296 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (1412217819956772864 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (2031571345493458944 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (1869691004450242560 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (215275786783948800 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (1157116553783672832 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    + (57264566760898560 : R) * h ^ 40 * a7 ^ 11 * a2
    + (466297186481602560 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (365969698958868480 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (528977365083095040 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (245982431155322880 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (233298295668080640 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (69306679296000000 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (15911519841681408 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (92067079749894144 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (41946682635583488 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (144605065066315776 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (20230896913219584 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (649669638094848 : R) * h ^ 38 * a7 ^ 11 * b4
    + (1354267612938240 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (30513460534050816 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (65556969909387264 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (80240829586735104 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (85047025229365248 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (415924113522032640 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (606905086815240192 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (299064770458288128 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (248408126577967104 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (1065489671405961216 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (154730457445957632 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (45193576442757120 : R) * h ^ 32 * a7 ^ 12 * a3
    - (207890594062663680 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (78593229324288000 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (158552132419584000 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (28955637543075840 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (8732850870288384 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (41904163327574016 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (22892074990829568 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (132585640427520 : R) * h ^ 30 * a7 ^ 12 * b5
    - (15703008205602816 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (39236907590221824 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (57883575969644544 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (103843056448438272 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (310844387342942208 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (176564664577032192 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (21992295133347840 : R) * h ^ 24 * a7 ^ 13 * a4
    + (80201051392573440 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (24169402497761280 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (3866648621875200 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (9332174179270656 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (1064582416171008 : R) * h ^ 22 * a7 ^ 13 * b6
    + (18741096804777984 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (28950248458027008 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (72768962860941312 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (8902313665781760 : R) * h ^ 16 * a7 ^ 14 * a5
    - (17378986471096320 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (1632969159671808 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (1237854951309312 : R) * h ^ 14 * a7 ^ 14 * b7
    - (12907651396534272 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (3682756423342080 : R) * h ^ 8 * a7 ^ 15 * a6
    + (103988996923392 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (835469994885120 : R) * h ^ 6 * a7 ^ 15 * b8
    - (258664208866560 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `14` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock14Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (13781014859753717760 : R) * h ^ 104 * a6 * a5 * a3 * a1
    - (6890507429876858880 : R) * h ^ 104 * a6 * a5 * a2 ^ 2
    - (6890507429876858880 : R) * h ^ 104 * a6 * a4 ^ 2 * a1
    + (1945555039024054272 : R) * h ^ 102 * a6 * a5 * a3 * b3
    + (2594073385365405696 : R) * h ^ 102 * a6 * a5 * a2 * b4
    + (3242591731706757120 : R) * h ^ 102 * a6 * a5 * a1 * b5
    + (3891110078048108544 : R) * h ^ 102 * a6 * a5 * a0 * b6
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a5 * a3 * a1
    + (3014597000571125760 : R) * h ^ 96 * a7 ^ 2 * a5 * a2 ^ 2
    + (3014597000571125760 : R) * h ^ 96 * a7 ^ 2 * a4 ^ 2 * a1
    + (10335761144815288320 : R) * h ^ 96 * a7 * a6 ^ 2 * a3 * a1
    + (5167880572407644160 : R) * h ^ 96 * a7 * a6 ^ 2 * a2 ^ 2
    + (15503641717222932480 : R) * h ^ 96 * a7 * a6 * a5 * a4 * a1
    + (8613134287346073600 : R) * h ^ 96 * a7 * a6 * a5 * a3 * a2
    + (1722626857469214720 : R) * h ^ 96 * a7 * a6 * a4 ^ 2 * a2
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 * a4 ^ 2 * a3 * lambda
    - (851180329573023744 : R) * h ^ 94 * a7 ^ 2 * a5 * a3 * b3
    - (1134907106097364992 : R) * h ^ 94 * a7 ^ 2 * a5 * a2 * b4
    - (1418633882621706240 : R) * h ^ 94 * a7 ^ 2 * a5 * a1 * b5
    - (1702360659146047488 : R) * h ^ 94 * a7 ^ 2 * a5 * a0 * b6
    - (1459166279268040704 : R) * h ^ 94 * a7 * a6 ^ 2 * a3 * b3
    - (1945555039024054272 : R) * h ^ 94 * a7 * a6 ^ 2 * a2 * b4
    - (2431943798780067840 : R) * h ^ 94 * a7 * a6 ^ 2 * a1 * b5
    - (2918332558536081408 : R) * h ^ 94 * a7 * a6 ^ 2 * a0 * b6
    - (972777519512027136 : R) * h ^ 94 * a7 * a6 * a5 * a4 * b3
    - (1945555039024054272 : R) * h ^ 94 * a7 * a6 * a5 * a3 * b4
    - (2431943798780067840 : R) * h ^ 94 * a7 * a6 * a5 * a2 * b5
    - (2918332558536081408 : R) * h ^ 94 * a7 * a6 * a5 * a1 * b6
    - (3404721318292094976 : R) * h ^ 94 * a7 * a6 * a5 * a0 * b7
    - (1607785066971267072 : R) * h ^ 94 * a6 * a4 ^ 3 * b7
    - (5512405943901487104 : R) * h ^ 94 * a6 * a4 ^ 2 * a3 * b8
    - (7536492501427814400 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    - (3768246250713907200 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    - (6782843251285032960 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    - (3768246250713907200 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    - (753649250142781440 : R) * h ^ 88 * a7 ^ 3 * a4 ^ 2 * a2
    - (8397805930162421760 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    - (6459850715509555200 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    - (4844888036632166400 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 ^ 2 * a1
    - (5167880572407644160 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    - (1614962678877388800 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    + (3552917893530255360 : R) * h ^ 88 * a7 ^ 2 * a6 * a4 ^ 2 * a3
    + (159596311794941952 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (678284325128503296 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (1937955214652866560 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (1001276860903981056 : R) * h ^ 87 * a7 ^ 2 * a6 * a4 ^ 3 * lambda
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (1418633882621706240 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (1773292353277132800 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (2127950823932559360 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6
    + (425590164786511872 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (851180329573023744 : R) * h ^ 86 * a7 ^ 3 * a5 * a3 * b4
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 3 * a5 * a2 * b5
    + (1276770494359535616 : R) * h ^ 86 * a7 ^ 3 * a5 * a1 * b6
    + (1489565576752791552 : R) * h ^ 86 * a7 ^ 3 * a5 * a0 * b7
    + (729583139634020352 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (1459166279268040704 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a3 * b4
    + (1823957849085050880 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a2 * b5
    + (2188749418902061056 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a1 * b6
    + (2553540988719071232 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a0 * b7
    + (303992974847508480 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 ^ 2 * b3
    + (729583139634020352 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a4 * b4
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a3 * b5
    + (1276770494359535616 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a2 * b6
    + (1489565576752791552 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a1 * b7
    + (1702360659146047488 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a0 * b8
    + (703405966799929344 : R) * h ^ 86 * a7 ^ 2 * a4 ^ 3 * b7
    + (2411677600456900608 : R) * h ^ 86 * a7 ^ 2 * a4 ^ 2 * a3 * b8
    + (3014597000571125760 : R) * h ^ 86 * a7 * a6 * a5 * a4 ^ 2 * b7
    + (6890507429876858880 : R) * h ^ 86 * a7 * a6 * a5 * a4 * a3 * b8
    + (4363988038922010624 : R) * h ^ 86 * a7 * a6 * a4 ^ 3 * b8
    + (1318886187749867520 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    + (659443093874933760 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    - (598486169231032320 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    + (5887884766740480000 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    + (4710307813392384000 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    + (2119638516026572800 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    + (2260947750428344320 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    + (706546172008857600 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    - (1554401578419486720 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    + (4171986920433254400 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    + (3068429089867038720 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (1211222009158041600 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    + (1480382455637606400 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    - (3526001848882298880 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    - (2637772375499735040 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    - (69823386410287104 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (119697233846206464 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (44886462692327424 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (847855406410629120 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (438058626645491712 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (726733205494824960 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (605611004579020800 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (1635149712363356160 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (186195697094098944 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (248260929458798592 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (310326161823498240 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (372391394188197888 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (531987705983139840 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (1063975411966279680 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (1329969264957849600 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (1595963117949419520 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (1861956970940989440 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (132996926495784960 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (319192623589883904 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (465489242735247360 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (558587091282296832 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (651684939829346304 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (744782788376395776 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (303992974847508480 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (547187354725515264 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (797981558974709760 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (957577870769651712 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (1117174182564593664 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (1276770494359535616 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (202661983231672320 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (329325722751467520 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (425590164786511872 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (496521858917597184 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (567453553048682496 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (1318886187749867520 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 ^ 2 * b7
    - (3014597000571125760 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 * a3 * b8
    - (1909244767028379648 : R) * h ^ 78 * a7 ^ 3 * a4 ^ 3 * b8
    - (1130473875214172160 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * b7
    - (2583940286203822080 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 * a3 * b8
    - (1884123125356953600 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a4 * b7
    - (2153283571836518400 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a3 * b8
    - (7321164144244162560 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * a4 ^ 2 * b8
    + (261837699038576640 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    - (968557044128808960 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    - (824303867343667200 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    + (448864626923274240 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    - (2657514106776453120 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (2178517363693977600 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    - (883182715011072000 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    - (647667324341452800 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    + (1542625808886005760 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    + (1154025414281134080 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    - (782247547581235200 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (1295334648682905600 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    + (979071124069416960 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    + (1169165689395609600 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    + (4251052801586626560 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    + (87279233012858880 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (19637827427893248 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (33664847019245568 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (11221615673081856 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (476918666105978880 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (264954814503321600 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (715377999158968320 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (454208253434265600 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (582900591907307520 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (870565819082342400 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (93097848547049472 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (186195697094098944 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (232744621367623680 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (279293545641148416 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (325842469914673152 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (212795082393255936 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (398990779487354880 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (581861553419059200 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (698233864102871040 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (814606174786682880 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (930978485470494720 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (88664617663856640 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (144080003703767040 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (186195697094098944 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (217228313276448768 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (248260929458798592 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (56998682783907840 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (199495389743677440 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (246994292063600640 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (319192623589883904 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (372391394188197888 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (425590164786511872 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (83123079059865600 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (114947343614214144 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (139646772820574208 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (159596311794941952 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (741873480609300480 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (1695710812821258240 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (824303867343667200 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (942061562678476800 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (3203009313106821120 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (1413092344017715200 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (1614962678877388800 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (2637772375499735040 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (392525651116032000 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 3 * b7
    + (4037406697193472000 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 2 * a4 * b8
    - (327297123798220800 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    + (364118050225520640 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    + (365784841133752320 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    + (154556975126937600 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    + (565323524147773440 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (839976031208079360 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (592468404653260800 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    - (511509989110579200 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    - (1859835600694149120 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (233412574681497600 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    - (830191752110407680 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    - (1477438513254236160 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    - (2315200402921881600 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    - (15273865777250304 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (24547284284866560 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (4909456856973312 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (69550638807121920 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (8416211754811392 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (300645786574651392 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (379878965294137344 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (380872545848524800 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (85164047518924800 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (615073676525568000 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (149825639153664000 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (34911693205143552 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (69823386410287104 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (101825771848335360 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (122190926218002432 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (142556080587669504 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (162921234957336576 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (51536309017116672 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (139646772820574208 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (180100004629708800 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (232744621367623680 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (271535391595560960 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (310326161823498240 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (36366347088691200 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (50289462831218688 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (61095463109001216 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (69823386410287104 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (108189882588856320 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (247291160203100160 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (35624176739942400 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (80748133943869440 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (86210507710660608 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (104735079615430656 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (119697233846206464 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (26836879810756608 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (961422313176170496 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (1099718335962021888 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (1721617505794916352 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (171729972363264000 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (1766365430022144000 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (264954814503321600 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (302805502289510400 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (441591357505536000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (2893474799655321600 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (728976209215488000 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    + (57276996664688640 : R) * h ^ 56 * a7 ^ 9 * a0
    - (98137049923584000 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    - (119554366054072320 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (71804594694389760 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (173670953983672320 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (545983028715847680 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (956807559795179520 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (1012900176278323200 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    + (160155722695311360 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    + (1633940593170186240 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    + (412020507672576000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    + (4295774749851648 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (6136821071216640 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (44594233117507584 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (54626230896427008 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (76447256772870144 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (400875660244942848 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (65548717129728000 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (108229310388633600 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (156725504114688000 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (14546538835476480 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (22910798665875456 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (31517500810199040 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (40730308739334144 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (47518693529223168 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (54307078319112192 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (32002385438048256 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (56528641563033600 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (62861828539023360 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (76369328886251520 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (87279233012858880 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (11741134917206016 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (150147555542433792 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (172012821729509376 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (248321540037279744 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (13804368486727680 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (25782997915533312 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (257395809501315072 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (294879122964873216 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (297258088170258432 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (1896072067971809280 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (318927091531776000 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (165596759064576000 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (517292733077913600 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (778041915604992000 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (234096521379840 : R) * h ^ 48 * a7 ^ 10 * a1
    + (32820865007616000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (79963685010800640 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (135812341982822400 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (147430400317194240 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (1064262326519070720 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (180258972106752000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    - (290425173159444480 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    - (434625779544883200 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    - (1073943687462912 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (21782518541844480 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (57654155459690496 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (93867792301817856 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (101924500798439424 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (54336436568064000 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (1272822148104192 : R) * h ^ 46 * a7 ^ 10 * b3
    - (8940060325969920 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (9275583171133440 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (11000819994329088 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (13364632555094016 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (15273865777250304 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (12329304918589440 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (18052134092144640 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (82030262212362240 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (94268390343966720 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (45527067801944064 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (275702368866140160 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (4241503543099392 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (152001589844901888 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (454968978041733120 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (508780348415410176 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (20699594883072000 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (275994598440960000 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (663446114795520 : R) * h ^ 40 * a7 ^ 11 * a2
    + (43823306385653760 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (152868326190612480 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (252675349995847680 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (282979346719703040 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (152696475824947200 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (2029026419933184 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (25377979194408960 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (14593728077365248 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (46869818728513536 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (6237601136640000 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (768996714479616 : R) * h ^ 38 * a7 ^ 11 * b4
    + (3412050868961280 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (2962781720543232 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (8808451320840192 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (10157717377253376 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (3768891784298496 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (44595323904983040 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (125792993956331520 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (73669317022973952 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (23770136259330048 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (240501693081452544 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (32527934816256000 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (4365074238013440 : R) * h ^ 32 * a7 ^ 12 * a3
    - (68694650734510080 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (40613373573857280 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (132142486876323840 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (17807196133785600 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (2199131595472896 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (12562234305675264 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (6692128608485376 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (288847288074240 : R) * h ^ 30 * a7 ^ 12 * b5
    - (1034244096786432 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (4283511317987328 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (11268743611023360 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (9914088092073984 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (65459788355469312 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (35332686436368384 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (6010540554977280 : R) * h ^ 24 * a7 ^ 13 * a4
    + (35596366373191680 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (19192603811512320 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (1074947201040384 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (2572389150621696 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (86276850057216 : R) * h ^ 22 * a7 ^ 13 * b6
    + (1788937602859008 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (5716982573826048 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (13796111932194816 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (3067351083417600 : R) * h ^ 16 * a7 ^ 14 * a5
    - (7421434014597120 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (425834763411456 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (117200903307264 : R) * h ^ 14 * a7 ^ 14 * b7
    - (2324605416505344 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (1237133280337920 : R) * h ^ 8 * a7 ^ 15 * a6
    + (25808812033536 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (143415376183296 : R) * h ^ 6 * a7 ^ 15 * b8
    - (75539381944320 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `15` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock15Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (13781014859753717760 : R) * h ^ 104 * a6 * a4 * a3 * a2
    - (2296835809958952960 : R) * h ^ 104 * a6 * a3 ^ 3
    + (972777519512027136 : R) * h ^ 102 * a6 * a4 ^ 2 * b3
    + (2594073385365405696 : R) * h ^ 102 * a6 * a4 * a3 * b4
    + (3242591731706757120 : R) * h ^ 102 * a6 * a4 * a2 * b5
    + (3891110078048108544 : R) * h ^ 102 * a6 * a4 * a1 * b6
    + (4539628424389459968 : R) * h ^ 102 * a6 * a4 * a0 * b7
    + (1621295865853378560 : R) * h ^ 102 * a6 * a3 ^ 2 * b5
    + (3891110078048108544 : R) * h ^ 102 * a6 * a3 * a2 * b6
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a4 * a3 * a2
    + (1004865666857041920 : R) * h ^ 96 * a7 ^ 2 * a3 ^ 3
    + (8613134287346073600 : R) * h ^ 96 * a7 * a6 * a5 * a3 * a2
    + (6890507429876858880 : R) * h ^ 96 * a7 * a6 * a4 ^ 2 * a2
    + (8613134287346073600 : R) * h ^ 96 * a7 * a6 * a4 * a3 ^ 2
    - (638385247179767808 : R) * h ^ 95 * a7 ^ 2 * a6 * a4 * a0 * lambda
    - (425590164786511872 : R) * h ^ 94 * a7 ^ 2 * a4 ^ 2 * b3
    - (1134907106097364992 : R) * h ^ 94 * a7 ^ 2 * a4 * a3 * b4
    - (1418633882621706240 : R) * h ^ 94 * a7 ^ 2 * a4 * a2 * b5
    - (1702360659146047488 : R) * h ^ 94 * a7 ^ 2 * a4 * a1 * b6
    - (1986087435670388736 : R) * h ^ 94 * a7 ^ 2 * a4 * a0 * b7
    - (709316941310853120 : R) * h ^ 94 * a7 ^ 2 * a3 ^ 2 * b5
    - (1702360659146047488 : R) * h ^ 94 * a7 ^ 2 * a3 * a2 * b6
    - (1215971899390033920 : R) * h ^ 94 * a7 * a6 * a5 * a4 * b3
    - (1621295865853378560 : R) * h ^ 94 * a7 * a6 * a5 * a3 * b4
    - (2026619832316723200 : R) * h ^ 94 * a7 * a6 * a5 * a2 * b5
    - (2431943798780067840 : R) * h ^ 94 * a7 * a6 * a5 * a1 * b6
    - (2837267765243412480 : R) * h ^ 94 * a7 * a6 * a5 * a0 * b7
    - (1783425452438716416 : R) * h ^ 94 * a7 * a6 * a4 ^ 2 * b4
    - (4458563631096791040 : R) * h ^ 94 * a7 * a6 * a4 * a3 * b5
    - (5350276357316149248 : R) * h ^ 94 * a7 * a6 * a4 * a2 * b6
    - (3972174871340777472 : R) * h ^ 94 * a7 * a6 * a4 * a1 * b7
    - (4539628424389459968 : R) * h ^ 94 * a7 * a6 * a4 * a0 * b8
    - (2675138178658074624 : R) * h ^ 94 * a7 * a6 * a3 ^ 2 * b6
    - (3404721318292094976 : R) * h ^ 94 * a7 * a6 * a3 * a2 * b7
    + (2127950823932559360 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    - (3768246250713907200 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    - (3014597000571125760 : R) * h ^ 88 * a7 ^ 3 * a4 ^ 2 * a2
    - (3768246250713907200 : R) * h ^ 88 * a7 ^ 3 * a4 * a3 ^ 2
    - (3229925357754777600 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    - (6459850715509555200 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    - (4306567143673036800 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    - (5598537286774947840 : R) * h ^ 88 * a7 ^ 2 * a6 * a4 ^ 2 * a3
    + (279293545641148416 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (398990779487354880 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (239394467692412928 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (159596311794941952 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (531987705983139840 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (709316941310853120 : R) * h ^ 86 * a7 ^ 3 * a5 * a3 * b4
    + (886646176638566400 : R) * h ^ 86 * a7 ^ 3 * a5 * a2 * b5
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 3 * a5 * a1 * b6
    + (1241304647293992960 : R) * h ^ 86 * a7 ^ 3 * a5 * a0 * b7
    + (780248635441938432 : R) * h ^ 86 * a7 ^ 3 * a4 ^ 2 * b4
    + (1950621588604846080 : R) * h ^ 86 * a7 ^ 3 * a4 * a3 * b5
    + (2340745906325815296 : R) * h ^ 86 * a7 ^ 3 * a4 * a2 * b6
    + (1737826506211590144 : R) * h ^ 86 * a7 ^ 3 * a4 * a1 * b7
    + (1986087435670388736 : R) * h ^ 86 * a7 ^ 3 * a4 * a0 * b8
    + (1170372953162907648 : R) * h ^ 86 * a7 ^ 3 * a3 ^ 2 * b6
    + (1489565576752791552 : R) * h ^ 86 * a7 ^ 3 * a3 * a2 * b7
    + (455989462271262720 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (607985949695016960 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a3 * b4
    + (759982437118771200 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a2 * b5
    + (911978924542525440 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a1 * b6
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a0 * b7
    + (379991218559385600 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 ^ 2 * b3
    + (1823957849085050880 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a4 * b4
    + (2279947311356313600 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a3 * b5
    + (2735936773627576320 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a2 * b6
    + (2482609294587985920 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a1 * b7
    + (2837267765243412480 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a0 * b8
    + (1671961361661296640 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 ^ 2 * b5
    + (4012707267987111936 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a3 * b6
    + (3688448094816436224 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a2 * b7
    + (2269814212194729984 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a1 * b8
    + (1808758200342675456 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 ^ 2 * b7
    + (1702360659146047488 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 * a2 * b8
    - (930978485470494720 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    - (1329969264957849600 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    - (864480022222602240 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    + (1521152346795540480 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    + (2826184688035430400 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    + (1884123125356953600 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    + (2449360062964039680 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    + (2153283571836518400 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (1480382455637606400 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    + (1345802232397824000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    + (4575727590152601600 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (933089547795824640 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    - (174558466025717760 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (104735079615430656 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (69823386410287104 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (149621542307758080 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (149621542307758080 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (154608927051350016 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (72317078782083072 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (299243084615516160 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (398990779487354880 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (498738474359193600 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (598486169231032320 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (698233864102871040 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (166246158119731200 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (797981558974709760 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (997476948718387200 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (1196972338462064640 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (1086141566382243840 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (1241304647293992960 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (731483095726817280 : R) * h ^ 78 * a7 ^ 4 * a4 ^ 2 * b5
    - (1755559429744361472 : R) * h ^ 78 * a7 ^ 4 * a4 * a3 * b6
    - (1613696041482190848 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (993043717835194368 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (791331712649920512 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (744782788376395776 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (284993413919539200 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (633318697598976000 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (791648371998720000 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (949978046398464000 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (930978485470494720 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (1063975411966279680 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (443323088319283200 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (1456633004477644800 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (1747959605373173760 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (1773292353277132800 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (1418633882621706240 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (1086774885079842816 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 ^ 2 * b6
    - (2234348365129187328 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (1702360659146047488 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (815714482507481088 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    + (581861553419059200 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (378210009722388480 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    - (47276251215298560 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    + (498738474359193600 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    + (540300013889126400 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (807679251531694080 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    - (685419056081141760 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    - (588788476674048000 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    - (2001880820691763200 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    - (408226677160673280 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    - (841126395248640000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (1429914871922688000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (841126395248640000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (1009351674298368000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    + (98189137139466240 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (65459424759644160 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (67641405584965632 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (31638721967161344 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (56108078365409280 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (71693655689134080 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (77927886618624000 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (43639616506429440 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (58186155341905920 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (72732694177382400 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (87279233012858880 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (101825771848335360 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (187026927884697600 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (411182164416135168 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (513977705520168960 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (616773246624202752 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (610954631090012160 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (698233864102871040 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (193953851139686400 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (637276939458969600 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (764732327350763520 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (775815404558745600 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (620652323646996480 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (475464012222431232 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (977527409744019456 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (744782788376395776 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (356875086097022976 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (53436265109913600 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (300826381359513600 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (471030781339238400 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (565236937607086080 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (598486169231032320 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (531987705983139840 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (296868139499520000 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (831230790598656000 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (897729253846548480 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (797981558974709760 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (517025551752364032 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (922112023704109056 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    - (327297123798220800 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (236381256076492800 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (58792261126717440 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    + (16516382636113920 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    - (202612505208422400 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (267119478020505600 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    + (615890063909191680 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (367992797921280000 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    + (441591357505536000 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (126168959287296000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (494161757208576000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (294394238337024000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (336450558099456000 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    - (14319249166172160 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (36820926427299840 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (31365974363996160 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (34093450395648000 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (23768005418680320 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (29222957481984000 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (15663505210343424 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (27274760316518400 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (58671039969755136 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (73338799962193920 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (88006559954632704 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (89097550367293440 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (101825771848335360 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (46756731971174400 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (194646543465185280 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (302706546243010560 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (363247855491612672 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (386937933023674368 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (349116932051435520 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (129879811031040000 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (363663470886912000 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (392756548557864960 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (349116932051435520 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (226198678891659264 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (403424010370547712 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (50467583714918400 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (185542587187200000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (251862929551392768 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (278462314850549760 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (265993852991569920 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (148434069749760000 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (364494701677510656 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (354658470655426560 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (195616312720883712 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    + (47730830553907200 : R) * h ^ 56 * a7 ^ 9 * a0
    + (132964456543027200 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (44132077456588800 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (4242740493680640 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (15260877796147200 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    - (200447841691238400 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    - (125606146772828160 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    - (147197119168512000 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    - (69655779606528000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (186624918945792000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (35046933135360000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    + (5369718437314560 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (15325005952843776 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (12785043898368000 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (6852783529525248 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (8718182315458560 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (10150107232075776 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (12785043898368000 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (27577813208924160 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (42275878490603520 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (50731054188724224 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (54731352368480256 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (50912885924167680 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (43120097262305280 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (118623560741683200 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (160308795329740800 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (177831437263699968 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (171649158258622464 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (64939905515520000 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (159466431983910912 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (155163080911749120 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (85582136815386624 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (28449863368704000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (86537062664110080 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (105497041173479424 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (107367310452326400 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (59614833263247360 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (131057387984388096 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    - (19390649912524800 : R) * h ^ 48 * a7 ^ 10 * a1
    - (31223918320680960 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (6889718100787200 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (1396207968583680 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    + (23489981448192000 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (77540179920814080 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    + (15333033246720000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (24970939858944000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (27928024842240000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    - (2155345317199872 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (5533793167343616 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (4440671914033152 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (2789574816301056 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (1503764687093760 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (1118691341107200 : R) * h ^ 46 * a7 ^ 10 * b3
    - (11392894673879040 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (16383796995686400 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (21926959097315328 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (24501826351005696 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (24183620813979648 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (23824827836006400 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (54751298196602880 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (66675695073361920 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (68308121948258304 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (26081489552670720 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (57337607243169792 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (12320027789230080 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (33011118637056000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (36781962483990528 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (20217957250498560 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    + (6016073434398720 : R) * h ^ 40 * a7 ^ 11 * a2
    + (7182708690124800 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (1797347176611840 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    - (9302689783480320 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    - (11489386482892800 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (7187359334400000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (752319926894592 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (1748545006731264 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (657897050603520 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (781561909739520 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (957102591836160 : R) * h ^ 38 * a7 ^ 11 * b4
    + (6110185563095040 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (7389958310461440 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (8977823557484544 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (9334029086097408 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (10141351941242880 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (20719043031859200 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (23133488425205760 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (8845356297093120 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (4442295411671040 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (10790847633162240 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    - (1805573003673600 : R) * h ^ 32 * a7 ^ 12 * a3
    - (1926465973125120 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (318991918694400 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    + (2674044960768000 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (598946611200000 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (231046385762304 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (485551044034560 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (97790365532160 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (495383457300480 : R) * h ^ 30 * a7 ^ 12 * b5
    - (2533861254758400 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (2746046899814400 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (3080603679326208 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (3607399067811840 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (6732949110128640 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (1392825681838080 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (532349473259520 : R) * h ^ 24 * a7 ^ 13 * a4
    + (539263343001600 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    - (194835067699200 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (62832747479040 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (77974260940800 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (199128168529920 : R) * h ^ 22 * a7 ^ 13 * b6
    + (882467678453760 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (880229555896320 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (1119388937748480 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (145885475635200 : R) * h ^ 16 * a7 ^ 14 * a5
    - (112857396019200 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (18523903426560 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (67599740436480 : R) * h ^ 14 * a7 ^ 14 * b7
    - (269351575879680 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (45712680222720 : R) * h ^ 8 * a7 ^ 15 * a6
    + (1368434995200 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (20218824622080 : R) * h ^ 6 * a7 ^ 15 * b8
    - (4025371607040 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `16` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock16Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6485183463413514240 : R) * h ^ 112 * a6 * a1 * a0
    - (576460752303423488 : R) * h ^ 110 * a6 * a2 * b1
    - (1152921504606846976 : R) * h ^ 110 * a6 * a1 * b2
    - (1729382256910270464 : R) * h ^ 110 * a6 * a0 * b3
    - (2837267765243412480 : R) * h ^ 104 * a7 ^ 2 * a1 * a0
    - (1621295865853378560 : R) * h ^ 104 * a7 * a6 * a2 * a0
    - (810647932926689280 : R) * h ^ 104 * a7 * a6 * a1 ^ 2
    + (1459166279268040704 : R) * h ^ 103 * a7 * a6 * a3 * a0 * lambda
    + (1459166279268040704 : R) * h ^ 103 * a7 * a6 * a2 * a1 * lambda
    + (252201579132747776 : R) * h ^ 102 * a7 ^ 2 * a2 * b1
    + (504403158265495552 : R) * h ^ 102 * a7 ^ 2 * a1 * b2
    + (756604737398243328 : R) * h ^ 102 * a7 ^ 2 * a0 * b3
    + (216172782113783808 : R) * h ^ 102 * a7 * a6 * a3 * b1
    + (432345564227567616 : R) * h ^ 102 * a7 * a6 * a2 * b2
    + (648518346341351424 : R) * h ^ 102 * a7 * a6 * a1 * b3
    + (864691128455135232 : R) * h ^ 102 * a7 * a6 * a0 * b4
    + (4539628424389459968 : R) * h ^ 102 * a6 * a3 * a1 * b7
    + (5188146770730811392 : R) * h ^ 102 * a6 * a3 * a0 * b8
    + (2269814212194729984 : R) * h ^ 102 * a6 * a2 ^ 2 * b7
    + (5188146770730811392 : R) * h ^ 102 * a6 * a2 * a1 * b8
    + (709316941310853120 : R) * h ^ 96 * a7 ^ 3 * a2 * a0
    + (354658470655426560 : R) * h ^ 96 * a7 ^ 3 * a1 ^ 2
    - (3343922723322593280 : R) * h ^ 96 * a7 ^ 2 * a6 * a3 * a0
    - (3343922723322593280 : R) * h ^ 96 * a7 ^ 2 * a6 * a2 * a1
    - (638385247179767808 : R) * h ^ 95 * a7 ^ 3 * a3 * a0 * lambda
    - (638385247179767808 : R) * h ^ 95 * a7 ^ 3 * a2 * a1 * lambda
    - (729583139634020352 : R) * h ^ 95 * a7 ^ 2 * a6 * a4 * a0 * lambda
    - (1367968386813788160 : R) * h ^ 95 * a7 ^ 2 * a6 * a3 * a1 * lambda
    - (683984193406894080 : R) * h ^ 95 * a7 ^ 2 * a6 * a2 ^ 2 * lambda
    - (94575592174780416 : R) * h ^ 94 * a7 ^ 3 * a3 * b1
    - (189151184349560832 : R) * h ^ 94 * a7 ^ 3 * a2 * b2
    - (283726776524341248 : R) * h ^ 94 * a7 ^ 3 * a1 * b3
    - (378302368699121664 : R) * h ^ 94 * a7 ^ 3 * a0 * b4
    - (54043195528445952 : R) * h ^ 94 * a7 ^ 2 * a6 * a4 * b1
    - (108086391056891904 : R) * h ^ 94 * a7 ^ 2 * a6 * a3 * b2
    - (162129586585337856 : R) * h ^ 94 * a7 ^ 2 * a6 * a2 * b3
    - (216172782113783808 : R) * h ^ 94 * a7 ^ 2 * a6 * a1 * b4
    - (270215977642229760 : R) * h ^ 94 * a7 ^ 2 * a6 * a0 * b5
    - (1986087435670388736 : R) * h ^ 94 * a7 ^ 2 * a3 * a1 * b7
    - (2269814212194729984 : R) * h ^ 94 * a7 ^ 2 * a3 * a0 * b8
    - (993043717835194368 : R) * h ^ 94 * a7 ^ 2 * a2 ^ 2 * b7
    - (2269814212194729984 : R) * h ^ 94 * a7 ^ 2 * a2 * a1 * b8
    - (2269814212194729984 : R) * h ^ 94 * a7 * a6 * a4 * a1 * b7
    - (2594073385365405696 : R) * h ^ 94 * a7 * a6 * a4 * a0 * b8
    - (2837267765243412480 : R) * h ^ 94 * a7 * a6 * a3 * a2 * b7
    - (7133701809754865664 : R) * h ^ 94 * a7 * a6 * a3 * a1 * b8
    - (3566850904877432832 : R) * h ^ 94 * a7 * a6 * a2 ^ 2 * b8
    + (1462966191453634560 : R) * h ^ 88 * a7 ^ 4 * a3 * a0
    + (1462966191453634560 : R) * h ^ 88 * a7 ^ 4 * a2 * a1
    + (1773292353277132800 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    + (3901243177209692160 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    + (1950621588604846080 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    + (319192623589883904 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (598486169231032320 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (299243084615516160 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (227994731135631360 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (547187354725515264 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (626985510622986240 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (80748133943869440 : R) * h ^ 87 * a7 * a5 ^ 5 * lambda
    + (23643898043695104 : R) * h ^ 86 * a7 ^ 4 * a4 * b1
    + (47287796087390208 : R) * h ^ 86 * a7 ^ 4 * a3 * b2
    + (70931694131085312 : R) * h ^ 86 * a7 ^ 4 * a2 * b3
    + (94575592174780416 : R) * h ^ 86 * a7 ^ 4 * a1 * b4
    + (118219490218475520 : R) * h ^ 86 * a7 ^ 4 * a0 * b5
    + (11258999068426240 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (22517998136852480 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (33776997205278720 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (45035996273704960 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (56294995342131200 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (67553994410557440 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6
    + (993043717835194368 : R) * h ^ 86 * a7 ^ 3 * a4 * a1 * b7
    + (1134907106097364992 : R) * h ^ 86 * a7 ^ 3 * a4 * a0 * b8
    + (1241304647293992960 : R) * h ^ 86 * a7 ^ 3 * a3 * a2 * b7
    + (3120994541767753728 : R) * h ^ 86 * a7 ^ 3 * a3 * a1 * b8
    + (1560497270883876864 : R) * h ^ 86 * a7 ^ 3 * a2 ^ 2 * b8
    + (709316941310853120 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a1 * b7
    + (810647932926689280 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a0 * b8
    + (993043717835194368 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a2 * b7
    + (3080462145121419264 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a1 * b8
    + (531987705983139840 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 ^ 2 * b7
    + (3647915698170101760 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 * a2 * b8
    + (287104476244869120 : R) * h ^ 86 * a5 ^ 5 * b8
    - (775815404558745600 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    - (1706793890029240320 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    - (853396945014620160 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    - (562070344119091200 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    - (1626045756085370880 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    - (1892039609076940800 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    - (201870334859673600 : R) * h ^ 80 * a7 ^ 2 * a5 ^ 5
    - (99747694871838720 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (239394467692412928 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (274306160897556480 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (56998682783907840 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (156746377655746560 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (196645455604482048 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (103310112545832960 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (302805502289510400 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 ^ 4 * lambda
    - (4925812092436480 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (9851624184872960 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (14777436277309440 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (19703248369745920 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (24629060462182400 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (29554872554618880 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (2111062325329920 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (4222124650659840 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (6333186975989760 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (8444249301319680 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (10555311626649600 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (12666373951979520 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (14777436277309440 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (310326161823498240 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (354658470655426560 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (434456626552897536 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (1347702188490620928 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (232744621367623680 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (1595963117949419520 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (177329235327713280 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (202661983231672320 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (265993852991569920 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (911978924542525440 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (301459700057112576 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (1195705701066866688 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (633318697598976000 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (1076641785918259200 : R) * h ^ 78 * a7 * a6 * a5 ^ 4 * b8
    + (245905775552102400 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (711395018287349760 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (827767328971161600 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    + (141309234401771520 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    + (473801550641233920 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    + (606798477137018880 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    + (320023854380482560 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    + (757013755723776000 : R) * h ^ 72 * a7 ^ 3 * a6 * a5 ^ 4
    + (35050231670243328 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (68576540224389120 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (86032386826960896 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (45198174238801920 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (37405385576939520 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (49873847435919360 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (54861232179511296 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (88318271501107200 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (454208253434265600 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (1231453023109120 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (1847179534663680 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (2770769301995520 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (3694359069327360 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (4617948836659200 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (5541538603991040 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (6465128371322880 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (738871813865472 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (1108307720798208 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (1477743627730944 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (1847179534663680 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (2216615441596416 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (111200207986753536 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (127085951984861184 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (116372310683811840 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (398990779487354880 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (131888618774986752 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (523121244216754176 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (277076930199552000 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (60956924643901440 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (221661544159641600 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (72040001851883520 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (310326161823498240 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (37682462507139072 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (345792008889040896 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (314020520892825600 : R) * h ^ 70 * a7 ^ 3 * a5 ^ 4 * b8
    + (1614962678877388800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a5 ^ 3 * b8
    - (87205015977984000 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (207288178405539840 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (265474333747445760 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (140010436291461120 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    - (114121060625940480 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (155682600155873280 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (172307215967846400 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    - (220795678752768000 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    - (1135520633585664000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    - (4424572229124096 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (22777208003100672 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (21819808253214720 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (24001789078536192 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (11065759899844608 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (12624317632217088 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (6545942475964416 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (264954814503321600 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (340656190075699200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (134690174402560 : R) * h ^ 62 * a7 ^ 8 * b1
    - (426610511577088 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (484884627849216 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (646512837132288 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (808141046415360 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (969769255698432 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (14708167044759552 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (16809333765439488 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (184717953466368 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (246290604621824 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (307863255777280 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (369435906932736 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (37282240274628608 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (135706123146625024 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (31517500810199040 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (135767695797780480 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (16486077346873344 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (151284003888955392 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (15377769626075136 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (69823386410287104 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (16624615811973120 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (80906463618269184 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (42115693390331904 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (942061562678476800 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    - (1211222009158041600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    + (11104723843153920 : R) * h ^ 56 * a7 ^ 9 * a0
    + (69614419071467520 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (68111137568194560 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (75384406985932800 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (34783050344693760 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (39978242785935360 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (20768400259153920 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (662387036258304000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    + (851640475189248000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    + (2805403918270464 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (6660746951786496 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (5523138964094976 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (2863849833234432 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (2630066173378560 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (2805403918270464 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (38639243781734400 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (298074166316236800 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (127746071278387200 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (45217415692288 : R) * h ^ 54 * a7 ^ 9 * b2
    + (105862353911808 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (107752139522048 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (134690174402560 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (161628209283072 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (4643443762528256 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (16944023939842048 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (39582418599936 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (49478023249920 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (59373627899904 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (9264759853547520 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (42175067018231808 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (7273269417738240 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (35396577832992768 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (18425615858270208 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (3359557778669568 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (17040231207272448 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (1731730813747200 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (18287077393170432 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (137383977890611200 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (1059819258013286400 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (454208253434265600 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    - (8612824083333120 : R) * h ^ 48 * a7 ^ 10 * a1
    - (20962887115735040 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (17490481218846720 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (9086175113379840 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (8373768887992320 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (8958228037632000 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (96598109454336000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    - (745185415790592000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    - (319365178195968000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    - (796021185576960 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (1567351677911040 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (1227364214243328 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (555931976859648 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (87223570236702720 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (149037083158118400 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (19161910691758080 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (10958609055744 : R) * h ^ 46 * a7 ^ 10 * b3
    - (22557168238592 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (21646635171840 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (25975962206208 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (1109931218436096 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (5086959265382400 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (7730941132800 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (9277129359360 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (2002313753395200 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (10181030996606976 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (757632231014400 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (8000596359512064 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (671045690327040 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (3656425918169088 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (310994115137372160 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (529909629006643200 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (68131238015139840 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    + (2513569883095040 : R) * h ^ 40 * a7 ^ 11 * a2
    + (4995011397550080 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (3919224766464000 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (1783044935516160 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (218261621204582400 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (372592707895296000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (47904776729395200 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (182305255587840 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (328620564283392 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (8577140958167040 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (65312440241356800 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (27944453092147200 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (2292438794240 : R) * h ^ 38 * a7 ^ 11 * b4
    + (4386235351040 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (4058744094720 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (232971911036928 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (1192594306498560 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (1417339207680 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (396704654295040 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (2165780208680960 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (30875317300101120 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (62910533468160 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (232557532592209920 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (99358055438745600 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (582525785210880 : R) * h ^ 32 * a7 ^ 12 * a3
    - (1054807393566720 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (21531531726028800 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (163359672332451840 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (69861132730368000 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (37362641928192 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (12742349171982336 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (16310973644144640 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (439227514880 : R) * h ^ 30 * a7 ^ 12 * b5
    - (801279836160 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (45115947089920 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (247666067898368 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (46390881288192 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (45503897527123968 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (58026028223692800 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (120192289996800 : R) * h ^ 24 * a7 ^ 13 * a4
    + (31902152890777600 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (40784801908654080 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (931598300086272 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (4761778781159424 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (79272345600 : R) * h ^ 22 * a7 ^ 13 * b6
    + (9643510202368 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (3334651464646656 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (16953876192165888 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (2334204113059840 : R) * h ^ 16 * a7 ^ 14 * a5
    - (11909854467194880 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (694857977561088 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (607673909248 : R) * h ^ 14 * a7 ^ 14 * b7
    - (2475378111152128 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (1738259924746240 : R) * h ^ 8 * a7 ^ 15 * a6
    + (40538987274240 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (144437568077824 : R) * h ^ 6 * a7 ^ 15 * b8
    - (101417221427200 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `17` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock17Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2296835809958952960 : R) * h ^ 104 * a5 ^ 3 * a0
    + (216172782113783808 : R) * h ^ 102 * a5 ^ 3 * b2
    + (5167880572407644160 : R) * h ^ 96 * a7 * a6 * a5 ^ 2 * a0
    + (287104476244869120 : R) * h ^ 96 * a7 * a5 ^ 3 * a1
    + (1794402976530432000 : R) * h ^ 96 * a5 ^ 4 * a3
    + (3588805953060864000 : R) * h ^ 96 * a5 ^ 3 * a4 ^ 2
    - (516788057240764416 : R) * h ^ 95 * a7 * a5 ^ 3 * a2 * lambda
    - (486388759756013568 : R) * h ^ 94 * a7 * a6 * a5 ^ 2 * b2
    - (81064793292668928 : R) * h ^ 94 * a7 * a5 ^ 3 * b3
    - (287104476244869120 : R) * h ^ 94 * a5 ^ 4 * b5
    - (1378101485975371776 : R) * h ^ 94 * a5 ^ 3 * a4 * b6
    - (1607785066971267072 : R) * h ^ 94 * a5 ^ 3 * a3 * b7
    - (1837468647967162368 : R) * h ^ 94 * a5 ^ 3 * a2 * b8
    - (2411677600456900608 : R) * h ^ 94 * a5 ^ 2 * a4 ^ 2 * b7
    - (1507298500285562880 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    - (3875910429305733120 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a5 * a0
    - (645985071550955520 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 ^ 2 * a1
    + (1256082083571302400 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 3 * a2
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 * a5 ^ 3 * a3
    - (8074813394386944000 : R) * h ^ 88 * a7 * a6 * a5 ^ 2 * a4 ^ 2
    - (5383208929591296000 : R) * h ^ 88 * a7 * a5 ^ 4 * a4
    + (1162773128791719936 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (419890296508121088 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 3 * a3 * lambda
    + (339142162564251648 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 2 * a4 ^ 2 * lambda
    + (141863388262170624 : R) * h ^ 86 * a7 ^ 3 * a5 ^ 2 * b2
    + (364791569817010176 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a5 * b2
    + (182395784908505088 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 ^ 2 * b3
    + (20266198323167232 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 3 * b4
    + (861313428734607360 : R) * h ^ 86 * a7 * a6 * a5 ^ 3 * b5
    + (3100728343444586496 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a4 * b6
    + (3617516400685350912 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a3 * b7
    + (4134304457926115328 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a2 * b8
    + (3617516400685350912 : R) * h ^ 86 * a7 * a6 * a5 * a4 ^ 2 * b7
    + (1076641785918259200 : R) * h ^ 86 * a7 * a5 ^ 4 * b6
    + (5024328334285209600 : R) * h ^ 86 * a7 * a5 ^ 3 * a4 * b7
    + (2296835809958952960 : R) * h ^ 86 * a7 * a5 ^ 3 * a3 * b8
    + (2411677600456900608 : R) * h ^ 86 * a7 * a5 ^ 2 * a4 ^ 2 * b8
    + (2260947750428344320 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    + (188412312535695360 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    + (968977607326433280 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 3 * a0
    + (484488803663216640 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    - (2826184688035430400 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    + (336450558099456000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 3 * a3
    + (1224680031482019840 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 2 * a4 ^ 2
    + (6056110045790208000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a3
    + (6056110045790208000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 * a4 ^ 2
    + (14467373998276608000 : R) * h ^ 80 * a7 ^ 2 * a6 * a5 ^ 3 * a4
    + (1682252790497280000 : R) * h ^ 80 * a7 ^ 2 * a5 ^ 5
    - (339142162564251648 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (872079846593789952 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (944753167143272448 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (508713243846377472 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (641947664853762048 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    - (212795082393255936 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (53198770598313984 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (91197892454252544 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 3 * b2
    - (136796838681378816 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (45598946227126272 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (255438541364920320 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 3 * b5
    - (904379100171337728 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a4 * b6
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a3 * b7
    - (1205838800228450304 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 ^ 2 * b7
    - (968977607326433280 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b5
    - (2325546257583439872 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b6
    - (2713137300514013184 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * b7
    - (3100728343444586496 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a2 * b8
    - (1356568650257006592 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * b7
    - (2906932821979299840 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 3 * b6
    - (10174264876927549440 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a4 * b7
    - (5167880572407644160 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a3 * b8
    - (3617516400685350912 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * a4 ^ 2 * b8
    - (2041133385803366400 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 4 * b7
    - (4593671619917905920 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 3 * a4 * b8
    - (329721546937466880 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    - (847855406410629120 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    - (282618468803543040 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    + (824303867343667200 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    - (121122200915804160 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    + (2119638516026572800 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (757013755723776000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (1837020047223029760 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (1974544212846182400 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    - (3028055022895104000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    - (1514027511447552000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    - (14383261358751744000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    - (5116852237762560000 : R) * h ^ 72 * a7 ^ 3 * a6 * a5 ^ 4
    + (508713243846377472 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (275553007083454464 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (148374696121860096 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (218019961648447488 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (708564875357454336 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (190767466442391552 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (1285409357218971648 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (215433497983057920 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (31032616182349824 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (79798155897470976 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (79798155897470976 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (13299692649578496 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (34199209670344704 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (34199209670344704 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (574736718071070720 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (1356568650257006592 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (1582663425299841024 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (1808758200342675456 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (791331712649920512 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (825095515715665920 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (2885063535702835200 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (1507298500285562880 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (1055108950199894016 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (484488803663216640 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (581386564395859968 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (678284325128503296 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (775182085861146624 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (2906932821979299840 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b6
    + (6782843251285032960 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (3875910429305733120 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (1356568650257006592 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (5008627308240568320 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 3 * b7
    + (9205287269601116160 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 2 * a4 * b8
    + (1637392716084019200 : R) * h ^ 70 * a7 ^ 3 * a5 ^ 4 * b8
    + (247291160203100160 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    + (41215193367183360 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    + (105981925801328640 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (1236455801015500800 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (294394238337024000 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    + (20607596683591680 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    - (529909629006643200 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (567760316792832000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (688882517708636160 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (3868655714146713600 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (681750466815590400 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    + (567760316792832000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (6245363484721152000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (6085023765626880000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    - (74187348060930048 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (190767466442391552 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (413329510625181696 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (111281022091395072 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (363319289387679744 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (177141218839363584 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (844827351387734016 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (510353440317112320 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (23274462136762368 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (11637231068381184 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (29924308461551616 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (19949538974367744 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (85201156036362240 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (197832928162480128 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (230805082856226816 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (263777237549973504 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (115402541428113408 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (8549802417586176 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (431052538553303040 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (508713243846377472 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (593498784487440384 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (678284325128503296 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (1644501058757591040 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (3833012983148052480 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (2260947750428344320 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (791331712649920512 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (1381534436155195392 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (2602445066899292160 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (90841650686853120 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (1271783109615943680 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (1483746961218600960 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (968977607326433280 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (4513063673706577920 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (6056110045790208000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (3918527499998330880 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    - (24042196130856960 : R) * h ^ 56 * a7 ^ 9 * a0
    - (30911395025387520 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (180316470981427200 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (463670925380812800 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (441591357505536000 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    - (15455697512693760 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (56578892680396800 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    - (141940079198208000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (2470940212042137600 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (1600253919127142400 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (993580554387456000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (3518931130122240000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    + (55640511045697536 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (60277220299505664 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (16228482388328448 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (154998566484443136 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (475428295274397696 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (139336800735854592 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (181399421215309824 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (439836820415447040 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (2262794929963008 : R) * h ^ 54 * a7 ^ 9 * b2
    + (8727923301285888 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (2909307767095296 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (7481077115387904 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (127801734054543360 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (148374696121860096 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (173103812142170112 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (197832928162480128 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (232354981934530560 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (540949412944281600 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (329721546937466880 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (115402541428113408 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (107763134638325760 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (1074402905366200320 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (1251911498528194560 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (847855406410629120 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (2473480908536020992 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (3409085279942737920 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (1072795694244298752 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (204393714045419520 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (1761949516447088640 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (1302063659844894720 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (3422963865464340480 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (3005274516357120 : R) * h ^ 48 * a7 ^ 10 * a1
    - (135237353236070400 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (101964671090688000 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (16529009839964160 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (165596759064576000 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (94528149966028800 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (17969821715005440 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (510097159618560000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (1366937175903436800 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (983230756945920000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    - (5409494129442816 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (45207915224629248 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (66797592687673344 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (152204121175228416 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (237876656851648512 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (162077827934453760 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (848548098736128 : R) * h ^ 46 * a7 ^ 10 * b3
    - (2181980825321472 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (12627203850240000 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (14425317678514176 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (16829537291599872 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (19233756904685568 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (47925650270453760 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (302165380363714560 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (351617118413783040 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (247291160203100160 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (338212473406488576 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (479126622893506560 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (228857504166051840 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (1436840867464740864 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (1092938609826201600 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (1858305183587500032 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (250051106187509760 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (1285030850341109760 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    + (13148076009062400 : R) * h ^ 40 * a7 ^ 11 * a2
    + (76473503318016000 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (82812754250956800 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (39070485341798400 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (35623755464048640 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (500431188079411200 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (105346152529920000 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (4395213980172288 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (42491093396226048 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (32063068418605056 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (129834599520927744 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (21291011879731200 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (212137024684032 : R) * h ^ 38 * a7 ^ 11 * b4
    + (9470402887680000 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (28288093425500160 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (32870190022656000 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (24042196130856960 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (95924357934612480 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (389549514999988224 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (305250025875701760 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (251520405372665856 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (269132479800016896 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (1035073907016597504 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (173403463420477440 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (8804515184640000 : R) * h ^ 32 * a7 ^ 12 * a3
    - (54361592325734400 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (39693575226654720 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (21979549956833280 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (65818243104768000 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (3946183705755648 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (34521813576843264 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (22353042972082176 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (701599013928960 : R) * h ^ 30 * a7 ^ 12 * b5
    - (17835136238223360 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (35104706921496576 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (28362278248120320 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (108256870891782144 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (276899072651034624 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (183594448003792896 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (7065623435673600 : R) * h ^ 24 * a7 ^ 13 * a4
    + (43447490948628480 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (4027318555115520 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (3045367352918016 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (8747341359611904 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (1240918728376320 : R) * h ^ 22 * a7 ^ 13 * b6
    + (19281983205015552 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (24593151616352256 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (72533327399092224 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (5501192049131520 : R) * h ^ 16 * a7 ^ 14 * a5
    - (11165947774894080 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (1511016595587072 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (1282681370836992 : R) * h ^ 14 * a7 ^ 14 * b7
    - (12666166912745472 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (2765206657597440 : R) * h ^ 8 * a7 ^ 15 * a6
    + (97124631109632 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (824371827965952 : R) * h ^ 6 * a7 ^ 15 * b8
    - (210519335792640 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `18` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock18Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (6890507429876858880 : R) * h ^ 104 * a5 ^ 2 * a4 * a1
    - (6890507429876858880 : R) * h ^ 104 * a5 ^ 2 * a3 * a2
    + (972777519512027136 : R) * h ^ 102 * a5 ^ 2 * a4 * b3
    + (1297036692682702848 : R) * h ^ 102 * a5 ^ 2 * a3 * b4
    + (1621295865853378560 : R) * h ^ 102 * a5 ^ 2 * a2 * b5
    + (1945555039024054272 : R) * h ^ 102 * a5 ^ 2 * a1 * b6
    + (2269814212194729984 : R) * h ^ 102 * a5 ^ 2 * a0 * b7
    + (10335761144815288320 : R) * h ^ 96 * a7 * a6 * a5 * a4 * a1
    + (10335761144815288320 : R) * h ^ 96 * a7 * a6 * a5 * a3 * a2
    + (4306567143673036800 : R) * h ^ 96 * a7 * a5 ^ 3 * a1
    + (5167880572407644160 : R) * h ^ 96 * a7 * a5 ^ 2 * a4 * a2
    + (2583940286203822080 : R) * h ^ 96 * a7 * a5 ^ 2 * a3 ^ 2
    - (319192623589883904 : R) * h ^ 95 * a7 ^ 2 * a5 ^ 2 * a0 * lambda
    - (1550364171722293248 : R) * h ^ 95 * a7 * a5 ^ 2 * a4 * a3 * lambda
    - (516788057240764416 : R) * h ^ 95 * a7 * a5 * a4 ^ 3 * lambda
    - (1459166279268040704 : R) * h ^ 94 * a7 * a6 * a5 * a4 * b3
    - (1945555039024054272 : R) * h ^ 94 * a7 * a6 * a5 * a3 * b4
    - (2431943798780067840 : R) * h ^ 94 * a7 * a6 * a5 * a2 * b5
    - (2918332558536081408 : R) * h ^ 94 * a7 * a6 * a5 * a1 * b6
    - (3404721318292094976 : R) * h ^ 94 * a7 * a6 * a5 * a0 * b7
    - (607985949695016960 : R) * h ^ 94 * a7 * a5 ^ 3 * b3
    - (1134907106097364992 : R) * h ^ 94 * a7 * a5 ^ 2 * a4 * b4
    - (1418633882621706240 : R) * h ^ 94 * a7 * a5 ^ 2 * a3 * b5
    - (1702360659146047488 : R) * h ^ 94 * a7 * a5 ^ 2 * a2 * b6
    - (1986087435670388736 : R) * h ^ 94 * a7 * a5 ^ 2 * a1 * b7
    - (2269814212194729984 : R) * h ^ 94 * a7 * a5 ^ 2 * a0 * b8
    - (5512405943901487104 : R) * h ^ 94 * a5 ^ 2 * a4 * a3 * b8
    - (1837468647967162368 : R) * h ^ 94 * a5 * a4 ^ 3 * b8
    + (1063975411966279680 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    - (3014597000571125760 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    - (3014597000571125760 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    - (3875910429305733120 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    - (3875910429305733120 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    - (8074813394386944000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 ^ 2 * a1
    - (7751820858611466240 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    - (3875910429305733120 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    - (2153283571836518400 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 3 * a2
    + (1614962678877388800 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 2 * a4 * a3
    + (1291970143101911040 : R) * h ^ 88 * a7 ^ 2 * a5 * a4 ^ 3
    + (478788935384825856 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (119697233846206464 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (2325546257583439872 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (387591042930573312 : R) * h ^ 87 * a7 ^ 2 * a6 * a4 ^ 3 * lambda
    + (968977607326433280 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 3 * a3 * lambda
    + (1744159693187579904 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 2 * a4 ^ 2 * lambda
    + (425590164786511872 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (567453553048682496 : R) * h ^ 86 * a7 ^ 3 * a5 * a3 * b4
    + (709316941310853120 : R) * h ^ 86 * a7 ^ 3 * a5 * a2 * b5
    + (851180329573023744 : R) * h ^ 86 * a7 ^ 3 * a5 * a1 * b6
    + (993043717835194368 : R) * h ^ 86 * a7 ^ 3 * a5 * a0 * b7
    + (547187354725515264 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (729583139634020352 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a3 * b4
    + (911978924542525440 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a2 * b5
    + (1094374709451030528 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a1 * b6
    + (1276770494359535616 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a0 * b7
    + (1139973655678156800 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 ^ 2 * b3
    + (1702360659146047488 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a4 * b4
    + (2127950823932559360 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a3 * b5
    + (2553540988719071232 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a2 * b6
    + (2979131153505583104 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a1 * b7
    + (3404721318292094976 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a0 * b8
    + (506654958079180800 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 3 * b4
    + (709316941310853120 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a4 * b5
    + (851180329573023744 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a3 * b6
    + (993043717835194368 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a2 * b7
    + (1134907106097364992 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a1 * b8
    + (8268608915852230656 : R) * h ^ 86 * a7 * a6 * a5 * a4 * a3 * b8
    + (1378101485975371776 : R) * h ^ 86 * a7 * a6 * a4 ^ 3 * b8
    + (3445253714938429440 : R) * h ^ 86 * a7 * a5 ^ 3 * a3 * b8
    + (6201456686889172992 : R) * h ^ 86 * a7 * a5 ^ 2 * a4 ^ 2 * b8
    - (1595963117949419520 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    + (2260947750428344320 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    + (2260947750428344320 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    + (1805156200250081280 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    + (2260947750428344320 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    + (1130473875214172160 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    + (4844888036632166400 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    + (2906932821979299840 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (1453466410989649920 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    + (3902826473953689600 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    - (2422444018316083200 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    - (968977607326433280 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    - (1682252790497280000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 3 * a3
    - (3983574607897559040 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 2 * a4 ^ 2
    - (139646772820574208 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (179545850769309696 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (179545850769309696 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (37405385576939520 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (678284325128503296 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (113047387521417216 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (872079846593789952 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (1816833013737062400 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (2252872937033957376 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (1332344210073845760 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    - (319192623589883904 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (425590164786511872 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (531987705983139840 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (638385247179767808 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (744782788376395776 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (315867700427489280 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (496521858917597184 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (620652323646996480 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (744782788376395776 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (868913253105795072 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (993043717835194368 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (683984193406894080 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (638385247179767808 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (797981558974709760 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (957577870769651712 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (1117174182564593664 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (1276770494359535616 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (924645298494504960 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (1063975411966279680 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (1276770494359535616 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (1489565576752791552 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (1702360659146047488 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (253327479039590400 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 3 * b5
    - (319192623589883904 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a4 * b6
    - (372391394188197888 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a3 * b7
    - (425590164786511872 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (2411677600456900608 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 * a3 * b8
    - (401946266742816768 : R) * h ^ 78 * a7 ^ 3 * a4 ^ 3 * b8
    - (3100728343444586496 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 * a3 * b8
    - (6459850715509555200 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a3 * b8
    - (8010214887231848448 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * a4 ^ 2 * b8
    - (4737223858040340480 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 3 * a4 * b8
    + (465489242735247360 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    - (329721546937466880 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    - (329721546937466880 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    + (598486169231032320 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    - (2001188128366264320 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (1695710812821258240 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    - (847855406410629120 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    - (936173677911736320 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    + (706546172008857600 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    + (282618468803543040 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    - (908416506868531200 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (2220573683456409600 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    + (908416506868531200 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    + (3229925357754777600 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    + (5066945404977807360 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    + (3120578926372454400 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    + (104735079615430656 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (52367539807715328 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (67329694038491136 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (56108078365409280 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (508713243846377472 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (513700628589969408 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (630592458517905408 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (1090099808242237440 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (708564875357454336 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (2240760716942376960 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (277571710432051200 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (46548924273524736 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (62065232364699648 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (77581540455874560 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (93097848547049472 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (108614156638224384 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (374053855769395200 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (372391394188197888 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (465489242735247360 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (558587091282296832 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (651684939829346304 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (744782788376395776 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (255464929643986944 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (310326161823498240 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (372391394188197888 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (434456626552897536 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (496521858917597184 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (128247036263792640 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (531987705983139840 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (398990779487354880 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (478788935384825856 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (558587091282296832 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (638385247179767808 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (453218692969267200 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (478788935384825856 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (558587091282296832 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (638385247179767808 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (1808758200342675456 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (97372749755842560 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (116372310683811840 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (1922913895584890880 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (2242106519174774784 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (3875910429305733120 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (2519341779048726528 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (7967149215795118080 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 2 * a4 * b8
    + (986921637091737600 : R) * h ^ 70 * a7 ^ 3 * a5 ^ 4 * b8
    - (349116932051435520 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    + (171527937101660160 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    + (247291160203100160 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    + (123645580101550080 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    + (485490733634027520 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (992108583195770880 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (529909629006643200 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    - (936801430331719680 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    - (1411620372826030080 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (378506877861888000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    - (2006086452668006400 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    - (1559448336790978560 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    - (5234750120829911040 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    - (667644076228608000 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    - (15273865777250304 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (39275654855786496 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (16364856189911040 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (74187348060930048 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (21040529387028480 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (611578054182961152 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (393457899537432576 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (602694275108438016 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (204393714045419520 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (1197974268432875520 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (558297644846284800 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (50912885924167680 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (54307078319112192 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (67883847898890240 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (81460617478668288 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (95037387058446336 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (108614156638224384 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (102864810336583680 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (288991238198132736 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (232744621367623680 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (279293545641148416 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (325842469914673152 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (372391394188197888 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (125030964752547840 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (139646772820574208 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (162921234957336576 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (186195697094098944 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (263777237549973504 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (92622859523850240 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (252337918574592000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (179545850769309696 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (209470159230861312 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (239394467692412928 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (171649158258622464 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (174558466025717760 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (2319133905770250240 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (1398961420577538048 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (31586770042748928 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (2170343594253090816 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (726733205494824960 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (4259464065539112960 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (1985058292786790400 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    + (50912885924167680 : R) * h ^ 56 * a7 ^ 9 * a0
    - (51367465262776320 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    - (100462033832509440 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (77278487563468800 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (217483743571476480 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (1162326898869534720 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (859999168742031360 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (1409339745191854080 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    + (397432221754982400 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    + (2799058361788661760 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    + (1344356546405990400 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    + (5727699666468864 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (12273642142433280 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (85642747393867776 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (54481333732245504 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (169726937055363072 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (634946679182721024 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (144525383222427648 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (200135511669473280 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (400980723734937600 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (27274760316518400 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (39033212541861888 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (33941923949445120 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (40730308739334144 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (47518693529223168 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (54307078319112192 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (73044405723856896 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (136460388123279360 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (104735079615430656 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (122190926218002432 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (139646772820574208 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (47320781436223488 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (50912885924167680 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (346692508912189440 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (193711408825761792 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (41190454355558400 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (93157222174949376 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (65459424759644160 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (657711363061186560 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (55060381223092224 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (2298734116784308224 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (520829587106562048 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (711592930380349440 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (1425709239946444800 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    - (3778690752184320 : R) * h ^ 48 * a7 ^ 10 * a1
    + (30267407629025280 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (168355352134287360 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (118171687232471040 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (344794369590558720 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (1487639876626022400 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (348695740714844160 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    - (471241062938050560 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    - (968445332029440000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    - (1789906145771520 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (46844400843620352 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (83734579592036352 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (155824115033309184 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (203875789307904000 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (121092630065971200 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (2386541527695360 : R) * h ^ 46 * a7 ^ 10 * b3
    - (18971111064600576 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (18334699990548480 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (15273865777250304 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (17819510073458688 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (20365154369667072 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (32015373419151360 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (50226378351575040 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (38184664443125760 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (198196591633367040 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (15175508878688256 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (309723844199841792 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (14394393913982976 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (29287897387499520 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (569471019446697984 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (736946706444189696 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (430551573567897600 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    + (281744485908480 : R) * h ^ 40 * a7 ^ 11 * a2
    + (99702034000773120 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (196912633306152960 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (369550389286010880 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (493938997387591680 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (294082101588787200 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (4295774749851648 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (40160752790667264 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (25739984287825920 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (90356699621228544 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (12974210364211200 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (1617544813215744 : R) * h ^ 38 * a7 ^ 11 * b4
    + (8163487289180160 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (6724527216132096 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (5568596897955840 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (19887846064128000 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (11051844205805568 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (15758953342304256 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (151794458604601344 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (94842364404695040 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (4320127214419968 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (327603153102962688 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (46130525739417600 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (9609351455047680 : R) * h ^ 32 * a7 ^ 12 * a3
    - (96155420967567360 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (62603553952235520 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (220453494010675200 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (31714736445849600 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (3423428564484096 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (22279230339416064 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (12603599011971072 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (679501407191040 : R) * h ^ 30 * a7 ^ 12 * b5
    - (2773339839922176 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (2104856231804928 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (13484788291731456 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (3282991262466048 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (82619955450740736 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (45719925792178176 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (8300280969953280 : R) * h ^ 24 * a7 ^ 13 * a4
    + (54665032992030720 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (30966849428520960 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (1813475969335296 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (4544225180909568 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (225869108871168 : R) * h ^ 22 * a7 ^ 13 * b6
    + (812545770258432 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (6902109161127936 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (16842069368635392 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (4480405034434560 : R) * h ^ 16 * a7 ^ 14 * a5
    - (11228531887964160 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (719980284248064 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (64900929945600 : R) * h ^ 14 * a7 ^ 14 * b7
    - (2727903772016640 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (1789756617277440 : R) * h ^ 8 * a7 ^ 15 * a6
    + (42247144525824 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (163454448697344 : R) * h ^ 6 * a7 ^ 15 * b8
    - (105640874035200 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `19` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock19Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (6890507429876858880 : R) * h ^ 104 * a5 * a4 ^ 2 * a2
    - (6890507429876858880 : R) * h ^ 104 * a5 * a4 * a3 ^ 2
    + (1459166279268040704 : R) * h ^ 103 * a7 * a5 * a4 * a0 * lambda
    + (1297036692682702848 : R) * h ^ 102 * a5 * a4 ^ 2 * b4
    + (3242591731706757120 : R) * h ^ 102 * a5 * a4 * a3 * b5
    + (3891110078048108544 : R) * h ^ 102 * a5 * a4 * a2 * b6
    + (4539628424389459968 : R) * h ^ 102 * a5 * a4 * a1 * b7
    + (5188146770730811392 : R) * h ^ 102 * a5 * a4 * a0 * b8
    + (1945555039024054272 : R) * h ^ 102 * a5 * a3 ^ 2 * b6
    + (4539628424389459968 : R) * h ^ 102 * a5 * a3 * a2 * b7
    - (3647915698170101760 : R) * h ^ 96 * a7 ^ 2 * a5 * a4 * a0
    + (5167880572407644160 : R) * h ^ 96 * a7 * a6 * a4 ^ 2 * a2
    + (5167880572407644160 : R) * h ^ 96 * a7 * a6 * a4 * a3 ^ 2
    + (8613134287346073600 : R) * h ^ 96 * a7 * a5 ^ 2 * a4 * a2
    + (4306567143673036800 : R) * h ^ 96 * a7 * a5 ^ 2 * a3 ^ 2
    + (9474447716080680960 : R) * h ^ 96 * a7 * a5 * a4 ^ 2 * a3
    - (1094374709451030528 : R) * h ^ 95 * a7 ^ 2 * a6 * a4 * a0 * lambda
    - (911978924542525440 : R) * h ^ 95 * a7 ^ 2 * a5 ^ 2 * a0 * lambda
    - (820781032088272896 : R) * h ^ 95 * a7 ^ 2 * a5 * a4 * a1 * lambda
    - (638385247179767808 : R) * h ^ 95 * a7 ^ 2 * a5 * a3 * a2 * lambda
    - (972777519512027136 : R) * h ^ 94 * a7 * a6 * a4 ^ 2 * b4
    - (2431943798780067840 : R) * h ^ 94 * a7 * a6 * a4 * a3 * b5
    - (2918332558536081408 : R) * h ^ 94 * a7 * a6 * a4 * a2 * b6
    - (3404721318292094976 : R) * h ^ 94 * a7 * a6 * a4 * a1 * b7
    - (3891110078048108544 : R) * h ^ 94 * a7 * a6 * a4 * a0 * b8
    - (1459166279268040704 : R) * h ^ 94 * a7 * a6 * a3 ^ 2 * b6
    - (3404721318292094976 : R) * h ^ 94 * a7 * a6 * a3 * a2 * b7
    - (1621295865853378560 : R) * h ^ 94 * a7 * a5 ^ 2 * a4 * b4
    - (2026619832316723200 : R) * h ^ 94 * a7 * a5 ^ 2 * a3 * b5
    - (2431943798780067840 : R) * h ^ 94 * a7 * a5 ^ 2 * a2 * b6
    - (2837267765243412480 : R) * h ^ 94 * a7 * a5 ^ 2 * a1 * b7
    - (3242591731706757120 : R) * h ^ 94 * a7 * a5 ^ 2 * a0 * b8
    - (2431943798780067840 : R) * h ^ 94 * a7 * a5 * a4 ^ 2 * b5
    - (5836665117072162816 : R) * h ^ 94 * a7 * a5 * a4 * a3 * b6
    - (6809442636584189952 : R) * h ^ 94 * a7 * a5 * a4 * a2 * b7
    - (5188146770730811392 : R) * h ^ 94 * a7 * a5 * a4 * a1 * b8
    - (3404721318292094976 : R) * h ^ 94 * a7 * a5 * a3 ^ 2 * b7
    - (4539628424389459968 : R) * h ^ 94 * a7 * a5 * a3 * a2 * b8
    + (2735936773627576320 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    + (2279947311356313600 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    + (2583940286203822080 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    + (2127950823932559360 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    - (1507298500285562880 : R) * h ^ 88 * a7 ^ 3 * a4 ^ 2 * a2
    - (1507298500285562880 : R) * h ^ 88 * a7 ^ 3 * a4 * a3 ^ 2
    - (9689776073264332800 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    - (4844888036632166400 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    - (7105835787060510720 : R) * h ^ 88 * a7 ^ 2 * a6 * a4 ^ 2 * a3
    - (2691604464795648000 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 3 * a2
    - (9689776073264332800 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 2 * a4 * a3
    - (2368611929020170240 : R) * h ^ 88 * a7 ^ 2 * a5 * a4 ^ 3
    + (319192623589883904 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (1025976290110341120 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (615585774066204672 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (478788935384825856 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (512988145055170560 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (661184720293330944 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (319192623589883904 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (283726776524341248 : R) * h ^ 86 * a7 ^ 3 * a4 ^ 2 * b4
    + (709316941310853120 : R) * h ^ 86 * a7 ^ 3 * a4 * a3 * b5
    + (851180329573023744 : R) * h ^ 86 * a7 ^ 3 * a4 * a2 * b6
    + (993043717835194368 : R) * h ^ 86 * a7 ^ 3 * a4 * a1 * b7
    + (1134907106097364992 : R) * h ^ 86 * a7 ^ 3 * a4 * a0 * b8
    + (425590164786511872 : R) * h ^ 86 * a7 ^ 3 * a3 ^ 2 * b6
    + (993043717835194368 : R) * h ^ 86 * a7 ^ 3 * a3 * a2 * b7
    + (1823957849085050880 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a4 * b4
    + (2279947311356313600 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a3 * b5
    + (2735936773627576320 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a2 * b6
    + (3191926235898839040 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a1 * b7
    + (3647915698170101760 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a0 * b8
    + (1823957849085050880 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 ^ 2 * b5
    + (4377498837804122112 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a3 * b6
    + (5107081977438142464 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a2 * b7
    + (3891110078048108544 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a1 * b8
    + (2553540988719071232 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 ^ 2 * b7
    + (3404721318292094976 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 * a2 * b8
    + (506654958079180800 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 3 * b4
    + (2533274790395904000 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a4 * b5
    + (3039929748475084800 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a3 * b6
    + (3546584706554265600 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a2 * b7
    + (3242591731706757120 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a1 * b8
    + (2371145203810566144 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 ^ 2 * b6
    + (5532672142224654336 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a3 * b7
    + (5188146770730811392 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a2 * b8
    + (2553540988719071232 : R) * h ^ 86 * a7 ^ 2 * a5 * a3 ^ 2 * b8
    - (797981558974709760 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    - (2564940725275852800 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    - (1937955214652866560 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    - (1595963117949419520 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    - (1614962678877388800 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    + (339221327401451520 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    + (198110005092679680 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    + (2072535437892648960 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    + (2422444018316083200 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (1211222009158041600 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    + (4037406697193472000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    + (10631837635942809600 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (1776458946765127680 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    + (2355153906696192000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 3 * a3
    + (3095345134514995200 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 2 * a4 ^ 2
    - (274306160897556480 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (179545850769309696 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (139646772820574208 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (256494072527585280 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (577111663187066880 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (495888540219998208 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (239394467692412928 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (313492755311493120 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (376903789908590592 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (487655397151211520 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (609569246439014400 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (731483095726817280 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (853396945014620160 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (975310794302423040 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (531987705983139840 : R) * h ^ 78 * a7 ^ 4 * a4 ^ 2 * b5
    - (1276770494359535616 : R) * h ^ 78 * a7 ^ 4 * a4 * a3 * b6
    - (1489565576752791552 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (1134907106097364992 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (744782788376395776 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (993043717835194368 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (455989462271262720 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (569986827839078400 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (683984193406894080 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (797981558974709760 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (911978924542525440 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (759982437118771200 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (2786602269435494400 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (3343922723322593280 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (3901243177209692160 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (3647915698170101760 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (1778358902857924608 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 ^ 2 * b6
    - (4149504106668490752 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (3891110078048108544 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (1915155741539303424 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (633318697598976000 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 3 * b5
    - (2127950823932559360 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a4 * b6
    - (2482609294587985920 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a3 * b7
    - (2533274790395904000 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (1613696041482190848 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 ^ 2 * b7
    - (3343922723322593280 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 * a3 * b8
    + (685765402243891200 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (565236937607086080 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (465489242735247360 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    + (641235181318963200 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    + (1816833013737062400 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    + (452130176457768960 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    + (204690582184919040 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    + (44282830808678400 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    - (1503290780402319360 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    - (518133859473162240 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    - (1892534389309440000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (2523379185745920000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (3364505580994560000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (3322449261232128000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (1261689592872960000 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    + (130918849519288320 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (154297215504875520 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (144634157564166144 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (69823386410287104 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (144277915796766720 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (340210887866449920 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (282677842431442944 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (148285635680010240 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (83894936222564352 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (232744621367623680 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (290930776709529600 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (349116932051435520 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (407303087393341440 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (465489242735247360 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (193953851139686400 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (742566172934799360 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (891079407521759232 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (1039592642108719104 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (975310794302423040 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (518688013333561344 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (1210272031111643136 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (1134907106097364992 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (558587091282296832 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (356241767399424000 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (664984632478924800 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (797981558974709760 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (930978485470494720 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (911978924542525440 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (910395627798528000 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (2294196982052290560 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (2676563145727672320 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (2761269521531535360 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (1210272031111643136 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (2507942042491944960 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (451239572039270400 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (1280095417521930240 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (1380634760765767680 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (821414350785871872 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    - (327297123798220800 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (485750493256089600 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (337947268302766080 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (162739403221893120 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    - (454208253434265600 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (229052323882598400 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    + (273724794124369920 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (320895904540262400 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    + (579195924916469760 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (283880158396416000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (1466714151714816000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (750705307759411200 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (1734823190200320000 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (157711199109120000 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    - (16364856189911040 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (73641852854599680 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (90474276364222464 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (82447704042504192 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (78818491037122560 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (156690714879590400 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (62921202166923264 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (57933817423331328 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (29093077670952960 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (36366347088691200 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (43639616506429440 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (50912885924167680 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (58186155341905920 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (176636543002214400 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (335263085541457920 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (402315702649749504 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (469368319758041088 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (465489242735247360 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (230320198228377600 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (609707784904114176 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (711325749054799872 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (734808018889211904 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (352996009074229248 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (731483095726817280 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (53436265109913600 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (400771988324352000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (523675398077153280 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (610954631090012160 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (645985071550955520 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (626391774343987200 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (1355737419466407936 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (1470091026801623040 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (616060763089403904 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (238978852297113600 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (599436147277430784 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    + (40912140474777600 : R) * h ^ 56 * a7 ^ 9 * a0
    + (231835462690406400 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (195799903245434880 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (134826067167805440 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (64081771049779200 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    - (152280212963328000 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    - (145522597319147520 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    - (222779438247444480 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    - (201081778864128000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (712328915976192000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (259566348533760000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    + (9205231606824960 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (39412028657369088 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (41533128321269760 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (18352017298685952 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (34107366089687040 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (60021171529187328 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (9281767924039680 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (21592518583910400 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (41215193367183360 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (49458232040620032 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (57701270714056704 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (58186155341905920 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (38963943309312000 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (195252649249996800 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (260902564399153152 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (304386325132345344 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (323902931403276288 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (157414330969620480 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (359524634242056192 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (390055048488419328 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (179684389234409472 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (55662776156160000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (261243962759577600 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (296749392243720192 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (325961217170472960 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (322188517897666560 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (626668851274186752 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (102271074057584640 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    - (28979432836300800 : R) * h ^ 48 * a7 ^ 10 * a1
    - (85826709969960960 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (63662331254538240 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (21417992587837440 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    + (19954525431398400 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (119691880169472000 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    + (27817375747276800 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (90683939487744000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (147032836669440000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    - (4790129780588544 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (16769715913359360 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (15877198086930432 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (12428106346266624 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (12040554267279360 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (9375698858803200 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (23344543118131200 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (31547806099439616 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (36805773782679552 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (39518097169711104 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (39613342364467200 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (125350252621332480 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (146179727315435520 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (161102917602902016 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (80544423645020160 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (165936611236773888 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (33954293455257600 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (128191373487636480 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (132818805612085248 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (134852352367656960 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    + (12537777597972480 : R) * h ^ 40 * a7 ^ 11 * a2
    + (27156232305377280 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (18722162076549120 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    - (16779452067348480 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    - (22785318243532800 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (34653339648000000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (1989672456683520 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (6027995995176960 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (2990406547537920 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (4484984702238720 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (745794227404800 : R) * h ^ 38 * a7 ^ 11 * b4
    + (9269156826316800 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (14690725719441408 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (17391447862935552 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (19259011312386048 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (23650301839933440 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (60688371076300800 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (64846283818401792 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (33583401554411520 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (15731692111134720 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (51685206943334400 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    - (4628862877040640 : R) * h ^ 32 * a7 ^ 12 * a3
    - (8131434837442560 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (3544623297331200 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    + (6294782921932800 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (2887778304000000 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (700913396219904 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (2082658918072320 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (506672594288640 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (714719467929600 : R) * h ^ 30 * a7 ^ 12 * b5
    - (5396176375382016 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (6984214964600832 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (7614677441839104 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (10750598420889600 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (24204151294525440 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (6055066368737280 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (1549044390297600 : R) * h ^ 24 * a7 ^ 13 * a4
    + (2785024946995200 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    - (573943106764800 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (233231329787904 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (336451652812800 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (404437994569728 : R) * h ^ 22 * a7 ^ 13 * b6
    + (2397780232372224 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (2743501729038336 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (4072569191792640 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (518792777072640 : R) * h ^ 16 * a7 ^ 14 * a5
    - (485324498534400 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (72449622540288 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (175138639183872 : R) * h ^ 14 * a7 ^ 14 * b7
    - (890954047291392 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (166087772282880 : R) * h ^ 8 * a7 ^ 15 * a6
    + (5080905252864 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (63648228704256 : R) * h ^ 6 * a7 ^ 15 * b8
    - (13813654256640 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `20` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock20Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6485183463413514240 : R) * h ^ 112 * a5 * a2 * a0
    + (3242591731706757120 : R) * h ^ 112 * a5 * a1 ^ 2
    - (576460752303423488 : R) * h ^ 110 * a5 * a3 * b1
    - (1152921504606846976 : R) * h ^ 110 * a5 * a2 * b2
    - (1729382256910270464 : R) * h ^ 110 * a5 * a1 * b3
    - (2305843009213693952 : R) * h ^ 110 * a5 * a0 * b4
    - (4863887597560135680 : R) * h ^ 104 * a7 * a6 * a2 * a0
    - (2431943798780067840 : R) * h ^ 104 * a7 * a6 * a1 ^ 2
    - (2431943798780067840 : R) * h ^ 104 * a7 * a5 * a3 * a0
    - (2431943798780067840 : R) * h ^ 104 * a7 * a5 * a2 * a1
    - (2296835809958952960 : R) * h ^ 104 * a4 ^ 3 * a3
    + (1459166279268040704 : R) * h ^ 103 * a7 * a5 * a3 * a1 * lambda
    + (729583139634020352 : R) * h ^ 103 * a7 * a5 * a2 ^ 2 * lambda
    + (432345564227567616 : R) * h ^ 102 * a7 * a6 * a3 * b1
    + (864691128455135232 : R) * h ^ 102 * a7 * a6 * a2 * b2
    + (1297036692682702848 : R) * h ^ 102 * a7 * a6 * a1 * b3
    + (1729382256910270464 : R) * h ^ 102 * a7 * a6 * a0 * b4
    + (288230376151711744 : R) * h ^ 102 * a7 * a5 * a4 * b1
    + (576460752303423488 : R) * h ^ 102 * a7 * a5 * a3 * b2
    + (864691128455135232 : R) * h ^ 102 * a7 * a5 * a2 * b3
    + (1152921504606846976 : R) * h ^ 102 * a7 * a5 * a1 * b4
    + (1441151880758558720 : R) * h ^ 102 * a7 * a5 * a0 * b5
    + (5188146770730811392 : R) * h ^ 102 * a5 * a3 * a1 * b8
    + (2594073385365405696 : R) * h ^ 102 * a5 * a2 ^ 2 * b8
    + (1418633882621706240 : R) * h ^ 96 * a7 ^ 3 * a2 * a0
    + (709316941310853120 : R) * h ^ 96 * a7 ^ 3 * a1 ^ 2
    + (1823957849085050880 : R) * h ^ 96 * a7 ^ 2 * a6 * a3 * a0
    + (1823957849085050880 : R) * h ^ 96 * a7 ^ 2 * a6 * a2 * a1
    + (607985949695016960 : R) * h ^ 96 * a7 ^ 2 * a5 * a4 * a0
    - (3039929748475084800 : R) * h ^ 96 * a7 ^ 2 * a5 * a3 * a1
    - (1519964874237542400 : R) * h ^ 96 * a7 ^ 2 * a5 * a2 ^ 2
    + (4306567143673036800 : R) * h ^ 96 * a7 * a5 * a4 ^ 2 * a3
    + (1148417904979476480 : R) * h ^ 96 * a7 * a4 ^ 4
    - (1094374709451030528 : R) * h ^ 95 * a7 ^ 2 * a6 * a3 * a1 * lambda
    - (547187354725515264 : R) * h ^ 95 * a7 ^ 2 * a6 * a2 ^ 2 * lambda
    - (729583139634020352 : R) * h ^ 95 * a7 ^ 2 * a5 * a4 * a1 * lambda
    - (911978924542525440 : R) * h ^ 95 * a7 ^ 2 * a5 * a3 * a2 * lambda
    - (126100789566373888 : R) * h ^ 94 * a7 ^ 3 * a3 * b1
    - (252201579132747776 : R) * h ^ 94 * a7 ^ 3 * a2 * b2
    - (378302368699121664 : R) * h ^ 94 * a7 ^ 3 * a1 * b3
    - (504403158265495552 : R) * h ^ 94 * a7 ^ 3 * a0 * b4
    - (216172782113783808 : R) * h ^ 94 * a7 ^ 2 * a6 * a4 * b1
    - (432345564227567616 : R) * h ^ 94 * a7 ^ 2 * a6 * a3 * b2
    - (648518346341351424 : R) * h ^ 94 * a7 ^ 2 * a6 * a2 * b3
    - (864691128455135232 : R) * h ^ 94 * a7 ^ 2 * a6 * a1 * b4
    - (1080863910568919040 : R) * h ^ 94 * a7 ^ 2 * a6 * a0 * b5
    - (90071992547409920 : R) * h ^ 94 * a7 ^ 2 * a5 ^ 2 * b1
    - (180143985094819840 : R) * h ^ 94 * a7 ^ 2 * a5 * a4 * b2
    - (270215977642229760 : R) * h ^ 94 * a7 ^ 2 * a5 * a3 * b3
    - (360287970189639680 : R) * h ^ 94 * a7 ^ 2 * a5 * a2 * b4
    - (450359962737049600 : R) * h ^ 94 * a7 ^ 2 * a5 * a1 * b5
    - (540431955284459520 : R) * h ^ 94 * a7 ^ 2 * a5 * a0 * b6
    - (3891110078048108544 : R) * h ^ 94 * a7 * a6 * a3 * a1 * b8
    - (1945555039024054272 : R) * h ^ 94 * a7 * a6 * a2 ^ 2 * b8
    - (2594073385365405696 : R) * h ^ 94 * a7 * a5 * a4 * a1 * b8
    - (3242591731706757120 : R) * h ^ 94 * a7 * a5 * a3 * a2 * b8
    - (531987705983139840 : R) * h ^ 88 * a7 ^ 4 * a3 * a0
    - (531987705983139840 : R) * h ^ 88 * a7 ^ 4 * a2 * a1
    - (455989462271262720 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    + (2279947311356313600 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    + (1139973655678156800 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    - (126663739519795200 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    + (1697294109565255680 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    + (2153283571836518400 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    - (1614962678877388800 : R) * h ^ 88 * a7 ^ 2 * a6 * a4 ^ 2 * a3
    - (2691604464795648000 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 2 * a4 * a3
    - (2512164167142604800 : R) * h ^ 88 * a7 ^ 2 * a5 * a4 ^ 3
    + (319192623589883904 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (159596311794941952 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (547187354725515264 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (683984193406894080 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (227994731135631360 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (319192623589883904 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (170996048351723520 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (63050394783186944 : R) * h ^ 86 * a7 ^ 4 * a4 * b1
    + (126100789566373888 : R) * h ^ 86 * a7 ^ 4 * a3 * b2
    + (189151184349560832 : R) * h ^ 86 * a7 ^ 4 * a2 * b3
    + (252201579132747776 : R) * h ^ 86 * a7 ^ 4 * a1 * b4
    + (315251973915934720 : R) * h ^ 86 * a7 ^ 4 * a0 * b5
    + (90071992547409920 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (135107988821114880 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (202661983231672320 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (270215977642229760 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (337769972052787200 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (405323966463344640 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6
    + (45035996273704960 : R) * h ^ 86 * a7 ^ 3 * a5 ^ 2 * b2
    + (67553994410557440 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (90071992547409920 : R) * h ^ 86 * a7 ^ 3 * a5 * a3 * b4
    + (112589990684262400 : R) * h ^ 86 * a7 ^ 3 * a5 * a2 * b5
    + (135107988821114880 : R) * h ^ 86 * a7 ^ 3 * a5 * a1 * b6
    + (157625986957967360 : R) * h ^ 86 * a7 ^ 3 * a5 * a0 * b7
    + (1134907106097364992 : R) * h ^ 86 * a7 ^ 3 * a3 * a1 * b8
    + (567453553048682496 : R) * h ^ 86 * a7 ^ 3 * a2 ^ 2 * b8
    + (1945555039024054272 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a1 * b8
    + (2431943798780067840 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 * a2 * b8
    + (810647932926689280 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a1 * b8
    + (1134907106097364992 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a2 * b8
    + (607985949695016960 : R) * h ^ 86 * a7 ^ 2 * a5 * a3 ^ 2 * b8
    + (132996926495784960 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    - (664984632478924800 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    - (332492316239462400 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    + (118747255799808000 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    - (1272970582173941760 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    - (1614962678877388800 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    - (546237376679116800 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    - (774232107814748160 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    - (415615395299328000 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    + (353273086004428800 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    + (2018703348596736000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (897201488265216000 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    + (560750930165760000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 3 * a3
    + (2018703348596736000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 2 * a4 ^ 2
    - (2216615441596416 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (159596311794941952 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (199495389743677440 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (227994731135631360 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (239394467692412928 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (128247036263792640 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (85498024175861760 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (96897760732643328 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (23643898043695104 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (39406496739491840 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (59109745109237760 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (78812993478983680 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (98516241848729600 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (118219490218475520 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (16888498602639360 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (43628621390151680 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (50665495807918080 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (67553994410557440 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (84442493013196800 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (101330991615836160 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (118219490218475520 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (14777436277309440 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (19703248369745920 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (24629060462182400 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (29554872554618880 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (34480684647055360 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (39406496739491840 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (567453553048682496 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (709316941310853120 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (810647932926689280 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (851180329573023744 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (455989462271262720 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (303992974847508480 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (344525371493842944 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 * a3 * b8
    - (21935256974131200 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (371283086467399680 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (471030781339238400 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    - (17812088369971200 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    + (548018585516113920 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    + (580674080861061120 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    + (311711546474496000 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    + (209588906486661120 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    - (203503109626920960 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    - (192337569046855680 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    - (378506877861888000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (630844796436480000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (1429914871922688000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (700938662707200000 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    + (1662461581197312 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (60264232318402560 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (69823386410287104 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (37405385576939520 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (42749012087930880 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (83716815338864640 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (72673320549482496 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (23155714880962560 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (12112220091580416 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (7881299347898368 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (11452513114914816 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (14777436277309440 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (19703248369745920 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (24629060462182400 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (29554872554618880 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (34480684647055360 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (7388718138654720 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (14038564463443968 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (14777436277309440 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (18471795346636800 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (22166154415964160 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (25860513485291520 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (29554872554618880 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (3940649673949184 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (4925812092436480 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (5910974510923776 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (6896136929411072 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (220676381741154304 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (248260929458798592 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (132996926495784960 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (151996487423754240 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (297659787871518720 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (258394028620382208 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (82331430687866880 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (43065671436730368 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (865865406873600 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (145593206581493760 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (169363273584476160 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (90915867721728000 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    - (103755414755082240 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (205482230556917760 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (12969426844385280 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (80800704343572480 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    + (275499818208460800 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (236566798663680000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (252337918574592000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (735985595842560000 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (87617332838400000 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    - (484884627849216 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (20261250520842240 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (22049881061326848 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (21196385160265728 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (14694972905226240 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (22309640683388928 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (9084165068685312 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (5343626510991360 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (862017116176384 : R) * h ^ 62 * a7 ^ 8 * b1
    - (3355709487972352 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (3687761999560704 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (4310085580881920 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (5387606976102400 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (6465128371322880 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (7542649766543360 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (8620171161763840 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (2216615441596416 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (3694359069327360 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (3694359069327360 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (4433230883192832 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (5172102697058304 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (76842668642009088 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (923589767331840 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (1108307720798208 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (1293025674264576 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (79613437944004608 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (75364925014278144 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (52248792551915520 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (79323166874271744 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (32299253577547776 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (18999560927969280 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    + (1262720385024000 : R) * h ^ 56 * a7 ^ 9 * a0
    + (49839831294935040 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (54250462060216320 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (33969658700759040 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (36217913018941440 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    - (48354717503324160 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    - (85187240342323200 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    - (143149198391377920 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    - (29570849832960000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (256280698552320000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (120473832652800000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    + (2272896693043200 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (6796424968667136 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (5871263243304960 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (2649548145033216 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (3707140892000256 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (5087577740673024 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (556627761561600 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (350194453446656 : R) * h ^ 54 * a7 ^ 9 * b2
    + (987911197556736 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (971281084186624 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (1077521395220480 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (1293025674264576 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (1508529953308672 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (9482188277940224 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (554153860399104 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (857619069665280 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (831230790598656 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (969769255698432 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (25075462183059456 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (197912092999680 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (230897441832960 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (21094130578882560 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (9420615626784768 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (13180945393778688 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (18089165300170752 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (1979120929996800 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    - (5710201969704960 : R) * h ^ 48 * a7 ^ 10 * a1
    - (16865724538552320 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (3214244807966720 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    + (4922918358220800 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    + (10221512137113600 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (96054817566228480 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    + (24012464219750400 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (29570849832960000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (61605937152000000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    - (732197434687488 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (1685712386654208 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (1338728421261312 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (809893393072128 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (633164078776320 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (99574521790464 : R) * h ^ 46 * a7 ^ 10 * b3
    - (243576185290752 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (225657581731840 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (242442313924608 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (282849366245376 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (2868900714774528 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (123695058124800 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (182450210734080 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (173173081374720 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (6157539993452544 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (39685497815040 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (4797718987800576 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (2879620953145344 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (2251250057871360 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    + (1838131917619200 : R) * h ^ 40 * a7 ^ 11 * a2
    - (49327531622400 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    - (8184769858764800 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    - (16747320343265280 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    - (24300763899494400 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (13861335859200000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (176301696614400 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (363576497799168 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (154722707177472 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (181991186104320 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (23901493002240 : R) * h ^ 38 * a7 ^ 11 * b4
    + (53794465382400 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (48041356689408 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (50508815400960 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (674653462855680 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (25512105738240 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (36378372997120 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (1321063220772864 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (556455962869760 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (647079772815360 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    - (132905775923200 : R) * h ^ 32 * a7 ^ 12 * a3
    + (3055755146035200 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    + (2326921216000000 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    + (8239427176366080 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (1155111321600000 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (37145964183552 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (77942986113024 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (15165932175360 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (5167382528000 : R) * h ^ 30 * a7 ^ 12 * b5
    - (11002095599616 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (9585024827392 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (140342351364096 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (4960687226880 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (282911643271168 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (53923314401280 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    - (185382802554880 : R) * h ^ 24 * a7 ^ 13 * a4
    - (1618448487546880 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    - (922420940636160 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (7653744967680 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (8953245204480 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (1038643888128 : R) * h ^ 22 * a7 ^ 13 * b6
    + (2124733743104 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (28737223524352 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (32608465453056 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    + (106542496972800 : R) * h ^ 16 * a7 ^ 14 * a5
    + (276102744637440 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (1653951430656 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (197711101952 : R) * h ^ 14 * a7 ^ 14 * b7
    - (6210958917632 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    - (36956834324480 : R) * h ^ 8 * a7 ^ 15 * a6
    + (97050820608 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (375486676992 : R) * h ^ 6 * a7 ^ 15 * b8
    + (1871129523200 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `21` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock21Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6485183463413514240 : R) * h ^ 112 * a4 * a3 * a0
    - (288230376151711744 : R) * h ^ 110 * a4 ^ 2 * b1
    - (1152921504606846976 : R) * h ^ 110 * a4 * a3 * b2
    - (4053239664633446400 : R) * h ^ 104 * a7 * a5 * a3 * a0
    - (3242591731706757120 : R) * h ^ 104 * a7 * a4 ^ 2 * a0
    - (810647932926689280 : R) * h ^ 104 * a7 * a4 * a3 * a1
    + (729583139634020352 : R) * h ^ 103 * a7 * a4 ^ 2 * a1 * lambda
    + (1459166279268040704 : R) * h ^ 103 * a7 * a4 * a3 * a2 * lambda
    + (360287970189639680 : R) * h ^ 102 * a7 * a5 * a4 * b1
    + (720575940379279360 : R) * h ^ 102 * a7 * a5 * a3 * b2
    + (648518346341351424 : R) * h ^ 102 * a7 * a4 ^ 2 * b2
    + (432345564227567616 : R) * h ^ 102 * a7 * a4 * a3 * b3
    + (540431955284459520 : R) * h ^ 102 * a4 ^ 3 * b5
    + (1945555039024054272 : R) * h ^ 102 * a4 ^ 2 * a3 * b6
    + (2269814212194729984 : R) * h ^ 102 * a4 ^ 2 * a2 * b7
    + (2594073385365405696 : R) * h ^ 102 * a4 ^ 2 * a1 * b8
    + (2269814212194729984 : R) * h ^ 102 * a4 * a3 ^ 2 * b7
    + (5188146770730811392 : R) * h ^ 102 * a4 * a3 * a2 * b8
    + (1519964874237542400 : R) * h ^ 96 * a7 ^ 2 * a6 * a3 * a0
    + (3039929748475084800 : R) * h ^ 96 * a7 ^ 2 * a5 * a4 * a0
    + (506654958079180800 : R) * h ^ 96 * a7 ^ 2 * a5 * a3 * a1
    - (1418633882621706240 : R) * h ^ 96 * a7 ^ 2 * a4 ^ 2 * a1
    - (3546584706554265600 : R) * h ^ 96 * a7 ^ 2 * a4 * a3 * a2
    - (911978924542525440 : R) * h ^ 95 * a7 ^ 2 * a5 * a4 * a1 * lambda
    - (911978924542525440 : R) * h ^ 95 * a7 ^ 2 * a5 * a3 * a2 * lambda
    - (1231171548132409344 : R) * h ^ 95 * a7 ^ 2 * a4 ^ 2 * a2 * lambda
    - (866379978315399168 : R) * h ^ 95 * a7 ^ 2 * a4 * a3 ^ 2 * lambda
    - (135107988821114880 : R) * h ^ 94 * a7 ^ 2 * a6 * a4 * b1
    - (270215977642229760 : R) * h ^ 94 * a7 ^ 2 * a6 * a3 * b2
    - (112589990684262400 : R) * h ^ 94 * a7 ^ 2 * a5 ^ 2 * b1
    - (630503947831869440 : R) * h ^ 94 * a7 ^ 2 * a5 * a4 * b2
    - (270215977642229760 : R) * h ^ 94 * a7 ^ 2 * a5 * a3 * b3
    - (229683580995895296 : R) * h ^ 94 * a7 ^ 2 * a4 ^ 2 * b3
    - (108086391056891904 : R) * h ^ 94 * a7 ^ 2 * a4 * a3 * b4
    - (1013309916158361600 : R) * h ^ 94 * a7 * a5 * a4 ^ 2 * b5
    - (2431943798780067840 : R) * h ^ 94 * a7 * a5 * a4 * a3 * b6
    - (2837267765243412480 : R) * h ^ 94 * a7 * a5 * a4 * a2 * b7
    - (3242591731706757120 : R) * h ^ 94 * a7 * a5 * a4 * a1 * b8
    - (1418633882621706240 : R) * h ^ 94 * a7 * a5 * a3 ^ 2 * b7
    - (3242591731706757120 : R) * h ^ 94 * a7 * a5 * a3 * a2 * b8
    - (1378101485975371776 : R) * h ^ 94 * a7 * a4 ^ 3 * b6
    - (4823355200913801216 : R) * h ^ 94 * a7 * a4 ^ 2 * a3 * b7
    - (5512405943901487104 : R) * h ^ 94 * a7 * a4 ^ 2 * a2 * b8
    - (4215369251218784256 : R) * h ^ 94 * a7 * a4 * a3 ^ 2 * b8
    - (332492316239462400 : R) * h ^ 88 * a7 ^ 4 * a3 * a0
    - (1013309916158361600 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    - (189995609279692800 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    - (633318697598976000 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    + (1899956092796928000 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    + (2216615441596416000 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    + (3293257227514675200 : R) * h ^ 88 * a7 ^ 3 * a4 ^ 2 * a2
    + (2419277424828088320 : R) * h ^ 88 * a7 ^ 3 * a4 * a3 ^ 2
    + (341992096703447040 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (341992096703447040 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (284993413919539200 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (1310969704029880320 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (541487486447124480 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (963277739048042496 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (29554872554618880 : R) * h ^ 86 * a7 ^ 4 * a4 * b1
    + (59109745109237760 : R) * h ^ 86 * a7 ^ 4 * a3 * b2
    + (84442493013196800 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (213920982300098560 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (101330991615836160 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (140737488355328000 : R) * h ^ 86 * a7 ^ 3 * a5 ^ 2 * b2
    + (219550481834311680 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (67553994410557440 : R) * h ^ 86 * a7 ^ 3 * a5 * a3 * b4
    + (56294995342131200 : R) * h ^ 86 * a7 ^ 3 * a4 ^ 2 * b4
    + (22517998136852480 : R) * h ^ 86 * a7 ^ 3 * a4 * a3 * b5
    + (379991218559385600 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 ^ 2 * b5
    + (911978924542525440 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a3 * b6
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a2 * b7
    + (1215971899390033920 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a1 * b8
    + (531987705983139840 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 ^ 2 * b7
    + (1215971899390033920 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 * a2 * b8
    + (633318697598976000 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a4 * b5
    + (759982437118771200 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a3 * b6
    + (886646176638566400 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a2 * b7
    + (1013309916158361600 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a1 * b8
    + (2279947311356313600 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 ^ 2 * b6
    + (5319877059831398400 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a3 * b7
    + (6079859496950169600 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a2 * b8
    + (2634605782011740160 : R) * h ^ 86 * a7 ^ 2 * a5 * a3 ^ 2 * b8
    + (1808758200342675456 : R) * h ^ 86 * a7 ^ 2 * a4 ^ 3 * b7
    + (5552938340547821568 : R) * h ^ 86 * a7 ^ 2 * a4 ^ 2 * a3 * b8
    + (210578466951659520 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    + (41561539529932800 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    + (395824185999360000 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    - (728316502238822400 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    - (831230790598656000 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    - (633318697598976000 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    - (3562417673994240000 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    - (1512048390517555200 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    - (2865767106635366400 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    - (74810771153879040 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (74810771153879040 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (213745060439654400 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (463114297619251200 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (203057807417671680 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (338429679029452800 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (961852771978444800 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (227875983879831552 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (18471795346636800 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (44824890041171968 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (22166154415964160 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (15832967439974400 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (91479367430963200 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (73887181386547200 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (25332747903959040 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (47498902319923200 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (53480245575024640 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (14073748835532800 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (94733921849180160 : R) * h ^ 78 * a7 ^ 4 * a4 ^ 2 * b5
    - (203717514394337280 : R) * h ^ 78 * a7 ^ 4 * a4 * a3 * b6
    - (232744621367623680 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (265993852991569920 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (116372310683811840 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (265993852991569920 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (474989023199232000 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (569986827839078400 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (664984632478924800 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (759982437118771200 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (816981119902679040 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 ^ 2 * b6
    - (1906289279772917760 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (2178616319740477440 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (987977168254402560 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (131941395333120000 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 3 * b5
    - (1234971460318003200 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a4 * b6
    - (1440800037037670400 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a3 * b7
    - (1646628613757337600 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (2682104684331663360 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 ^ 2 * b7
    - (5725201026294743040 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 * a3 * b8
    - (1528409123538862080 : R) * h ^ 78 * a7 ^ 3 * a4 ^ 3 * b8
    - (79659617432371200 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (160704619515740160 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (181831735443456000 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    - (59373627899904000 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    + (484884627849216000 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    + (1266637395197952000 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    + (567018146444083200 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    + (940082441748480000 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    + (2896245568957317120 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    + (716441776658841600 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    + (46756731971174400 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (98812560232415232 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (44418895372615680 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (40077198832435200 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (236010170902118400 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (332195448099962880 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (224877615670886400 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (299911037929390080 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (6926923254988800 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (18779658602414080 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (15423949114441728 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (5541538603991040 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (14513553486643200 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (30346520926617600 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (17944029765304320 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (5277655813324800 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (11434920928870400 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (114898965102592000 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (127323446496460800 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (145465388354764800 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (166246158119731200 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (177553535699779584 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (409981497718603776 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (467705858176843776 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (216120005555650560 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (89060441849856000 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (106872530219827200 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (124684618589798400 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (142496706959769600 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (148434069749760000 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (878729692918579200 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (1025184641738342400 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (1171639590558105600 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (919895408262512640 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (2001287084412764160 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (217703302299648000 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (1288407725427916800 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (1409134102157721600 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (2102618076028600320 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (23378365985587200 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (106934377748889600 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (271015872351436800 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (124035219534643200 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    - (92771293593600000 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (661768560967680000 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (1004750218136125440 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    - (690713204568883200 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    - (958042964188200960 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    - (17533774489190400 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (50068667152465920 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (70256937589014528 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (40912140474777600 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (150846123383193600 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (97960919757225984 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (124545461649408000 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (757632231014400 : R) * h ^ 62 * a7 ^ 8 * b1
    - (5887884766740480 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (6176506569031680 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (3740538557693952 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (1154487209164800 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (4700412208742400 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (7256776743321600 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (42647307262361600 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (47746292436172800 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (54549520633036800 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (62342309294899200 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (34806414966784000 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (190111058000609280 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (219872088985436160 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (250754621830594560 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (194209762471051264 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (425436233158623232 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (55662776156160000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (155855773237248000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (181831735443456000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (207807697649664000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (230072808112128000 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (872792330128588800 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (965811013838438400 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (699500501498068992 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (199149043580928000 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (924249474308505600 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (2272896693043200 : R) * h ^ 56 * a7 ^ 9 * a0
    + (40912140474777600 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (140973711556608000 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (212886539426856960 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (115964116992000000 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (467196234537369600 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (314939987491553280 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (406090875823718400 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    + (1917756584755200 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (17314602308075520 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (31490829063290880 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (20223233617821696 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (24943881564979200 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (79173341235118080 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (16321949466624000 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (593478580961280 : R) * h ^ 54 * a7 ^ 9 * b2
    + (1883257259950080 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (1471971191685120 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (5028934257213440 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (5330483911065600 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (5966353819238400 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (6818690079129600 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (1113255523123200 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (25829933318144000 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (67312789047214080 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (77906239983452160 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (88837790745231360 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (49462561367654400 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (183248387456368640 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (203555336429240320 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (145570116837310464 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (6957847019520000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (80711025426432000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (146980652816793600 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (164019647073484800 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (199149043580928000 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (602741279230525440 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (129467494170624000 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    - (4510279375257600 : R) * h ^ 48 * a7 ^ 10 * a1
    - (49313740750848000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (97885069561036800 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (65191526174556160 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (78067043559014400 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (260501792410828800 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (54483807633408000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    - (1829859407953920 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (10347913024634880 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (16140006598901760 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (12401927446855680 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (15131142940262400 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (187040457031680 : R) * h ^ 46 * a7 ^ 10 * b3
    - (443756021022720 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (2962695284326400 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (7259514784972800 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (8341057343324160 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (9489343693455360 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (4791572889600000 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (34610134961356800 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (61563030428712960 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (68865162026680320 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (41508174561280000 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (124298415130542080 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (9393093476352000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (65886945804288000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (97292347968061440 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (123880600711987200 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    + (5238316597248000 : R) * h ^ 40 * a7 ^ 11 * a2
    + (32536541528064000 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (53316565713551360 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (41247470046412800 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (51067698020352000 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (1070002266439680 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (5021611673518080 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (3043944824832000 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (4603866041548800 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (43800613355520 : R) * h ^ 38 * a7 ^ 11 * b4
    + (1088462153318400 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (3704308629504000 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (6439025573363712 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (7215657800171520 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (6023127918182400 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (27369464345395200 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (39942336859340800 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (25287801071206400 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (7204270768128000 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (39064445544038400 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    - (3381738445209600 : R) * h ^ 32 * a7 ^ 12 * a3
    - (16782516258078720 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (10324369054105600 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (15731559235584000 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (506615622008832 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (1838418178867200 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (459360593510400 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (81648313958400 : R) * h ^ 30 * a7 ^ 12 * b5
    - (1285004722176000 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (2837631121489920 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (4090581747761152 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (4470854595379200 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (15862790619136000 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (4055844991795200 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (1702150117785600 : R) * h ^ 24 * a7 ^ 13 * a4
    + (6317742017740800 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (1591109222400000 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (182845339729920 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (272945656627200 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (91201182105600 : R) * h ^ 22 * a7 ^ 13 * b6
    + (923049834577920 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (1606182208798720 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (2455867333017600 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (632182987161600 : R) * h ^ 16 * a7 ^ 14 * a5
    - (951425512243200 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (53842938347520 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (63390688542720 : R) * h ^ 14 * a7 ^ 14 * b7
    - (494265717227520 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (188946203443200 : R) * h ^ 8 * a7 ^ 15 * a6
    + (3525637086720 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (33058212741120 : R) * h ^ 6 * a7 ^ 15 * b8
    - (12459767040000 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `22` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock22Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6485183463413514240 : R) * h ^ 112 * a4 * a2 * a1
    + (3242591731706757120 : R) * h ^ 112 * a3 ^ 2 * a1
    + (3242591731706757120 : R) * h ^ 112 * a3 * a2 ^ 2
    - (1729382256910270464 : R) * h ^ 110 * a4 * a2 * b3
    - (2305843009213693952 : R) * h ^ 110 * a4 * a1 * b4
    - (2882303761517117440 : R) * h ^ 110 * a4 * a0 * b5
    - (864691128455135232 : R) * h ^ 110 * a3 ^ 2 * b3
    - (2305843009213693952 : R) * h ^ 110 * a3 * a2 * b4
    - (4053239664633446400 : R) * h ^ 104 * a7 * a5 * a2 * a1
    - (5674535530486824960 : R) * h ^ 104 * a7 * a4 * a3 * a1
    - (3242591731706757120 : R) * h ^ 104 * a7 * a4 * a2 ^ 2
    - (3242591731706757120 : R) * h ^ 104 * a7 * a3 ^ 2 * a2
    + (243194379878006784 : R) * h ^ 103 * a7 * a3 ^ 3 * lambda
    + (1080863910568919040 : R) * h ^ 102 * a7 * a5 * a2 * b3
    + (1441151880758558720 : R) * h ^ 102 * a7 * a5 * a1 * b4
    + (1801439850948198400 : R) * h ^ 102 * a7 * a5 * a0 * b5
    + (1513209474796486656 : R) * h ^ 102 * a7 * a4 * a3 * b3
    + (2594073385365405696 : R) * h ^ 102 * a7 * a4 * a2 * b4
    + (1801439850948198400 : R) * h ^ 102 * a7 * a4 * a1 * b5
    + (2161727821137838080 : R) * h ^ 102 * a7 * a4 * a0 * b6
    + (1297036692682702848 : R) * h ^ 102 * a7 * a3 ^ 2 * b4
    + (1441151880758558720 : R) * h ^ 102 * a7 * a3 * a2 * b5
    + (864691128455135232 : R) * h ^ 102 * a3 ^ 3 * b8
    + (1519964874237542400 : R) * h ^ 96 * a7 ^ 2 * a6 * a2 * a1
    + (2533274790395904000 : R) * h ^ 96 * a7 ^ 2 * a5 * a3 * a1
    + (1519964874237542400 : R) * h ^ 96 * a7 ^ 2 * a5 * a2 ^ 2
    + (1418633882621706240 : R) * h ^ 96 * a7 ^ 2 * a4 ^ 2 * a1
    + (3546584706554265600 : R) * h ^ 96 * a7 ^ 2 * a4 * a3 * a2
    - (364791569817010176 : R) * h ^ 95 * a7 ^ 2 * a4 * a3 ^ 2 * lambda
    - (405323966463344640 : R) * h ^ 94 * a7 ^ 2 * a6 * a2 * b3
    - (540431955284459520 : R) * h ^ 94 * a7 ^ 2 * a6 * a1 * b4
    - (675539944105574400 : R) * h ^ 94 * a7 ^ 2 * a6 * a0 * b5
    - (675539944105574400 : R) * h ^ 94 * a7 ^ 2 * a5 * a3 * b3
    - (1261007895663738880 : R) * h ^ 94 * a7 ^ 2 * a5 * a2 * b4
    - (1125899906842624000 : R) * h ^ 94 * a7 ^ 2 * a5 * a1 * b5
    - (1351079888211148800 : R) * h ^ 94 * a7 ^ 2 * a5 * a0 * b6
    - (378302368699121664 : R) * h ^ 94 * a7 ^ 2 * a4 ^ 2 * b3
    - (1513209474796486656 : R) * h ^ 94 * a7 ^ 2 * a4 * a3 * b4
    - (1396115884484853760 : R) * h ^ 94 * a7 ^ 2 * a4 * a2 * b5
    - (810647932926689280 : R) * h ^ 94 * a7 ^ 2 * a4 * a1 * b6
    - (945755921747804160 : R) * h ^ 94 * a7 ^ 2 * a4 * a0 * b7
    - (675539944105574400 : R) * h ^ 94 * a7 ^ 2 * a3 ^ 2 * b5
    - (540431955284459520 : R) * h ^ 94 * a7 ^ 2 * a3 * a2 * b6
    - (1297036692682702848 : R) * h ^ 94 * a7 * a4 * a3 ^ 2 * b8
    - (332492316239462400 : R) * h ^ 88 * a7 ^ 4 * a2 * a1
    - (823314306878668800 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    - (506654958079180800 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    - (1013309916158361600 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    - (1329969264957849600 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    - (709316941310853120 : R) * h ^ 88 * a7 ^ 3 * a4 ^ 2 * a2
    + (164662861375733760 : R) * h ^ 88 * a7 ^ 3 * a4 * a3 ^ 2
    + (22166154415964160 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (113997365567815680 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (182395784908505088 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (88664617663856640 : R) * h ^ 86 * a7 ^ 4 * a2 * b3
    + (118219490218475520 : R) * h ^ 86 * a7 ^ 4 * a1 * b4
    + (147774362773094400 : R) * h ^ 86 * a7 ^ 4 * a0 * b5
    + (219550481834311680 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (427841964600197120 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (422212465065984000 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (506654958079180800 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6
    + (270215977642229760 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (585467951558164480 : R) * h ^ 86 * a7 ^ 3 * a5 * a3 * b4
    + (647392446434508800 : R) * h ^ 86 * a7 ^ 3 * a5 * a2 * b5
    + (506654958079180800 : R) * h ^ 86 * a7 ^ 3 * a5 * a1 * b6
    + (591097451092377600 : R) * h ^ 86 * a7 ^ 3 * a5 * a0 * b7
    + (315251973915934720 : R) * h ^ 86 * a7 ^ 3 * a4 ^ 2 * b4
    + (714946440845066240 : R) * h ^ 86 * a7 ^ 3 * a4 * a3 * b5
    + (506654958079180800 : R) * h ^ 86 * a7 ^ 3 * a4 * a2 * b6
    + (275845477176442880 : R) * h ^ 86 * a7 ^ 3 * a4 * a1 * b7
    + (315251973915934720 : R) * h ^ 86 * a7 ^ 3 * a4 * a0 * b8
    + (236438980436951040 : R) * h ^ 86 * a7 ^ 3 * a3 ^ 2 * b6
    + (157625986957967360 : R) * h ^ 86 * a7 ^ 3 * a3 * a2 * b7
    + (405323966463344640 : R) * h ^ 86 * a7 ^ 2 * a5 * a3 ^ 2 * b8
    + (648518346341351424 : R) * h ^ 86 * a7 ^ 2 * a4 ^ 2 * a3 * b8
    - (88664617663856640 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    + (169016927421726720 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    + (105289233475829760 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    + (292909897639526400 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    + (395824185999360000 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    + (158329674399744000 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    + (451239572039270400 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    - (43540660459929600 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    - (202661983231672320 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    - (13853846509977600 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (4987384743591936 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (2216615441596416 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (28499341391953920 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (113997365567815680 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (30399297484750848 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (45071180645793792 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (89649780082343936 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (92358976733184000 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (110830772079820800 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (78109306037207040 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (177329235327713280 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (214624669741875200 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (189995609279692800 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (221661544159641600 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (42221246506598400 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (205476732998778880 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (263882790666240000 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (232216855786291200 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (172403423235276800 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (197032483697459200 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (138626426029998080 : R) * h ^ 78 * a7 ^ 4 * a4 ^ 2 * b5
    - (240661105087610880 : R) * h ^ 78 * a7 ^ 4 * a4 * a3 * b6
    - (147774362773094400 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (78812993478983680 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (66498463247892480 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (39406496739491840 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (101330991615836160 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (405323966463344640 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 * a3 * b8
    - (108086391056891904 : R) * h ^ 78 * a7 ^ 3 * a4 ^ 3 * b8
    + (55415386039910400 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    - (36481795809607680 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    - (68691988945305600 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    - (84112639524864000 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (121913849287802880 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    + (5343626510991360 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    - (64321430224896000 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    + (139528025564774400 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    + (50665495807918080 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    + (5195192441241600 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (3117115464744960 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (2147346209046528 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (5887884766740480 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (28499341391953920 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (17812088369971200 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (28499341391953920 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (15146872184242176 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (35219556460920832 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (44486240459816960 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (41561539529932800 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (48488462784921600 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (22430037206630400 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (56365364086308864 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (77845423246540800 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (76526009293209600 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (64651283713228800 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (73887181386547200 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (29906716275507200 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (86729477198970880 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (87081320919859200 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (67729916271001600 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (49258120924364800 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (44860074413260800 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (66498463247892480 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (37436171902517248 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (33988103437811712 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (101330991615836160 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (63331869759897600 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (101330991615836160 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    - (20780769764966400 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    + (2886218022912000 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    + (13928063544852480 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (3815992543150080 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    + (10514079940608000 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (32284410170572800 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (34461443193569280 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    - (25357486915584000 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    - (51209754063667200 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    - (1136448346521600 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (1168918299279360 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (995745217904640 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (5879226112671744 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (8906044184985600 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (7124835347988480 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (8906044184985600 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (4156153952993280 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (10643272556871680 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (15258472614461440 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (15816474765557760 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (14142468312268800 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (16162820928307200 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (2803754650828800 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (15217240928419840 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (23199695346073600 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (25398718601625600 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (22320086043852800 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (18471795346636800 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (12149603486924800 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (27443810229288960 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (23859402322739200 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (17240342323527680 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (12083632789258240 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (33864958135500800 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (31665934879948800 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (25332747903959040 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (31665934879948800 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    + (4545793386086400 : R) * h ^ 56 * a7 ^ 9 * a0
    + (1001156876697600 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    - (1678902716006400 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (9546166110781440 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (3834546801868800 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (13142599925760000 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (13037459126353920 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (17317308137472000 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    + (255700877967360 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (330111186370560 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (1877845601157120 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (1403784290893824 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (1113255523123200 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (4453022092492800 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (927712935936000 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (1002960762961920 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (2755651017113600 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (4322626885386240 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (4949863909294080 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (4613138473287680 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (4040705232076800 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (1830686860247040 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (6033570057420800 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (7240284068904960 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (6926923254988800 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (5695470231879680 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (3752083429785600 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (7292510871224320 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (11313974649815040 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (7311752324710400 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (3958241859993600 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (15832967439974400 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (3298534883328000 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    - (712647817297920 : R) * h ^ 48 * a7 ^ 10 * a1
    - (32212254720000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (3638535231897600 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (2940334610841600 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (1748159063654400 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (8888649567436800 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (1932735283200000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    - (68423660863488 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (482314089922560 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (872629980364800 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (556627761561600 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (695784701952000 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (87759066759168 : R) * h ^ 46 * a7 ^ 10 * b3
    - (641324516638720 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (1078144165478400 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (1339127853219840 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (1346901744025600 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (1178539026022400 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (708669603840000 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (1834810028851200 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (1908511667650560 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (3059391104286720 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (980111536947200 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (4492879388999680 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (1979120929996800 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (2473901162496000 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    + (169424380231680 : R) * h ^ 40 * a7 ^ 11 * a2
    + (1010252812124160 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (1959036589178880 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (1147078390579200 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (1486998208512000 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (52116810891264 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (219070712512512 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (134023112294400 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (173946175488000 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (55003498676224 : R) * h ^ 38 * a7 ^ 11 * b4
    + (244960775372800 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (325102180761600 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (351513545277440 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (446582109503488 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (211956636057600 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (474271763660800 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (1141258709893120 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (661424963584000 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (618475290624000 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    - (131292620390400 : R) * h ^ 32 * a7 ^ 12 * a3
    - (507880553840640 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (314150014156800 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (381715218432000 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (21497867403264 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (66736745349120 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (14495514624000 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (20726488760320 : R) * h ^ 30 * a7 ^ 12 * b5
    - (72588302745600 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (83558924288000 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (143036906471424 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (54116587929600 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (326202766131200 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (51539607552000 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (54706726502400 : R) * h ^ 24 * a7 ^ 13 * a4
    + (159614553292800 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (32614907904000 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (6351861841920 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (8266784440320 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (6081510113280 : R) * h ^ 22 * a7 ^ 13 * b6
    + (18407332249600 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (38198700933120 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (39460012032000 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (16255097241600 : R) * h ^ 16 * a7 ^ 14 * a5
    - (20062745395200 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (1553056727040 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (1530552647680 : R) * h ^ 14 * a7 ^ 14 * b7
    - (8931644538880 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (3990750167040 : R) * h ^ 8 * a7 ^ 15 * a6
    + (95884830720 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (623049441280 : R) * h ^ 6 * a7 ^ 15 * b8
    - (256945274880 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Integer expansion of compact block `23` after the extra
`2^{34}` scale. -/
def degreeZeroCompactBlock23Expansion810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (4611686018427387904 : R) * h ^ 118 * a0 * b1
    - (1297036692682702848 : R) * h ^ 111 * a7 * a1 * a0 * lambda
    - (576460752303423488 : R) * h ^ 110 * a7 * a1 * b1
    - (1152921504606846976 : R) * h ^ 110 * a7 * a0 * b2
    - (2882303761517117440 : R) * h ^ 110 * a3 * a1 * b5
    - (3458764513820540928 : R) * h ^ 110 * a3 * a0 * b6
    - (1441151880758558720 : R) * h ^ 110 * a2 ^ 2 * b5
    - (3458764513820540928 : R) * h ^ 110 * a2 * a1 * b6
    - (4035225266123964416 : R) * h ^ 110 * a2 * a0 * b7
    - (2017612633061982208 : R) * h ^ 110 * a1 ^ 2 * b7
    - (4611686018427387904 : R) * h ^ 110 * a1 * a0 * b8
    + (3242591731706757120 : R) * h ^ 104 * a7 ^ 2 * a1 * a0
    + (891712726219358208 : R) * h ^ 103 * a7 ^ 2 * a2 * a0 * lambda
    + (445856363109679104 : R) * h ^ 103 * a7 ^ 2 * a1 ^ 2 * lambda
    + (72057594037927936 : R) * h ^ 102 * a7 ^ 2 * a2 * b1
    + (144115188075855872 : R) * h ^ 102 * a7 ^ 2 * a1 * b2
    + (216172782113783808 : R) * h ^ 102 * a7 ^ 2 * a0 * b3
    + (1441151880758558720 : R) * h ^ 102 * a7 * a4 * a1 * b5
    + (1729382256910270464 : R) * h ^ 102 * a7 * a4 * a0 * b6
    + (1801439850948198400 : R) * h ^ 102 * a7 * a3 * a2 * b5
    + (3891110078048108544 : R) * h ^ 102 * a7 * a3 * a1 * b6
    + (4539628424389459968 : R) * h ^ 102 * a7 * a3 * a0 * b7
    + (1945555039024054272 : R) * h ^ 102 * a7 * a2 ^ 2 * b6
    + (4539628424389459968 : R) * h ^ 102 * a7 * a2 * a1 * b7
    + (5188146770730811392 : R) * h ^ 102 * a7 * a2 * a0 * b8
    + (2594073385365405696 : R) * h ^ 102 * a7 * a1 ^ 2 * b8
    - (2702159776422297600 : R) * h ^ 96 * a7 ^ 3 * a2 * a0
    - (1351079888211148800 : R) * h ^ 96 * a7 ^ 3 * a1 ^ 2
    - (415457065624928256 : R) * h ^ 95 * a7 ^ 3 * a3 * a0 * lambda
    - (415457065624928256 : R) * h ^ 95 * a7 ^ 3 * a2 * a1 * lambda
    - (9007199254740992 : R) * h ^ 94 * a7 ^ 3 * a3 * b1
    - (18014398509481984 : R) * h ^ 94 * a7 ^ 3 * a2 * b2
    - (27021597764222976 : R) * h ^ 94 * a7 ^ 3 * a1 * b3
    - (36028797018963968 : R) * h ^ 94 * a7 ^ 3 * a0 * b4
    - (450359962737049600 : R) * h ^ 94 * a7 ^ 2 * a5 * a1 * b5
    - (540431955284459520 : R) * h ^ 94 * a7 ^ 2 * a5 * a0 * b6
    - (630503947831869440 : R) * h ^ 94 * a7 ^ 2 * a4 * a2 * b5
    - (1621295865853378560 : R) * h ^ 94 * a7 ^ 2 * a4 * a1 * b6
    - (1891511843495608320 : R) * h ^ 94 * a7 ^ 2 * a4 * a0 * b7
    - (337769972052787200 : R) * h ^ 94 * a7 ^ 2 * a3 ^ 2 * b5
    - (1891511843495608320 : R) * h ^ 94 * a7 ^ 2 * a3 * a2 * b6
    - (2837267765243412480 : R) * h ^ 94 * a7 ^ 2 * a3 * a1 * b7
    - (3242591731706757120 : R) * h ^ 94 * a7 ^ 2 * a3 * a0 * b8
    - (1418633882621706240 : R) * h ^ 94 * a7 ^ 2 * a2 ^ 2 * b7
    - (3242591731706757120 : R) * h ^ 94 * a7 ^ 2 * a2 * a1 * b8
    + (1393301134717747200 : R) * h ^ 88 * a7 ^ 4 * a3 * a0
    + (1393301134717747200 : R) * h ^ 88 * a7 ^ 4 * a2 * a1
    + (134263563890982912 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (156429718306947072 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (78214859153473536 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (1125899906842624 : R) * h ^ 86 * a7 ^ 4 * a4 * b1
    + (2251799813685248 : R) * h ^ 86 * a7 ^ 4 * a3 * b2
    + (3377699720527872 : R) * h ^ 86 * a7 ^ 4 * a2 * b3
    + (4503599627370496 : R) * h ^ 86 * a7 ^ 4 * a1 * b4
    + (5629499534213120 : R) * h ^ 86 * a7 ^ 4 * a0 * b5
    + (112589990684262400 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (135107988821114880 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6
    + (168884986026393600 : R) * h ^ 86 * a7 ^ 3 * a5 * a2 * b5
    + (472877960873902080 : R) * h ^ 86 * a7 ^ 3 * a5 * a1 * b6
    + (551690954352885760 : R) * h ^ 86 * a7 ^ 3 * a5 * a0 * b7
    + (191402984163246080 : R) * h ^ 86 * a7 ^ 3 * a4 * a3 * b5
    + (607985949695016960 : R) * h ^ 86 * a7 ^ 3 * a4 * a2 * b6
    + (1024568915226787840 : R) * h ^ 86 * a7 ^ 3 * a4 * a1 * b7
    + (1170935903116328960 : R) * h ^ 86 * a7 ^ 3 * a4 * a0 * b8
    + (320881473450147840 : R) * h ^ 86 * a7 ^ 3 * a3 ^ 2 * b6
    + (1142788405445263360 : R) * h ^ 86 * a7 ^ 3 * a3 * a2 * b7
    + (1486187877032263680 : R) * h ^ 86 * a7 ^ 3 * a3 * a1 * b8
    + (743093938516131840 : R) * h ^ 86 * a7 ^ 3 * a2 ^ 2 * b8
    - (468655836223242240 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    - (557320453887098880 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    - (278660226943549440 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    - (34832528367943680 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (45915605575925760 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (48686374877921280 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (140737488355328 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (281474976710656 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (422212465065984 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (562949953421312 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (20406935811522560 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (24488322973827072 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (38702809297715200 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (113997365567815680 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (132996926495784960 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (45739683715481600 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (156218612074414080 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (280771289268879360 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (320881473450147840 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (23925373020405760 : R) * h ^ 78 * a7 ^ 4 * a4 ^ 2 * b5
    - (173107110677053440 : R) * h ^ 78 * a7 ^ 4 * a4 * a3 * b6
    - (339881034378117120 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (478507460408115200 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (177329235327713280 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (517913957147607040 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    + (124024911613132800 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (168357220445061120 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (179440297653043200 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    + (7857110092087296 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (11320571719581696 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (12705956370579456 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (6526151266664448 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (17592186044416 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (35184372088832 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (52776558133248 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (70368744177664 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (6553089301544960 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (19685656183701504 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (22966598880985088 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (9763663254650880 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (34938081484210176 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (65390155527094272 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (74731606316679168 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (10555311626649600 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (40215737297534976 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (83861950873731072 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (123989727241043968 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (20899517020766208 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (91250669012385792 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (143692975610789888 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (74309393851613184 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    - (28301429298954240 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (42155275808931840 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (47696814412922880 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (24541099531960320 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    - (1303127437344768 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (2476375063658496 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (2909307767095296 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (3082480848470016 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (1924145348608 : R) * h ^ 62 * a7 ^ 8 * b1
    - (4398046511104 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (6597069766656 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (8796093022208 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (1577799185858560 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (5772436045824000 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (11044594301009920 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (12622393486868480 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (2133052557885440 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (8431055161786368 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (18302470555959296 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (27953983624577024 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (1099511627776000 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (9024791440785408 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (20611444974288896 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (34111248740122624 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (10652068649893888 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (36574154786340864 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    + (4723776830832640 : R) * h ^ 56 * a7 ^ 9 * a0
    + (9308053123891200 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (11039783937638400 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (11732476263137280 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (403709745954816 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (605641928343552 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (659758516273152 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (337996746326016 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (481036337152 : R) * h ^ 54 * a7 ^ 9 * b2
    + (824633720832 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (1099511627776 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (332602267402240 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (1340648271642624 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (2978336481476608 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (4635266144796672 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (426060755763200 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (1797701511413760 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (4242740493680640 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (7267771859599360 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (923589767331840 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (4502500115742720 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (8037429999042560 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (4134163720437760 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    - (1525336160337920 : R) * h ^ 48 * a7 ^ 10 * a1
    - (2314128379084800 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (2530594730803200 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (1297767318159360 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (95887829237760 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (130981470142464 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (137069586284544 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (90194313216 : R) * h ^ 46 * a7 ^ 10 * b3
    - (137438953472 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (64596308131840 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (276973850984448 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (666926816690176 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (1166272599425024 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (39943195852800 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (353561707806720 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (883904269516800 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (1624528430039040 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (452775452344320 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (1711114970726400 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    + (367842474065920 : R) * h ^ 40 * a7 ^ 11 * a2
    + (505023729500160 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (529376194068480 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (20145745428480 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (26140244705280 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (13323793858560 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (15032385536 : R) * h ^ 38 * a7 ^ 11 * b4
    + (11843372318720 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (53092238229504 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (134923176378368 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (252574141775872 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (32792075304960 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (171218871255040 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (331056079175680 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (169135812116480 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    - (77918256496640 : R) * h ^ 32 * a7 ^ 12 * a3
    - (101371965603840 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (51700668825600 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (3919224766464 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (4917603336192 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (864362168320 : R) * h ^ 30 * a7 ^ 12 * b5
    - (9644349063168 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (25509018730496 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (50080392413184 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (15710721933312 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (63183263891456 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    + (15237319229440 : R) * h ^ 24 * a7 ^ 13 * a4
    + (19146662215680 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (721510465536 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (441792331776 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (699005927424 : R) * h ^ 22 * a7 ^ 13 * b6
    + (4588694405120 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (9341218324480 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (5736197259264 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (2815195873280 : R) * h ^ 16 * a7 ^ 14 * a5
    - (1725117235200 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (127306432512 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (330481270784 : R) * h ^ 14 * a7 ^ 14 * b7
    - (1664073334784 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (498030346240 : R) * h ^ 8 * a7 ^ 15 * a6
    + (9055678464 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (119103029248 : R) * h ^ 6 * a7 ^ 15 * b8
    - (35486187520 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Combined integer polynomial of compact-block expansions `0`–`2`. -/
def degreeZeroExpansionGroup0810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1459166279268040704 : R) * h ^ 111 * a6 * a2 * a0 * lambda
    - (729583139634020352 : R) * h ^ 111 * a6 * a1 ^ 2 * lambda
    + (638385247179767808 : R) * h ^ 103 * a7 ^ 2 * a2 * a0 * lambda
    + (319192623589883904 : R) * h ^ 103 * a7 ^ 2 * a1 ^ 2 * lambda
    + (547187354725515264 : R) * h ^ 103 * a7 * a6 * a3 * a0 * lambda
    + (547187354725515264 : R) * h ^ 103 * a7 * a6 * a2 * a1 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 ^ 2 * a4 * a0 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 ^ 2 * a3 * a1 * lambda
    + (775182085861146624 : R) * h ^ 103 * a6 ^ 2 * a2 ^ 2 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 * a5 ^ 2 * a0 * lambda
    + (3100728343444586496 : R) * h ^ 103 * a6 * a5 * a4 * a1 * lambda
    + (3100728343444586496 : R) * h ^ 103 * a6 * a5 * a3 * a2 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 * a4 ^ 2 * a2 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 * a4 * a3 ^ 2 * lambda
    - (239394467692412928 : R) * h ^ 95 * a7 ^ 3 * a3 * a0 * lambda
    - (239394467692412928 : R) * h ^ 95 * a7 ^ 3 * a2 * a1 * lambda
    - (1493365488938385408 : R) * h ^ 95 * a7 ^ 2 * a6 * a4 * a0 * lambda
    - (1493365488938385408 : R) * h ^ 95 * a7 ^ 2 * a6 * a3 * a1 * lambda
    - (746682744469192704 : R) * h ^ 95 * a7 ^ 2 * a6 * a2 ^ 2 * lambda
    - (678284325128503296 : R) * h ^ 95 * a7 ^ 2 * a5 ^ 2 * a0 * lambda
    - (1356568650257006592 : R) * h ^ 95 * a7 ^ 2 * a5 * a4 * a1 * lambda
    - (1356568650257006592 : R) * h ^ 95 * a7 ^ 2 * a5 * a3 * a2 * lambda
    - (678284325128503296 : R) * h ^ 95 * a7 ^ 2 * a4 ^ 2 * a2 * lambda
    - (678284325128503296 : R) * h ^ 95 * a7 ^ 2 * a4 * a3 ^ 2 * lambda
    - (3294523864909873152 : R) * h ^ 95 * a7 * a6 ^ 2 * a5 * a0 * lambda
    - (3294523864909873152 : R) * h ^ 95 * a7 * a6 ^ 2 * a4 * a1 * lambda
    - (3294523864909873152 : R) * h ^ 95 * a7 * a6 ^ 2 * a3 * a2 * lambda
    - (2131750736118153216 : R) * h ^ 95 * a7 * a6 * a5 ^ 2 * a1 * lambda
    - (4263501472236306432 : R) * h ^ 95 * a7 * a6 * a5 * a4 * a2 * lambda
    - (2131750736118153216 : R) * h ^ 95 * a7 * a6 * a5 * a3 ^ 2 * lambda
    - (2131750736118153216 : R) * h ^ 95 * a7 * a6 * a4 ^ 2 * a3 * lambda
    - (403740669719347200 : R) * h ^ 95 * a6 ^ 4 * a0 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a6 ^ 3 * a5 * a1 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a6 ^ 3 * a4 * a2 * lambda
    - (807481339438694400 : R) * h ^ 95 * a6 ^ 3 * a3 ^ 2 * lambda
    - (2422444018316083200 : R) * h ^ 95 * a6 ^ 2 * a5 ^ 2 * a2 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a6 ^ 2 * a5 * a4 * a3 * lambda
    - (807481339438694400 : R) * h ^ 95 * a6 ^ 2 * a4 ^ 3 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a6 * a5 ^ 3 * a3 * lambda
    - (2422444018316083200 : R) * h ^ 95 * a6 * a5 ^ 2 * a4 ^ 2 * lambda
    + (356598009166823424 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (356598009166823424 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (178299004583411712 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (2572065560623841280 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (2572065560623841280 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (2572065560623841280 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (932640947051692032 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (1865281894103384064 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (932640947051692032 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (932640947051692032 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (1941992621350060032 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 3 * a0 * lambda
    + (4953898017456390144 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (4953898017456390144 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (2476949008728195072 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a3 ^ 2 * lambda
    + (3718451568115187712 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (7436903136230375424 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (1239483856038395904 : R) * h ^ 87 * a7 ^ 2 * a6 * a4 ^ 3 * lambda
    + (706546172008857600 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 3 * a3 * lambda
    + (1059819258013286400 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 2 * a4 ^ 2 * lambda
    + (1261689592872960000 : R) * h ^ 87 * a7 * a6 ^ 4 * a1 * lambda
    + (5046758371491840000 : R) * h ^ 87 * a7 * a6 ^ 3 * a5 * a2 * lambda
    + (5046758371491840000 : R) * h ^ 87 * a7 * a6 ^ 3 * a4 * a3 * lambda
    + (7570137557237760000 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 ^ 2 * a3 * lambda
    + (7570137557237760000 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 * a4 ^ 2 * lambda
    + (3835536362333798400 : R) * h ^ 87 * a7 * a6 * a5 ^ 3 * a4 * lambda
    + (333086052518461440 : R) * h ^ 87 * a6 ^ 5 * a2 * lambda
    + (1665430262592307200 : R) * h ^ 87 * a6 ^ 4 * a5 * a3 * lambda
    + (832715131296153600 : R) * h ^ 87 * a6 ^ 4 * a4 ^ 2 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a6 ^ 3 * a5 ^ 2 * a4 * lambda
    + (832715131296153600 : R) * h ^ 87 * a6 ^ 2 * a5 ^ 4 * lambda
    - (494686224255025152 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (494686224255025152 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (494686224255025152 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (1756694950377947136 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (2999333030398525440 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (2999333030398525440 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (1499666515199262720 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (1163151635669581824 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (2326303271339163648 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (387717211889860608 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (2791362055272136704 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (7720026280871067648 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (7720026280871067648 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (6959984470124396544 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (6959984470124396544 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (1678047158521036800 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    - (2778871328302694400 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 4 * a2 * lambda
    - (11115485313210777600 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a5 * a3 * lambda
    - (5557742656605388800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a4 ^ 2 * lambda
    - (15310603209513369600 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (1927230853113446400 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 ^ 4 * lambda
    - (1373979966638653440 : R) * h ^ 79 * a7 * a6 ^ 5 * a3 * lambda
    - (6869899833193267200 : R) * h ^ 79 * a7 * a6 ^ 4 * a5 * a4 * lambda
    - (4579933222128844800 : R) * h ^ 79 * a7 * a6 ^ 3 * a5 ^ 3 * lambda
    - (284511003192852480 : R) * h ^ 79 * a6 ^ 6 * a4 * lambda
    - (853533009578557440 : R) * h ^ 79 * a6 ^ 5 * a5 ^ 2 * lambda
    + (574205138558779392 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (499238511631663104 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (499238511631663104 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (249619255815831552 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (1959282407337099264 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (3575837969325490176 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (3575837969325490176 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (1596021563864383488 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (1596021563864383488 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (4053477468382691328 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (11834537983308988416 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (5917268991654494208 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (10687283636509605888 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (683776617637478400 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (5129951029021900800 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (19838491735936204800 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (9124381424458137600 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (3666548812488376320 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 5 * a4 * lambda
    + (9166372031220940800 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 4 * a5 ^ 2 * lambda
    + (1458118891363368960 : R) * h ^ 71 * a7 * a6 ^ 6 * a5 * lambda
    + (31118390974218240 : R) * h ^ 71 * a6 ^ 8 * lambda
    - (62803687029866496 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (553564105554788352 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (509384560119644160 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (509384560119644160 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (2302012905555492864 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (4446718630985465856 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (2223359315492732928 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (2024068486451429376 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (5670157227940380672 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (16284164298563911680 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (4939709923706535936 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (8371248842774937600 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (16252804412316057600 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (7898758411431444480 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 5 * a5 * lambda
    - (655708952671027200 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 7 * lambda
    + (54691005915463680 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (568619003900067840 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (550032920278990848 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (275016460139495424 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (2726065219452272640 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (5219421244574662656 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (798184141039337472 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (7391262131267567616 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (10659260266211966976 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (12833661039044198400 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (2485071535920906240 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 6 * lambda
    - (51121437989142528 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (599596772301471744 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (576197847146299392 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (3084957704716812288 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (2963969757633576960 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (9360891838287839232 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (3778645223811317760 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    + (49437974091792384 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (613062275476488192 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (295359719239581696 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (3438488253044883456 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (2944030216611299328 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    - (46762373173985280 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (622141631260065792 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (1288297194792321024 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    + (44123108506638336 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (320698863314574336 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    - (42451095870034560 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    + (2321544305392515 : R) * h ^ 7 * a7 ^ 16 * lambda

set_option maxHeartbeats 200000000 in
/-- Combined integer polynomial of compact-block expansions `3`–`5`. -/
def degreeZeroExpansionGroup1810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (648518346341351424 : R) * h ^ 119 * a0 ^ 2 * lambda
    - (162129586585337856 : R) * h ^ 111 * a7 * a1 * a0 * lambda
    - (1459166279268040704 : R) * h ^ 111 * a5 * a3 * a0 * lambda
    - (1459166279268040704 : R) * h ^ 111 * a5 * a2 * a1 * lambda
    - (729583139634020352 : R) * h ^ 111 * a4 ^ 2 * a0 * lambda
    - (1459166279268040704 : R) * h ^ 111 * a4 * a3 * a1 * lambda
    - (729583139634020352 : R) * h ^ 111 * a4 * a2 ^ 2 * lambda
    - (729583139634020352 : R) * h ^ 111 * a3 ^ 2 * a2 * lambda
    + (20266198323167232 : R) * h ^ 103 * a7 ^ 2 * a2 * a0 * lambda
    + (10133099161583616 : R) * h ^ 103 * a7 ^ 2 * a1 ^ 2 * lambda
    + (1094374709451030528 : R) * h ^ 103 * a7 * a6 * a3 * a0 * lambda
    + (1094374709451030528 : R) * h ^ 103 * a7 * a6 * a2 * a1 * lambda
    + (1641562064176545792 : R) * h ^ 103 * a7 * a5 * a4 * a0 * lambda
    + (1641562064176545792 : R) * h ^ 103 * a7 * a5 * a3 * a1 * lambda
    + (820781032088272896 : R) * h ^ 103 * a7 * a5 * a2 ^ 2 * lambda
    + (820781032088272896 : R) * h ^ 103 * a7 * a4 ^ 2 * a1 * lambda
    + (1641562064176545792 : R) * h ^ 103 * a7 * a4 * a3 * a2 * lambda
    + (273593677362757632 : R) * h ^ 103 * a7 * a3 ^ 3 * lambda
    + (516788057240764416 : R) * h ^ 103 * a5 ^ 3 * a1 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a5 ^ 2 * a4 * a2 * lambda
    + (775182085861146624 : R) * h ^ 103 * a5 ^ 2 * a3 ^ 2 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a5 * a4 ^ 2 * a3 * lambda
    + (129197014310191104 : R) * h ^ 103 * a4 ^ 4 * lambda
    - (321725898380279808 : R) * h ^ 95 * a7 ^ 3 * a3 * a0 * lambda
    - (321725898380279808 : R) * h ^ 95 * a7 ^ 3 * a2 * a1 * lambda
    - (889179451428962304 : R) * h ^ 95 * a7 ^ 2 * a6 * a4 * a0 * lambda
    - (889179451428962304 : R) * h ^ 95 * a7 ^ 2 * a6 * a3 * a1 * lambda
    - (444589725714481152 : R) * h ^ 95 * a7 ^ 2 * a6 * a2 ^ 2 * lambda
    - (512988145055170560 : R) * h ^ 95 * a7 ^ 2 * a5 ^ 2 * a0 * lambda
    - (1025976290110341120 : R) * h ^ 95 * a7 ^ 2 * a5 * a4 * a1 * lambda
    - (1025976290110341120 : R) * h ^ 95 * a7 ^ 2 * a5 * a3 * a2 * lambda
    - (512988145055170560 : R) * h ^ 95 * a7 ^ 2 * a4 ^ 2 * a2 * lambda
    - (512988145055170560 : R) * h ^ 95 * a7 ^ 2 * a4 * a3 ^ 2 * lambda
    - (1162773128791719936 : R) * h ^ 95 * a7 * a6 * a5 ^ 2 * a1 * lambda
    - (2325546257583439872 : R) * h ^ 95 * a7 * a6 * a5 * a4 * a2 * lambda
    - (1162773128791719936 : R) * h ^ 95 * a7 * a6 * a5 * a3 ^ 2 * lambda
    - (1162773128791719936 : R) * h ^ 95 * a7 * a6 * a4 ^ 2 * a3 * lambda
    - (1098174621636624384 : R) * h ^ 95 * a7 * a5 ^ 3 * a2 * lambda
    - (3294523864909873152 : R) * h ^ 95 * a7 * a5 ^ 2 * a4 * a3 * lambda
    - (1098174621636624384 : R) * h ^ 95 * a7 * a5 * a4 ^ 3 * lambda
    - (403740669719347200 : R) * h ^ 95 * a5 ^ 4 * a4 * lambda
    - (1480382455637606400 : R) * h ^ 88 * a6 ^ 5 * a1
    + (234723742297620480 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (234723742297620480 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (117361871148810240 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (441739791575285760 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (441739791575285760 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (441739791575285760 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (574261729047871488 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (1148523458095742976 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (574261729047871488 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (574261729047871488 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (872079846593789952 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (872079846593789952 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (436039923296894976 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a3 ^ 2 * lambda
    + (2107526295934992384 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (4215052591869984768 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (702508765311664128 : R) * h ^ 87 * a7 ^ 2 * a6 * a4 ^ 3 * lambda
    + (1235446449341202432 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 3 * a3 * lambda
    + (1853169674011803648 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 2 * a4 ^ 2 * lambda
    + (1211222009158041600 : R) * h ^ 87 * a7 * a6 * a5 ^ 3 * a4 * lambda
    + (252337918574592000 : R) * h ^ 87 * a7 * a5 ^ 5 * lambda
    + (107664178591825920 : R) * h ^ 86 * a6 ^ 5 * b3
    + (3238336621707264000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 4 * a1
    + (370095613909401600 : R) * h ^ 80 * a7 * a6 ^ 5 * a2
    + (1264493347523788800 : R) * h ^ 80 * a6 ^ 6 * a3
    + (7586960085142732800 : R) * h ^ 80 * a6 ^ 5 * a5 * a4
    + (6322466737618944000 : R) * h ^ 80 * a6 ^ 4 * a5 ^ 3
    - (106644931312877568 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (106644931312877568 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (106644931312877568 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (82826210920366080 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (679709292198100992 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (679709292198100992 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (339854646099050496 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (676369525628731392 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (1352739051257462784 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (225456508542910464 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (218019961648447488 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (1308119769890684928 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (1308119769890684928 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (2068161580637356032 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (2068161580637356032 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (1331334858399547392 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    - (1362624760302796800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (851640475189248000 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 ^ 4 * lambda
    - (333086052518461440 : R) * h ^ 79 * a7 * a6 ^ 5 * a3 * lambda
    - (1665430262592307200 : R) * h ^ 79 * a7 * a6 ^ 4 * a5 * a4 * lambda
    - (235515390669619200 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 4 * b3
    - (53832089295912960 : R) * h ^ 78 * a7 * a6 ^ 5 * b4
    - (123365204636467200 : R) * h ^ 78 * a6 ^ 6 * b5
    - (888229473382563840 : R) * h ^ 78 * a6 ^ 5 * a5 * b6
    - (1036267718946324480 : R) * h ^ 78 * a6 ^ 5 * a4 * b7
    - (1184305964510085120 : R) * h ^ 78 * a6 ^ 5 * a3 * b8
    - (2590669297365811200 : R) * h ^ 78 * a6 ^ 4 * a5 ^ 2 * b7
    - (5921529822550425600 : R) * h ^ 78 * a6 ^ 4 * a5 * a4 * b8
    - (2833544543993856000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (809584155426816000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 4 * a2
    - (2555972833561804800 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 5 * a3
    - (12432899529768960000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 4 * a5 * a4
    - (11064316790833152000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 3 * a5 ^ 3
    - (6322466737618944000 : R) * h ^ 72 * a7 * a6 ^ 6 * a4
    - (18967400212856832000 : R) * h ^ 72 * a7 * a6 ^ 5 * a5 ^ 2
    - (1106431679083315200 : R) * h ^ 72 * a6 ^ 7 * a5
    + (37488261265883136 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (112454888192999424 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (112454888192999424 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (56227444096499712 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (218487528968159232 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (779701903285026816 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (779701903285026816 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (581748372440875008 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (581748372440875008 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (258898704457531392 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (1102590535211679744 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (551295267605839872 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (2249844882011062272 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (394317425572577280 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (728625739884134400 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (3595815339687936000 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (1135520633585664000 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (1561340871180288000 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 5 * a4 * lambda
    + (1405206784062259200 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 4 * a5 ^ 2 * lambda
    + (284511003192852480 : R) * h ^ 71 * a7 * a6 ^ 6 * a5 * lambda
    + (206075966835916800 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (117757695334809600 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 4 * b4
    + (340656190075699200 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 5 * b5
    + (1943001973024358400 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a5 * b6
    + (2266835635195084800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a4 * b7
    + (2590669297365811200 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a3 * b8
    + (4533671270390169600 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2 * b7
    + (10362677189463244800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 * a4 * b8
    + (758696008514273280 : R) * h ^ 70 * a7 * a6 ^ 6 * b6
    + (5310872059599912960 : R) * h ^ 70 * a7 * a6 ^ 5 * a5 * b7
    + (6069568068114186240 : R) * h ^ 70 * a7 * a6 ^ 5 * a4 * b8
    + (6291625436459827200 : R) * h ^ 70 * a7 * a6 ^ 4 * a5 ^ 2 * b8
    + (126449334752378880 : R) * h ^ 70 * a6 ^ 7 * b7
    + (1011594678019031040 : R) * h ^ 70 * a6 ^ 6 * a5 * b8
    + (1239675737997312000 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (708386135998464000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (1960711626424320000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (7235658389127168000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (7260957893984256000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    + (11753427113607168000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 5 * a4
    + (35600017548902400000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 4 * a5 ^ 2
    + (18878490524359065600 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 6 * a5
    + (829823759312486400 : R) * h ^ 64 * a7 * a6 ^ 8
    - (4100278575955968 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (67340053499609088 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (111519598934753280 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (111519598934753280 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (219834568151138304 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (596976316427796480 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (298488158213898240 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (497778987255201792 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (822353505514684416 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (3193367901801283584 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (915253287349911552 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (3361022792014233600 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (3204297287899545600 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (2643870541865287680 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 5 * a5 * lambda
    - (231165190094192640 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 7 * lambda
    - (90158235490713600 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (103037983417958400 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (390992347791360000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (1700126726396313600 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (1983481180795699200 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (2266835635195084800 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (2975221771193548800 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (6800506905585254400 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (1898632555674992640 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 5 * b6
    - (11050823721576038400 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a5 * b7
    - (12629512824658329600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    - (11010344513804697600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    - (2710757613754122240 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 6 * b7
    - (11926331158230466560 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 5 * a5 * b8
    - (885145343266652160 : R) * h ^ 62 * a7 * a6 ^ 7 * b8
    - (271179067686912000 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    - (309918934499328000 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    - (656732980248576000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (1571731739246592000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (2117779385745408000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (8013618163482624000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (25995241240657920000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    - (35771647582745395200 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    - (6240966189829324800 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 7
    + (6603897959350272 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (60648150855057408 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (79234234476134400 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (39617117238067200 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (423967884771852288 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (1080644963873587200 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (158851213352239104 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (2919739957041954816 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (2416439657257500672 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (4927205889854668800 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (1249940108539330560 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 6 * lambda
    + (19722114013593600 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (45079117745356800 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (238811992817664000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (743805442798387200 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (867773016598118400 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (991740590397849600 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (867773016598118400 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (1983481180795699200 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (1974971347343769600 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (9173600461180108800 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (10484114812777267200 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (7225538587184332800 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (6045224687401697280 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (21909371206238208000 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    + (5692340403311738880 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 6 * b8
    + (23728168422604800 : R) * h ^ 48 * a7 ^ 10 * a1
    + (67794766921728000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    + (55688558542848000 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (4842483351552000 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    + (231632120315904000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (2115934630182912000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (9117704367636480000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (28282046354817024000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    + (11409959981521305600 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 6
    - (5471810648801280 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (98347535667560448 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (121746460822732800 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (1238386357139668992 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (731788461861765120 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (3933490541676724224 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (2200492458167500800 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (1725684976189440 : R) * h ^ 46 * a7 ^ 10 * b3
    - (9861057006796800 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (81881991217152000 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (162707440612147200 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (189825347380838400 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (216943254149529600 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (94912673690419200 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (216943254149529600 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (1092766113202176000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (3796506947616768000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (4338865082990592000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (2107448754595430400 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (5842693047032217600 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (17207879886962688000 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (10472408041893396480 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    - (5932042105651200 : R) * h ^ 40 * a7 ^ 11 * a2
    + (18219843610214400 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (30931362408038400 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (58109800218624000 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    - (1501169838981120000 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (11223449605767168000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (9483857265741004800 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (8494987327045632 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (255934781064216576 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (78123518801215488 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (1569451228142764032 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (1896427183769911296 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (862842488094720 : R) * h ^ 38 * a7 ^ 11 * b4
    + (14945664525926400 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (14236901053562880 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (16609717895823360 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (18982534738083840 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (339105902336409600 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (783029557945958400 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (894890923366809600 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (230502207533875200 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (3031622028047155200 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (6855019432457011200 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (9223626877933977600 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (3367669737062400 : R) * h ^ 32 * a7 ^ 12 * a3
    - (126585541361664000 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    + (88186161659904000 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    + (2203712027158118400 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (4104304160538624000 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (20739868661514240 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (309868834183446528 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (907882046040047616 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (1134727751270400 : R) * h ^ 30 * a7 ^ 12 * b5
    - (55938386661212160 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (64362656846315520 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (73557322110074880 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (884199765662760960 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (1368437370315079680 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (4495064519462092800 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (16606628290560000 : R) * h ^ 24 * a7 ^ 13 * a4
    - (165441189554995200 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    - (881514918341836800 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (24211331110600704 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (247177801178578944 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (3830548780154880 : R) * h ^ 22 * a7 ^ 13 * b6
    + (137047305906094080 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (108976556849233920 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (1246370196089733120 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (1347598920729600 : R) * h ^ 16 * a7 ^ 14 * a5
    + (52719189581721600 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (35902940017996800 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (8804865917890560 : R) * h ^ 14 * a7 ^ 14 * b7
    - (184609812823080960 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (11223977780332800 : R) * h ^ 8 * a7 ^ 15 * a6
    + (2163057405833520 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (11355896809205760 : R) * h ^ 6 * a7 ^ 15 * b8
    - (1517071202690400 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Combined integer polynomial of compact-block expansions `6`–`8`. -/
def degreeZeroExpansionGroup2810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (7177611906121728000 : R) * h ^ 96 * a6 ^ 3 * a5 * a0
    + (7177611906121728000 : R) * h ^ 96 * a6 ^ 3 * a4 * a1
    + (7177611906121728000 : R) * h ^ 96 * a6 ^ 3 * a3 * a2
    - (57420895248973824 : R) * h ^ 94 * a6 ^ 4 * b1
    - (459367161991790592 : R) * h ^ 94 * a6 ^ 3 * a5 * b2
    - (689050742987685888 : R) * h ^ 94 * a6 ^ 3 * a4 * b3
    - (918734323983581184 : R) * h ^ 94 * a6 ^ 3 * a3 * b4
    - (1148417904979476480 : R) * h ^ 94 * a6 ^ 3 * a2 * b5
    - (1378101485975371776 : R) * h ^ 94 * a6 ^ 3 * a1 * b6
    - (1607785066971267072 : R) * h ^ 94 * a6 ^ 3 * a0 * b7
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a5 * a0
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 ^ 4 * a0
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 ^ 3 * a5 * a1
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 ^ 3 * a4 * a2
    - (2691604464795648000 : R) * h ^ 88 * a7 * a6 ^ 3 * a3 ^ 2
    - (7401912278188032000 : R) * h ^ 88 * a6 ^ 4 * a5 * a2
    - (7401912278188032000 : R) * h ^ 88 * a6 ^ 4 * a4 * a3
    - (14803824556376064000 : R) * h ^ 88 * a6 ^ 3 * a5 ^ 2 * a3
    - (14803824556376064000 : R) * h ^ 88 * a6 ^ 3 * a5 * a4 ^ 2
    - (14803824556376064000 : R) * h ^ 88 * a6 ^ 2 * a5 ^ 3 * a4
    + (226094775042834432 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 3 * a0 * lambda
    + (403740669719347200 : R) * h ^ 87 * a7 * a6 ^ 4 * a1 * lambda
    + (1614962678877388800 : R) * h ^ 87 * a7 * a6 ^ 3 * a5 * a2 * lambda
    + (1614962678877388800 : R) * h ^ 87 * a7 * a6 ^ 3 * a4 * a3 * lambda
    + (100486566685704192 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 3 * b1
    + (602919400114225152 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a5 * b2
    + (904379100171337728 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (1205838800228450304 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a3 * b4
    + (1507298500285562880 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a2 * b5
    + (1808758200342675456 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a1 * b6
    + (2110217900399788032 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a0 * b7
    + (358880595306086400 : R) * h ^ 86 * a7 * a6 ^ 4 * b2
    + (602919400114225152 : R) * h ^ 86 * a7 * a6 ^ 3 * a5 * b3
    + (803892533485633536 : R) * h ^ 86 * a7 * a6 ^ 3 * a4 * b4
    + (1004865666857041920 : R) * h ^ 86 * a7 * a6 ^ 3 * a3 * b5
    + (1205838800228450304 : R) * h ^ 86 * a7 * a6 ^ 3 * a2 * b6
    + (1406811933599858688 : R) * h ^ 86 * a7 * a6 ^ 3 * a1 * b7
    + (1607785066971267072 : R) * h ^ 86 * a7 * a6 ^ 3 * a0 * b8
    + (717761190612172800 : R) * h ^ 86 * a6 ^ 4 * a5 * b4
    + (897201488265216000 : R) * h ^ 86 * a6 ^ 4 * a4 * b5
    + (1076641785918259200 : R) * h ^ 86 * a6 ^ 4 * a3 * b6
    + (1256082083571302400 : R) * h ^ 86 * a6 ^ 4 * a2 * b7
    + (1435522381224345600 : R) * h ^ 86 * a6 ^ 4 * a1 * b8
    + (1794402976530432000 : R) * h ^ 86 * a6 ^ 3 * a5 ^ 2 * b5
    + (4306567143673036800 : R) * h ^ 86 * a6 ^ 3 * a5 * a4 * b6
    + (5024328334285209600 : R) * h ^ 86 * a6 ^ 3 * a5 * a3 * b7
    + (5742089524897382400 : R) * h ^ 86 * a6 ^ 3 * a5 * a2 * b8
    + (2512164167142604800 : R) * h ^ 86 * a6 ^ 3 * a4 ^ 2 * b7
    + (5742089524897382400 : R) * h ^ 86 * a6 ^ 3 * a4 * a3 * b8
    + (4121519336718336000 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    + (4121519336718336000 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    + (4121519336718336000 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    + (7881915074409922560 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 3 * a0
    + (7065461720088576000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    + (7065461720088576000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (3532730860044288000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    + (1345802232397824000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 4 * a1
    + (11271093696331776000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a5 * a2
    + (11271093696331776000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a4 * a3
    + (19430019730243584000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a3
    + (19430019730243584000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 * a4 ^ 2
    + (12953346486829056000 : R) * h ^ 80 * a7 ^ 2 * a6 * a5 ^ 3 * a4
    + (5551434208641024000 : R) * h ^ 80 * a7 * a6 ^ 5 * a2
    + (29607649112752128000 : R) * h ^ 80 * a7 * a6 ^ 4 * a5 * a3
    + (14803824556376064000 : R) * h ^ 80 * a7 * a6 ^ 4 * a4 ^ 2
    + (59215298225504256000 : R) * h ^ 80 * a7 * a6 ^ 3 * a5 ^ 2 * a4
    + (9252390347735040000 : R) * h ^ 80 * a7 * a6 ^ 2 * a5 ^ 4
    - (296749392243720192 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (791331712649920512 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (2119638516026572800 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (2119638516026572800 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (1488793719590092800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 4 * a2 * lambda
    - (2321508850886246400 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a5 * a3 * lambda
    - (1160754425443123200 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a4 ^ 2 * lambda
    - (1110286841728204800 : R) * h ^ 79 * a7 * a6 ^ 3 * a5 ^ 3 * lambda
    - (65944309387493376 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (263777237549973504 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (395665856324960256 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (527554475099947008 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (659443093874933760 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (791331712649920512 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (923220331424907264 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (577797758442799104 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 3 * b2
    - (791331712649920512 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (1318886187749867520 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (1582663425299841024 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (1846440662849814528 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (2110217900399788032 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (293384886662725632 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 4 * b3
    - (1658028350314119168 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a5 * b4
    - (2072535437892648960 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a4 * b5
    - (2487042525471178752 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a3 * b6
    - (2901549613049708544 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a2 * b7
    - (3316056700628238336 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a1 * b8
    - (2355153906696192000 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b5
    - (5652369376070860800 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b6
    - (6594430938749337600 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * b7
    - (7536492501427814400 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a2 * b8
    - (3297215469374668800 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * b7
    - (7536492501427814400 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 * a3 * b8
    - (538320892959129600 : R) * h ^ 78 * a7 * a6 ^ 5 * b4
    - (3700956139094016000 : R) * h ^ 78 * a7 * a6 ^ 4 * a5 * b5
    - (4441147366912819200 : R) * h ^ 78 * a7 * a6 ^ 4 * a4 * b6
    - (5181338594731622400 : R) * h ^ 78 * a7 * a6 ^ 4 * a3 * b7
    - (5921529822550425600 : R) * h ^ 78 * a7 * a6 ^ 4 * a2 * b8
    - (4037406697193472000 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 ^ 2 * b6
    - (9420615626784768000 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 * a4 * b7
    - (10766417859182592000 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 * a3 * b8
    - (5383208929591296000 : R) * h ^ 78 * a7 * a6 ^ 3 * a4 ^ 2 * b8
    - (3947686548366950400 : R) * h ^ 78 * a6 ^ 3 * a5 ^ 3 * b8
    - (601054903271424000 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    - (601054903271424000 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    - (601054903271424000 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    - (4162734530085519360 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    - (3091139502538752000 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (3091139502538752000 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    - (1545569751269376000 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    - (1582859688125399040 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (6292676844453888000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (6292676844453888000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (8500633631981568000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (8500633631981568000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (2833544543993856000 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    - (8250048060063744000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 4 * a2
    - (42967540023951360000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    - (21483770011975680000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    - (72862573988413440000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    - (8095841554268160000 : R) * h ^ 72 * a7 ^ 3 * a6 * a5 ^ 4
    - (12143762331402240000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 5 * a3
    - (61065776295051264000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 4 * a5 * a4
    - (29607649112752128000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 3 * a5 ^ 3
    + (129827859106627584 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (574951947472207872 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (927341850761625600 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (927341850761625600 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (2455247947730780160 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (3046980366788198400 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (1523490183394099200 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (1491947943572275200 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (1879917493380710400 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (1457251479768268800 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (2498145393888460800 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 4 * a5 ^ 2 * lambda
    + (19233756904685568 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (38467513809371136 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (57701270714056704 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (76935027618742272 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (96168784523427840 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (115402541428113408 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (134636298332798976 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (346207624284340224 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (346207624284340224 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (461610165712453632 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (577012707140567040 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (692415248568680448 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (807817789996793856 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (923220331424907264 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (459255011805757440 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (1351858342443614208 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (1689822928054517760 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (2027787513665421312 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (2365752099276324864 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (2703716684887228416 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (1030379834179584000 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (2472911602031001600 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (2885063535702835200 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (3297215469374668800 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (1442531767851417600 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (3297215469374668800 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (1248455870921048064 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 4 * b4
    + (6272559904834191360 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (7527071885801029632 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (8781583866767867904 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (10036095847734706176 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (5299096290066432000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b6
    + (12364558010155008000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (14130923440177152000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (7065461720088576000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (1556083831209984000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 5 * b5
    + (5803772127215616000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a5 * b6
    + (6771067481751552000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a4 * b7
    + (7738362836287488000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a3 * b8
    + (4710307813392384000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2 * b7
    + (10766417859182592000 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 * a4 * b8
    + (5181338594731622400 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a5 ^ 3 * b8
    + (8882294733825638400 : R) * h ^ 70 * a7 * a6 ^ 4 * a5 ^ 2 * b8
    + (919614002005278720 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    + (450791177453568000 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    + (450791177453568000 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    + (225395588726784000 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    + (531933589395210240 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (1513370381451264000 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    + (1513370381451264000 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (1239675737997312000 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    + (1239675737997312000 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (3975426195943587840 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (22392361753509888000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (11196180876754944000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (29752217711935488000 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (1770965339996160000 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    + (19391577625460736000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (89055571356942336000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (35065113731923968000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    + (17290404462329856000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 5 * a4
    + (30764197906219008000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 4 * a5 ^ 2
    - (18933229453049856 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (183922800401055744 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (135237353236070400 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (135237353236070400 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (1512726394054901760 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (1333053910469836800 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (666526955234918400 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (2391879587928735744 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (2467391710062182400 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (637547522398617600 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (977612295477657600 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (4569287716188979200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (1873609045416345600 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 5 * a5 * lambda
    - (2103692161449984 : R) * h ^ 62 * a7 ^ 8 * b1
    - (91360345297256448 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (50488611874799616 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (67318149166399488 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (84147686457999360 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (100977223749599232 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (117806761041199104 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (134636298332798976 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (265837997218332672 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (471227044164796416 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (589033805205995520 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (706840566247194624 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (824647327288393728 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (942454088329592832 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (150263725817856000 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (360632941962854400 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (420738432289996800 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (480843922617139200 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (210369216144998400 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (480843922617139200 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (1122623362191851520 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (3982418059104092160 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (4778901670924910592 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (5575385282745729024 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (6371868894566547456 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (2318354626904064000 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (5409494129442816000 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (6182279005077504000 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (3091139502538752000 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (3073142902373744640 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (9417671684401397760 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (10987283631801630720 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (12556895579201863680 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (6182279005077504000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (14130923440177152000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (2266835635195084800 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    - (1839963989606400000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 5 * b6
    - (5458559835832320000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a5 * b7
    - (6238354098094080000 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    - (18061787460639129600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    - (6661721050369228800 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 5 * a5 * b8
    - (68369995247124480 : R) * h ^ 56 * a7 ^ 9 * a0
    - (7325356633620480 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    - (130306824732672000 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    - (130306824732672000 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (391866330686423040 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    - (4837955315171328000 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    - (2418977657585664000 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    - (4028946148491264000 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    - (11416240569911869440 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (47286499544137728000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (13680707251470336000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (28672060280537088000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (43366308410032128000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    - (11896188605300736000 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    + (21891546555088896 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (412473927370014720 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (194403695276851200 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (97201847638425600 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (1425932992710180864 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (1079483873152204800 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (92975680349798400 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (1543941383138574336 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (3128226276704256000 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (4054828856220057600 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (468402261354086400 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 6 * lambda
    + (8940691686162432 : R) * h ^ 54 * a7 ^ 9 * b2
    + (67167885440581632 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (59955226601324544 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (74944033251655680 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (89932839901986816 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (104921646552317952 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (119910453202649088 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (490460801069481984 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (1122470031859384320 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (1346964038231261184 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (1571458044603138048 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (1795952050975014912 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (338093383090176000 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (788884560543744000 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (901582354907136000 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (450791177453568000 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (2407408884001013760 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (5695424533427650560 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (6644661955665592320 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (7593899377903534080 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (2704747064721408000 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (6182279005077504000 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (330580196799283200 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (3483590678921871360 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (8697178585351323648 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (9939632668972941312 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (13505335683710976000 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (1425972091944960000 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (16398810483366297600 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    + (1665430262592307200 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 6 * b8
    - (15366813835591680 : R) * h ^ 48 * a7 ^ 10 * a1
    - (193358892808273920 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    + (343963059879936000 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    + (171981529939968000 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    + (2883015857028464640 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (10692957912956928000 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    + (1752978973261824000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (18221085354885120000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (22168619257430016000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (18659083032723456000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    + (1316026029441024000 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 6
    - (41971123885178880 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (373973543370620928 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (157424731501363200 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (903696444781756416 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (950208434484019200 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (3455443994073366528 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (1127348606022451200 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (6212465914281984 : R) * h ^ 46 * a7 ^ 10 * b3
    - (104095196060319744 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (118497035031674880 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (142196442038009856 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (165895849044344832 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (189595256050679808 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (933479855633203200 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (1519729756990341120 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (1773018049822064640 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (2026306342653788160 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (394442280271872000 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (901582354907136000 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (2609956062756864000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (5146232081809932288 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (5881408093497065472 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (4420973476026777600 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (2634942280888221696 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (15427214870134652928 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (4493717766615859200 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    + (39968096680673280 : R) * h ^ 40 * a7 ^ 11 * a2
    - (238124716554977280 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    - (847544642961408000 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    - (5446760587591680000 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    - (4800599015030784000 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (11031672117044183040 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (2083451188543488000 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (36317964798001152 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (231636229089656832 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (108064418247475200 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (1447517333558919168 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (1110549410082717696 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (8562684500901888 : R) * h ^ 38 * a7 ^ 11 * b4
    + (178752202116956160 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (150750908991406080 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (175876060489973760 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (201001211988541440 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (965671319356047360 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (1337274375786725376 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (1528313572327686144 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (536253671512473600 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (1920710449922310144 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (6993751423548653568 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (4837909808919085056 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (7440571969044480 : R) * h ^ 32 * a7 ^ 12 * a3
    + (739760082518016000 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    + (361466619494400000 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    + (2972830025766666240 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (1176171374318714880 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (21841567174361088 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (297395203432513536 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (572564557135872000 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (13479987888783360 : R) * h ^ 30 * a7 ^ 12 * b5
    - (176095649291304960 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (128358605635190784 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (146695549297360896 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (688978311732264960 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (1533591585697038336 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (2677634260977844224 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    - (33636859232256000 : R) * h ^ 24 * a7 ^ 13 * a4
    - (337532446543380480 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    - (234618104540037120 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (23883050506420224 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (162730502349520896 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (12630283388190720 : R) * h ^ 22 * a7 ^ 13 * b6
    + (121338724407312384 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (130161330119245824 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (806178357824716800 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    + (9523182661816320 : R) * h ^ 16 * a7 ^ 14 * a5
    - (20358958181990400 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (24139296720838656 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (8373062987218944 : R) * h ^ 14 * a7 ^ 14 * b7
    - (125367065245384704 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (13652215021562880 : R) * h ^ 8 * a7 ^ 15 * a6
    + (1458480185995392 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (7871283005128704 : R) * h ^ 6 * a7 ^ 15 * b8
    - (1353804698225280 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Combined integer polynomial of compact-block expansions `9`–`11`. -/
def degreeZeroExpansionGroup3810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (6890507429876858880 : R) * h ^ 104 * a6 ^ 2 * a3 * a0
    - (6890507429876858880 : R) * h ^ 104 * a6 ^ 2 * a2 * a1
    + (324259173170675712 : R) * h ^ 102 * a6 ^ 2 * a4 * b1
    + (648518346341351424 : R) * h ^ 102 * a6 ^ 2 * a3 * b2
    + (972777519512027136 : R) * h ^ 102 * a6 ^ 2 * a2 * b3
    + (1297036692682702848 : R) * h ^ 102 * a6 ^ 2 * a1 * b4
    + (1621295865853378560 : R) * h ^ 102 * a6 ^ 2 * a0 * b5
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a6 * a3 * a0
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a6 * a2 * a1
    + (3445253714938429440 : R) * h ^ 96 * a7 * a6 ^ 2 * a4 * a0
    + (3445253714938429440 : R) * h ^ 96 * a7 * a6 ^ 2 * a3 * a1
    + (1722626857469214720 : R) * h ^ 96 * a7 * a6 ^ 2 * a2 ^ 2
    + (10766417859182592000 : R) * h ^ 96 * a6 ^ 2 * a5 ^ 2 * a1
    + (21532835718365184000 : R) * h ^ 96 * a6 ^ 2 * a5 * a4 * a2
    + (10766417859182592000 : R) * h ^ 96 * a6 ^ 2 * a5 * a3 ^ 2
    + (10766417859182592000 : R) * h ^ 96 * a6 ^ 2 * a4 ^ 2 * a3
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 ^ 2 * a5 * a0 * lambda
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 ^ 2 * a4 * a1 * lambda
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 ^ 2 * a3 * a2 * lambda
    - (283726776524341248 : R) * h ^ 94 * a7 ^ 2 * a6 * a4 * b1
    - (567453553048682496 : R) * h ^ 94 * a7 ^ 2 * a6 * a3 * b2
    - (851180329573023744 : R) * h ^ 94 * a7 ^ 2 * a6 * a2 * b3
    - (1134907106097364992 : R) * h ^ 94 * a7 ^ 2 * a6 * a1 * b4
    - (1418633882621706240 : R) * h ^ 94 * a7 ^ 2 * a6 * a0 * b5
    - (202661983231672320 : R) * h ^ 94 * a7 * a6 ^ 2 * a5 * b1
    - (405323966463344640 : R) * h ^ 94 * a7 * a6 ^ 2 * a4 * b2
    - (607985949695016960 : R) * h ^ 94 * a7 * a6 ^ 2 * a3 * b3
    - (810647932926689280 : R) * h ^ 94 * a7 * a6 ^ 2 * a2 * b4
    - (1013309916158361600 : R) * h ^ 94 * a7 * a6 ^ 2 * a1 * b5
    - (1215971899390033920 : R) * h ^ 94 * a7 * a6 ^ 2 * a0 * b6
    - (1033576114481528832 : R) * h ^ 94 * a6 ^ 2 * a5 ^ 2 * b3
    - (2756202971950743552 : R) * h ^ 94 * a6 ^ 2 * a5 * a4 * b4
    - (3445253714938429440 : R) * h ^ 94 * a6 ^ 2 * a5 * a3 * b5
    - (4134304457926115328 : R) * h ^ 94 * a6 ^ 2 * a5 * a2 * b6
    - (4823355200913801216 : R) * h ^ 94 * a6 ^ 2 * a5 * a1 * b7
    - (5512405943901487104 : R) * h ^ 94 * a6 ^ 2 * a5 * a0 * b8
    - (1722626857469214720 : R) * h ^ 94 * a6 ^ 2 * a4 ^ 2 * b5
    - (4134304457926115328 : R) * h ^ 94 * a6 ^ 2 * a4 * a3 * b6
    - (4823355200913801216 : R) * h ^ 94 * a6 ^ 2 * a4 * a2 * b7
    - (5512405943901487104 : R) * h ^ 94 * a6 ^ 2 * a4 * a1 * b8
    - (2411677600456900608 : R) * h ^ 94 * a6 ^ 2 * a3 ^ 2 * b7
    - (5512405943901487104 : R) * h ^ 94 * a6 ^ 2 * a3 * a2 * b8
    - (1318886187749867520 : R) * h ^ 88 * a7 ^ 4 * a3 * a0
    - (1318886187749867520 : R) * h ^ 88 * a7 ^ 4 * a2 * a1
    - (3014597000571125760 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    - (3014597000571125760 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    - (1507298500285562880 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    + (2799268643387473920 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a5 * a0
    + (2799268643387473920 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    + (2799268643387473920 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 ^ 2 * a1
    - (18841231253569536000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a6 * a4 ^ 2 * a3
    - (16149626788773888000 : R) * h ^ 88 * a7 * a6 ^ 3 * a5 * a1
    - (16149626788773888000 : R) * h ^ 88 * a7 * a6 ^ 3 * a4 * a2
    - (8074813394386944000 : R) * h ^ 88 * a7 * a6 ^ 3 * a3 ^ 2
    - (16149626788773888000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 ^ 2 * a2
    - (32299253577547776000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 * a4 * a3
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 ^ 2 * a4 ^ 3
    + (1356568650257006592 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (1356568650257006592 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (1356568650257006592 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (1162773128791719936 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 3 * a0 * lambda
    + (1841057453920223232 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (1841057453920223232 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (920528726960111616 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a3 ^ 2 * lambda
    + (2422444018316083200 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 ^ 2 * a3 * lambda
    + (2422444018316083200 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 * a4 ^ 2 * lambda
    + (62065232364699648 : R) * h ^ 86 * a7 ^ 4 * a4 * b1
    + (124130464729399296 : R) * h ^ 86 * a7 ^ 4 * a3 * b2
    + (186195697094098944 : R) * h ^ 86 * a7 ^ 4 * a2 * b3
    + (248260929458798592 : R) * h ^ 86 * a7 ^ 4 * a1 * b4
    + (310326161823498240 : R) * h ^ 86 * a7 ^ 4 * a0 * b5
    + (177329235327713280 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (354658470655426560 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (531987705983139840 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (709316941310853120 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (886646176638566400 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6
    + (75998243711877120 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 3 * b1
    + (151996487423754240 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a5 * b2
    + (227994731135631360 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (303992974847508480 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a3 * b4
    + (379991218559385600 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a2 * b5
    + (455989462271262720 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a1 * b6
    + (531987705983139840 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a0 * b7
    + (904379100171337728 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 ^ 2 * b3
    + (2411677600456900608 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a4 * b4
    + (3014597000571125760 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a3 * b5
    + (3617516400685350912 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a2 * b6
    + (4220435800799576064 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a1 * b7
    + (4823355200913801216 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a0 * b8
    + (1507298500285562880 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 ^ 2 * b5
    + (3617516400685350912 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a3 * b6
    + (4220435800799576064 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a2 * b7
    + (4823355200913801216 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a1 * b8
    + (2110217900399788032 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 ^ 2 * b7
    + (4823355200913801216 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 * a2 * b8
    + (1550364171722293248 : R) * h ^ 86 * a7 * a6 ^ 3 * a5 * b3
    + (2067152228963057664 : R) * h ^ 86 * a7 * a6 ^ 3 * a4 * b4
    + (2583940286203822080 : R) * h ^ 86 * a7 * a6 ^ 3 * a3 * b5
    + (3100728343444586496 : R) * h ^ 86 * a7 * a6 ^ 3 * a2 * b6
    + (3617516400685350912 : R) * h ^ 86 * a7 * a6 ^ 3 * a1 * b7
    + (4134304457926115328 : R) * h ^ 86 * a7 * a6 ^ 3 * a0 * b8
    + (2239414914709979136 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 ^ 2 * b4
    + (5598537286774947840 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a4 * b5
    + (6718244744129937408 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a3 * b6
    + (7837952201484926976 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a2 * b7
    + (8957659658839916544 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a1 * b8
    + (3359122372064968704 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 ^ 2 * b6
    + (7837952201484926976 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a3 * b7
    + (8957659658839916544 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a2 * b8
    + (4478829829419958272 : R) * h ^ 86 * a7 * a6 ^ 2 * a3 ^ 2 * b8
    + (2153283571836518400 : R) * h ^ 86 * a6 ^ 2 * a5 ^ 3 * b6
    + (7536492501427814400 : R) * h ^ 86 * a6 ^ 2 * a5 ^ 2 * a4 * b7
    + (8613134287346073600 : R) * h ^ 86 * a6 ^ 2 * a5 ^ 2 * a3 * b8
    + (8613134287346073600 : R) * h ^ 86 * a6 ^ 2 * a5 * a4 ^ 2 * b8
    + (659443093874933760 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    + (659443093874933760 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    + (329721546937466880 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    - (2449360062964039680 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    - (2449360062964039680 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    - (2449360062964039680 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    + (2060759668359168000 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    + (4121519336718336000 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    + (2060759668359168000 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    + (2060759668359168000 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    - (2637772375499735040 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 3 * a0
    + (13942511127641456640 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    + (13942511127641456640 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (6971255563820728320 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    + (14130923440177152000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    + (28261846880354304000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (4710307813392384000 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    + (6056110045790208000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 4 * a1
    + (19177681811668992000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a5 * a2
    + (19177681811668992000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a4 * a3
    + (7065461720088576000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a3
    + (7065461720088576000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 * a4 ^ 2
    - (296749392243720192 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (296749392243720192 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (296749392243720192 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (1369037112115986432 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (1610925272180195328 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (1610925272180195328 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (805462636090097664 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (1017426487692754944 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (1271783109615943680 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (1271783109615943680 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (2119638516026572800 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (2119638516026572800 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (3633666027474124800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a5 * a3 * lambda
    - (1816833013737062400 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a4 ^ 2 * lambda
    - (5299096290066432000 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (38790770227937280 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (77581540455874560 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (116372310683811840 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (155163080911749120 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (193953851139686400 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (232744621367623680 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (83123079059865600 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (132996926495784960 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (199495389743677440 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (265993852991569920 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (332492316239462400 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (398990779487354880 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (465489242735247360 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (197832928162480128 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (527554475099947008 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (659443093874933760 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (791331712649920512 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (923220331424907264 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (329721546937466880 : R) * h ^ 78 * a7 ^ 4 * a4 ^ 2 * b5
    - (791331712649920512 : R) * h ^ 78 * a7 ^ 4 * a4 * a3 * b6
    - (923220331424907264 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (461610165712453632 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (44332308831928320 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 3 * b2
    - (1875256663590567936 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (2500342218120757248 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (3125427772650946560 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (3750513327181135872 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (4375598881711325184 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (5000684436241514496 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (1959488050371231744 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (4898720125928079360 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (5878464151113695232 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (6858208176299311104 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (7837952201484926976 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (2939232075556847616 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 ^ 2 * b6
    - (6858208176299311104 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (7837952201484926976 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (3918976100742463488 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (581386564395859968 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 4 * b3
    - (2713137300514013184 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a5 * b4
    - (3391421625642516480 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a4 * b5
    - (4069705950771019776 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a3 * b6
    - (4747990275899523072 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a2 * b7
    - (5426274601028026368 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a1 * b8
    - (2449360062964039680 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b5
    - (5878464151113695232 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b6
    - (6858208176299311104 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * b7
    - (7837952201484926976 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a2 * b8
    - (3429104088149655552 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * b7
    - (7837952201484926976 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 * a3 * b8
    - (1884123125356953600 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 3 * b6
    - (6594430938749337600 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a4 * b7
    - (7536492501427814400 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a3 * b8
    - (7536492501427814400 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * a4 ^ 2 * b8
    - (4844888036632166400 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 ^ 2 * b6
    - (11304738752141721600 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 * a4 * b7
    - (12919701431019110400 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 * a3 * b8
    - (6459850715509555200 : R) * h ^ 78 * a7 * a6 ^ 3 * a4 ^ 2 * b8
    - (6594430938749337600 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 ^ 3 * b7
    - (22609477504283443200 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 ^ 2 * a4 * b8
    + (535797513773383680 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (535797513773383680 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (535797513773383680 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    + (3158677004274892800 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    - (2926278729070018560 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (2926278729070018560 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    - (1463139364535009280 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    - (3091139502538752000 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    - (6182279005077504000 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    - (1030379834179584000 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    - (5923212075340922880 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (18178844217311232000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (18178844217311232000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (6182279005077504000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (6182279005077504000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (5299096290066432000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 4 * a2
    - (3869181418143744000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    - (1934590709071872000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    + (6476673243414528000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    + (530221340553117696 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (352389903289417728 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (352389903289417728 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (176194951644708864 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (1163307491442819072 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (1112810220913950720 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (1112810220913950720 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (463670925380812800 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (463670925380812800 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (582900591907307520 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (4901664068311449600 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (2450832034155724800 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (4636709253808128000 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (1362624760302796800 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (6813123801513984000 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (2075479380276019200 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (29093077670952960 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (29093077670952960 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (43639616506429440 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (58186155341905920 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (72732694177382400 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (87279233012858880 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (101825771848335360 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (47380155064123392 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (750601403910586368 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (1000801871880781824 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (1251002339850977280 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (1501202807821172736 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (1751403275791368192 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (2001603743761563648 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (428638011018706944 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (1071595027546767360 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (1285914033056120832 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (1500233038565474304 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (1714552044074827776 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (642957016528060416 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (1500233038565474304 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (1714552044074827776 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (857276022037413888 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (864480022222602240 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (3140389926881722368 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (3925487408602152960 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (4710584890322583552 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (5495682372043014144 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (6280779853763444736 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (2143190055093534720 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (5143656132224483328 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (6000932154261897216 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (6858208176299311104 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (3000466077130948608 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (6858208176299311104 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (412151933671833600 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (1442531767851417600 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (1648607734687334400 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (1648607734687334400 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (775182085861146624 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 4 * b4
    + (2496463141097963520 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (2995755769317556224 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (3495048397537148928 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (3994341025756741632 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (7489389423293890560 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b6
    + (17475241987685744640 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (19971705128783708160 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (9985852564391854080 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (5770127071405670400 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 3 * b7
    + (19783292816248012800 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 2 * a4 * b8
    + (3633666027474124800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a5 * b6
    + (4239277032053145600 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a4 * b7
    + (4844888036632166400 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a3 * b8
    + (13071104182163865600 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2 * b7
    + (29876809559231692800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 * a4 * b8
    + (10362677189463244800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a5 ^ 3 * b8
    - (1249184022496542720 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (36063294196285440 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (36063294196285440 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (18031647098142720 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    + (1419326574947205120 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (4894304212353024000 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    + (4894304212353024000 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (1352373532360704000 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    + (1352373532360704000 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (5608946225916149760 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (1904730722040545280 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (952365361020272640 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    - (5667089087987712000 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    - (481019157282816000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    - (11844111053094912000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    - (4655108893704192000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    - (67300471081009152 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (433668689032642560 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (243427235824926720 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (243427235824926720 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (655354044490973184 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (2202436895558860800 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (1101218447779430400 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (1014280149270528000 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (2252115923278233600 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (8152659642267205632 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (1816044457741516800 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (2129101187973120000 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (3522479632102195200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (3182055370260480 : R) * h ^ 62 * a7 ^ 8 * b1
    - (16001192719024128 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (99280127552126976 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (132373503402835968 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (165466879253544960 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (198560255104253952 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (231653630954962944 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (264747006805671936 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (474996444902719488 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (1189906876741976064 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (1487383595927470080 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (1784860315112964096 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (2082337034298458112 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (2379813753483952128 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (468822824551710720 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (1125174778924105728 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (1312703908744790016 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (1500233038565474304 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (656351954372395008 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (1500233038565474304 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (1100133951357321216 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (2836834832539975680 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (3404201799047970816 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (3971568765555965952 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (4538935732063961088 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (3771190193097277440 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (8799443783893647360 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (10056507181592739840 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (5028253590796369920 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (1262215296869990400 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (4327595303554252800 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (589209039871672320 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (6924152485686804480 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (8078177899967938560 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (9232203314249072640 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (16192419094132162560 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (37011243643730657280 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (9067342540780339200 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    - (908416506868531200 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 5 * b6
    - (8478554064106291200 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a5 * b7
    - (9689776073264332800 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    - (18353377944325324800 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    + (162815166444994560 : R) * h ^ 56 * a7 ^ 9 * a0
    + (130748382267310080 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    - (267657261613056000 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    - (267657261613056000 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (1766595038973788160 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (555117135664250880 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (277558567832125440 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (1239675737997312000 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    + (1855741680817274880 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    + (14915944076342722560 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    + (4073220281991168000 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    + (4549968094298112000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    + (8737200430645248000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    + (52265259456528384 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (238722339670327296 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (329641048512921600 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (164820524256460800 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (1366412264327872512 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (3221353754083196928 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (397259725130956800 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (3145924430329282560 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (4082932991901302784 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (1914416818185830400 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (1644061941301248 : R) * h ^ 54 * a7 ^ 9 * b2
    + (113963040189186048 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (146692752569008128 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (183365940711260160 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (220039128853512192 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (256712316995764224 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (293385505138016256 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (573968571760115712 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (1048714534170132480 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (1258457441004158976 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (1468200347838185472 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (1677943254672211968 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (622091824885923840 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (1451547591400488960 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (1658911533029130240 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (829455766514565120 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (812906913925693440 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (4681322968897290240 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (5461543463713505280 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (6241763958529720320 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (6662693602763735040 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (15229013949174251520 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (1983481180795699200 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (1921868672343736320 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (13014212495605235712 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (14873385709263126528 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (21580716838414712832 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (1788444997897420800 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (10516182756596121600 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    - (54733009688985600 : R) * h ^ 48 * a7 ^ 10 * a1
    + (99998829662699520 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (283434952823930880 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (141717476411965440 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (1675333398870097920 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (6250340423030538240 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (891016936685568000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    - (6993630840194334720 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    - (10252892123808399360 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    - (5122985451061248000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    - (27814395711062016 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (358829608138702848 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (419404841723363328 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (1716211261076668416 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (1549892516667457536 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (2725650205620830208 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (330010684135833600 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (10033418339352576 : R) * h ^ 46 * a7 ^ 10 * b3
    - (130160676122394624 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (124879100077670400 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (149854920093204480 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (174830740108738560 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (199806560124272640 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (409893363379077120 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (1337315591769292800 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (1560201523730841600 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (1783087455692390400 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (910175561727344640 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (2080401283948216320 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (1549601823617187840 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (7380852923959345152 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (8435260484524965888 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (8344273492144816128 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (3211123554300985344 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (15247965578267197440 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (1935116413068902400 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    + (18832931967467520 : R) * h ^ 40 * a7 ^ 11 * a2
    + (561437683608453120 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (871347649763082240 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (3971754225397923840 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (3954216298547773440 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (7390407266748334080 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (937642363453440000 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (34119220249755648 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (408401789419782144 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (191552353034305536 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (1427146858429415424 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (552086380247777280 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (10809754616070144 : R) * h ^ 38 * a7 ^ 11 * b4
    + (89232313354813440 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (135746979291463680 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (158371475840040960 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (180995972388618240 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (597567944817377280 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (1825225894961086464 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (2085972451384098816 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (1056851741091299328 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (2266309216085999616 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (8149401325994508288 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (3301890292168261632 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (62737159068057600 : R) * h ^ 32 * a7 ^ 12 * a3
    - (983472566666526720 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (499157209385533440 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (3927358552858951680 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (1587586001503518720 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (35620168588591104 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (324888899302195200 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (362563048197586944 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (7069530901708800 : R) * h ^ 30 * a7 ^ 12 * b5
    - (110407124810465280 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (164984857942818816 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (188554123363221504 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (784085306516176896 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (1897568860920348672 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (2214997359241199616 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (89004716257443840 : R) * h ^ 24 * a7 ^ 13 * a4
    + (908728320534773760 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (1056082723303587840 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (27083402658643968 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (116707764235862016 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (7839106337341440 : R) * h ^ 22 * a7 ^ 13 * b6
    + (132707847005798400 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (161933661529178112 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (729239092746780672 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (77034602832445440 : R) * h ^ 16 * a7 ^ 14 * a5
    - (344558143326781440 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (18404226054660096 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (8784184583946240 : R) * h ^ 14 * a7 ^ 14 * b7
    - (117717423496888320 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (55086188649246720 : R) * h ^ 8 * a7 ^ 15 * a6
    + (1137481421126400 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (7452462009581568 : R) * h ^ 6 * a7 ^ 15 * b8
    - (3451790574650880 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Combined integer polynomial of compact-block expansions `12`–`14`. -/
def degreeZeroExpansionGroup4810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (13781014859753717760 : R) * h ^ 104 * a6 * a5 * a4 * a0
    - (13781014859753717760 : R) * h ^ 104 * a6 * a5 * a3 * a1
    - (6890507429876858880 : R) * h ^ 104 * a6 * a5 * a2 ^ 2
    - (6890507429876858880 : R) * h ^ 104 * a6 * a4 ^ 2 * a1
    + (324259173170675712 : R) * h ^ 102 * a6 * a5 ^ 2 * b1
    + (1297036692682702848 : R) * h ^ 102 * a6 * a5 * a4 * b2
    + (1945555039024054272 : R) * h ^ 102 * a6 * a5 * a3 * b3
    + (2594073385365405696 : R) * h ^ 102 * a6 * a5 * a2 * b4
    + (3242591731706757120 : R) * h ^ 102 * a6 * a5 * a1 * b5
    + (3891110078048108544 : R) * h ^ 102 * a6 * a5 * a0 * b6
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a5 * a4 * a0
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a5 * a3 * a1
    + (3014597000571125760 : R) * h ^ 96 * a7 ^ 2 * a5 * a2 ^ 2
    + (3014597000571125760 : R) * h ^ 96 * a7 ^ 2 * a4 ^ 2 * a1
    + (10335761144815288320 : R) * h ^ 96 * a7 * a6 ^ 2 * a4 * a0
    + (10335761144815288320 : R) * h ^ 96 * a7 * a6 ^ 2 * a3 * a1
    + (5167880572407644160 : R) * h ^ 96 * a7 * a6 ^ 2 * a2 ^ 2
    + (8613134287346073600 : R) * h ^ 96 * a7 * a6 * a5 ^ 2 * a0
    + (17226268574692147200 : R) * h ^ 96 * a7 * a6 * a5 * a4 * a1
    + (8613134287346073600 : R) * h ^ 96 * a7 * a6 * a5 * a3 * a2
    + (1722626857469214720 : R) * h ^ 96 * a7 * a6 * a4 ^ 2 * a2
    + (7177611906121728000 : R) * h ^ 96 * a6 * a5 ^ 3 * a2
    + (21532835718365184000 : R) * h ^ 96 * a6 * a5 ^ 2 * a4 * a3
    + (7177611906121728000 : R) * h ^ 96 * a6 * a5 * a4 ^ 3
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 * a5 ^ 2 * a1 * lambda
    - (3100728343444586496 : R) * h ^ 95 * a7 * a6 * a5 * a4 * a2 * lambda
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 * a5 * a3 ^ 2 * lambda
    - (1550364171722293248 : R) * h ^ 95 * a7 * a6 * a4 ^ 2 * a3 * lambda
    - (141863388262170624 : R) * h ^ 94 * a7 ^ 2 * a5 ^ 2 * b1
    - (567453553048682496 : R) * h ^ 94 * a7 ^ 2 * a5 * a4 * b2
    - (851180329573023744 : R) * h ^ 94 * a7 ^ 2 * a5 * a3 * b3
    - (1134907106097364992 : R) * h ^ 94 * a7 ^ 2 * a5 * a2 * b4
    - (1418633882621706240 : R) * h ^ 94 * a7 ^ 2 * a5 * a1 * b5
    - (1702360659146047488 : R) * h ^ 94 * a7 ^ 2 * a5 * a0 * b6
    - (486388759756013568 : R) * h ^ 94 * a7 * a6 ^ 2 * a5 * b1
    - (972777519512027136 : R) * h ^ 94 * a7 * a6 ^ 2 * a4 * b2
    - (1459166279268040704 : R) * h ^ 94 * a7 * a6 ^ 2 * a3 * b3
    - (1945555039024054272 : R) * h ^ 94 * a7 * a6 ^ 2 * a2 * b4
    - (2431943798780067840 : R) * h ^ 94 * a7 * a6 ^ 2 * a1 * b5
    - (2918332558536081408 : R) * h ^ 94 * a7 * a6 ^ 2 * a0 * b6
    - (891712726219358208 : R) * h ^ 94 * a7 * a6 * a5 ^ 2 * b2
    - (1459166279268040704 : R) * h ^ 94 * a7 * a6 * a5 * a4 * b3
    - (1945555039024054272 : R) * h ^ 94 * a7 * a6 * a5 * a3 * b4
    - (2431943798780067840 : R) * h ^ 94 * a7 * a6 * a5 * a2 * b5
    - (2918332558536081408 : R) * h ^ 94 * a7 * a6 * a5 * a1 * b6
    - (3404721318292094976 : R) * h ^ 94 * a7 * a6 * a5 * a0 * b7
    - (918734323983581184 : R) * h ^ 94 * a6 * a5 ^ 3 * b4
    - (3445253714938429440 : R) * h ^ 94 * a6 * a5 ^ 2 * a4 * b5
    - (4134304457926115328 : R) * h ^ 94 * a6 * a5 ^ 2 * a3 * b6
    - (4823355200913801216 : R) * h ^ 94 * a6 * a5 ^ 2 * a2 * b7
    - (5512405943901487104 : R) * h ^ 94 * a6 * a5 ^ 2 * a1 * b8
    - (4134304457926115328 : R) * h ^ 94 * a6 * a5 * a4 ^ 2 * b6
    - (9646710401827602432 : R) * h ^ 94 * a6 * a5 * a4 * a3 * b7
    - (11024811887802974208 : R) * h ^ 94 * a6 * a5 * a4 * a2 * b8
    - (5512405943901487104 : R) * h ^ 94 * a6 * a5 * a3 ^ 2 * b8
    - (1607785066971267072 : R) * h ^ 94 * a6 * a4 ^ 3 * b7
    - (5512405943901487104 : R) * h ^ 94 * a6 * a4 ^ 2 * a3 * b8
    - (7536492501427814400 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    - (7536492501427814400 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    - (3768246250713907200 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    - (3768246250713907200 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    - (7536492501427814400 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    - (3768246250713907200 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    - (753649250142781440 : R) * h ^ 88 * a7 ^ 3 * a4 ^ 2 * a2
    - (9689776073264332800 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a5 * a0
    - (9689776073264332800 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    - (6459850715509555200 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    - (2045619393244692480 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 ^ 2 * a1
    + (2368611929020170240 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    + (2260947750428344320 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    + (3552917893530255360 : R) * h ^ 88 * a7 ^ 2 * a6 * a4 ^ 2 * a3
    - (3140205208928256000 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 3 * a2
    - (9420615626784768000 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 2 * a4 * a3
    - (3140205208928256000 : R) * h ^ 88 * a7 ^ 2 * a5 * a4 ^ 3
    - (16149626788773888000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 ^ 2 * a2
    - (32299253577547776000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 * a4 * a3
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 ^ 2 * a4 ^ 3
    - (16149626788773888000 : R) * h ^ 88 * a7 * a6 * a5 ^ 3 * a3
    - (24224440183160832000 : R) * h ^ 88 * a7 * a6 * a5 ^ 2 * a4 ^ 2
    - (1480382455637606400 : R) * h ^ 88 * a6 * a5 ^ 5
    + (159596311794941952 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (678284325128503296 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (1356568650257006592 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (678284325128503296 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (678284325128503296 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (2325546257583439872 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (2325546257583439872 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (1162773128791719936 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a3 ^ 2 * lambda
    + (3003830582711943168 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (6007661165423886336 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (1001276860903981056 : R) * h ^ 87 * a7 ^ 2 * a6 * a4 ^ 3 * lambda
    + (1614962678877388800 : R) * h ^ 87 * a7 * a6 * a5 ^ 3 * a4 * lambda
    + (354658470655426560 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (709316941310853120 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (1418633882621706240 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (1773292353277132800 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (2127950823932559360 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6
    + (390124317720969216 : R) * h ^ 86 * a7 ^ 3 * a5 ^ 2 * b2
    + (638385247179767808 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (851180329573023744 : R) * h ^ 86 * a7 ^ 3 * a5 * a3 * b4
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 3 * a5 * a2 * b5
    + (1276770494359535616 : R) * h ^ 86 * a7 ^ 3 * a5 * a1 * b6
    + (1489565576752791552 : R) * h ^ 86 * a7 ^ 3 * a5 * a0 * b7
    + (182395784908505088 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 3 * b1
    + (1033576114481528832 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a5 * b2
    + (1094374709451030528 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (1459166279268040704 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a3 * b4
    + (1823957849085050880 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a2 * b5
    + (2188749418902061056 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a1 * b6
    + (2553540988719071232 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a0 * b7
    + (623185598437392384 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 ^ 2 * b3
    + (851180329573023744 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a4 * b4
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a3 * b5
    + (1276770494359535616 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a2 * b6
    + (1489565576752791552 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a1 * b7
    + (1702360659146047488 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a0 * b8
    + (401946266742816768 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 3 * b4
    + (1507298500285562880 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a4 * b5
    + (1808758200342675456 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a3 * b6
    + (2110217900399788032 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a2 * b7
    + (2411677600456900608 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a1 * b8
    + (1808758200342675456 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 ^ 2 * b6
    + (4220435800799576064 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a3 * b7
    + (4823355200913801216 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a2 * b8
    + (2411677600456900608 : R) * h ^ 86 * a7 ^ 2 * a5 * a3 ^ 2 * b8
    + (703405966799929344 : R) * h ^ 86 * a7 ^ 2 * a4 ^ 3 * b7
    + (2411677600456900608 : R) * h ^ 86 * a7 ^ 2 * a4 ^ 2 * a3 * b8
    + (2067152228963057664 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 ^ 2 * b4
    + (5167880572407644160 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a4 * b5
    + (6201456686889172992 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a3 * b6
    + (7235032801370701824 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a2 * b7
    + (8268608915852230656 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a1 * b8
    + (3100728343444586496 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 ^ 2 * b6
    + (7235032801370701824 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a3 * b7
    + (8268608915852230656 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a2 * b8
    + (4134304457926115328 : R) * h ^ 86 * a7 * a6 ^ 2 * a3 ^ 2 * b8
    + (2727492524326256640 : R) * h ^ 86 * a7 * a6 * a5 ^ 3 * b5
    + (9818973087574523904 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a4 * b6
    + (11455468602170277888 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a3 * b7
    + (13091964116766031872 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a2 * b8
    + (11455468602170277888 : R) * h ^ 86 * a7 * a6 * a5 * a4 ^ 2 * b7
    + (26183928233532063744 : R) * h ^ 86 * a7 * a6 * a5 * a4 * a3 * b8
    + (4363988038922010624 : R) * h ^ 86 * a7 * a6 * a4 ^ 3 * b8
    + (1256082083571302400 : R) * h ^ 86 * a6 * a5 ^ 4 * b7
    + (5742089524897382400 : R) * h ^ 86 * a6 * a5 ^ 3 * a4 * b8
    + (1318886187749867520 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    + (1318886187749867520 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    + (659443093874933760 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    + (6231460160187924480 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    + (6829946329418956800 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    + (4710307813392384000 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    + (894958484544552960 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    - (1036267718946324480 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    - (989164640812400640 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    - (1554401578419486720 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    + (2422444018316083200 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 3 * a0
    - (430656714367303680 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    - (2583940286203822080 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    - (1695710812821258240 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    + (5315918817971404800 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    + (8747714510585856000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (1287484135660584960 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    + (7065461720088576000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 3 * a3
    + (10598192580132864000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 2 * a4 ^ 2
    + (12112220091580416000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a5 * a2
    + (12112220091580416000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a4 * a3
    + (31289901903249408000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a3
    + (31289901903249408000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 * a4 ^ 2
    + (15140275114475520000 : R) * h ^ 80 * a7 ^ 2 * a6 * a5 ^ 3 * a4
    + (647667324341452800 : R) * h ^ 80 * a7 ^ 2 * a5 ^ 5
    + (5551434208641024000 : R) * h ^ 80 * a7 * a6 ^ 2 * a5 ^ 4
    - (69823386410287104 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (119697233846206464 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (1740597275513585664 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (1695710812821258240 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (847855406410629120 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (1314175879936475136 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (2628351759872950272 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (438058626645491712 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (872079846593789952 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (3779012668573089792 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (3779012668573089792 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (3161289443902488576 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (3161289443902488576 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (706546172008857600 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    - (3633666027474124800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (1185988217300582400 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 ^ 4 * lambda
    - (62065232364699648 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (124130464729399296 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (186195697094098944 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (248260929458798592 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (310326161823498240 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (372391394188197888 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (186195697094098944 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (731483095726817280 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (797981558974709760 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (1063975411966279680 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (1329969264957849600 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (1595963117949419520 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (1861956970940989440 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (272643699316359168 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (372391394188197888 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (465489242735247360 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (558587091282296832 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (651684939829346304 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (744782788376395776 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (273593677362757632 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 3 * b2
    - (668784544664518656 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (638385247179767808 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (797981558974709760 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (957577870769651712 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (1117174182564593664 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (1276770494359535616 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (1788492002019508224 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (4122904721369333760 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (4947485665643200512 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (5772066609917067264 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (6596647554190934016 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (2260947750428344320 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 ^ 2 * b6
    - (5275544750999470080 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (6029194001142251520 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (3014597000571125760 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (1193277979392737280 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 3 * b5
    - (4295800725813854208 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a4 * b6
    - (5011767513449496576 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a3 * b7
    - (5727734301085138944 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (5011767513449496576 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 ^ 2 * b7
    - (11455468602170277888 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 * a3 * b8
    - (1909244767028379648 : R) * h ^ 78 * a7 ^ 3 * a4 ^ 3 * b8
    - (1550364171722293248 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a5 * b4
    - (1937955214652866560 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a4 * b5
    - (2325546257583439872 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a3 * b6
    - (2713137300514013184 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a2 * b7
    - (3100728343444586496 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a1 * b8
    - (5329376840295383040 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b5
    - (12790504416708919296 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b6
    - (14922255152827072512 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * b7
    - (17054005888945225728 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a2 * b8
    - (7461127576413536256 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * b7
    - (17054005888945225728 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 * a3 * b8
    - (4091238786489384960 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 3 * b6
    - (14319335752712847360 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a4 * b7
    - (16364955145957539840 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a3 * b8
    - (16364955145957539840 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * a4 ^ 2 * b8
    - (549535911562444800 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 4 * b7
    - (2512164167142604800 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 3 * a4 * b8
    - (3768246250713907200 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 ^ 3 * b7
    - (12919701431019110400 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 ^ 2 * a4 * b8
    - (4844888036632166400 : R) * h ^ 78 * a7 * a6 * a5 ^ 4 * b8
    - (871580118558965760 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    - (1133417817597542400 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    - (824303867343667200 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    - (1847410432105512960 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    + (728019634099322880 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    + (1943001973024358400 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    + (1236455801015500800 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    + (765425019676262400 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    + (2355153906696192000 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    + (467105524828078080 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    + (1095146566613729280 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (3515908332139315200 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (2927119855465267200 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (13775547538184601600 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (13607322259134873600 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (6623870362583040000 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    - (3028055022895104000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 4 * a2
    - (19682357648818176000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    - (9841178824409088000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    - (23551539066961920000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    - (4931103492145152000 : R) * h ^ 72 * a7 ^ 3 * a6 * a5 ^ 4
    - (8327151312961536000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 3 * a5 ^ 3
    + (87279233012858880 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (316387219671613440 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (296749392243720192 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (148374696121860096 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (923913023750406144 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (2713760723606962176 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (2702539107933880320 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (1383064131707338752 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (1383064131707338752 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (1144604798654349312 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (3455010781123313664 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (1727505390561656832 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (5039440571853176832 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (518869845069004800 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (2725249520605593600 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (3179457774039859200 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (62065232364699648 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (122190926218002432 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (139646772820574208 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (186195697094098944 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (232744621367623680 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (279293545641148416 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (325842469914673152 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (262668929829175296 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (470476627478839296 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (465489242735247360 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (581861553419059200 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (698233864102871040 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (814606174786682880 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (930978485470494720 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (386799394558574592 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (814606174786682880 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (977527409744019456 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (1140448644701356032 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (1303369879658692608 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (395665856324960256 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (923220331424907264 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (1055108950199894016 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (527554475099947008 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (151046509377355776 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (1871456751404974080 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (2244323134616371200 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (2693187761539645440 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (3142052388462919680 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (3590917015386193920 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (3926476969067151360 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (9304797469961355264 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (10855597048288247808 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (12406396626615140352 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (5357975137733836800 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (12246800314820198400 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (1789916969089105920 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (6264709391811870720 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (7159667876356423680 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (7159667876356423680 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (387591042930573312 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 4 * b4
    + (3391421625642516480 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (4069705950771019776 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (4747990275899523072 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (5426274601028026368 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (7065461720088576000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b6
    + (16486077346873344000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (18841231253569536000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (9420615626784768000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (6924152485686804480 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 3 * b7
    + (23739951379497615360 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 2 * a4 * b8
    + (2119638516026572800 : R) * h ^ 70 * a7 ^ 3 * a5 ^ 4 * b8
    + (4239277032053145600 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2 * b7
    + (9689776073264332800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 * a4 * b8
    + (13188861877498675200 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a5 ^ 3 * b8
    + (368209264272998400 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (236078203184087040 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (355481042791956480 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (216379765177712640 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    - (1373262535301529600 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (2306362391018864640 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (2638508361095577600 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (37719261786931200 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    - (35879297797324800 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (1066127705977651200 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (9796388843862097920 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (4850881062198312960 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (9326304329717514240 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (1094778573815808000 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    + (3974322217549824000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (10960928338083840000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (8206239393644544000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    + (6245363484721152000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 4 * a5 ^ 2
    - (15273865777250304 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (321296676528586752 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (463943672983977984 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (459034216127004672 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (1137123721538961408 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (2431544882217615360 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (1214486630979600384 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (1509248862114545664 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (898196821166260224 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (5108328823624040448 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (2774076907849777152 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (681312380151398400 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (3151069758200217600 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (6788384789889024 : R) * h ^ 62 * a7 ^ 8 * b1
    - (80975732850819072 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (77823982769799168 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (81460617478668288 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (101825771848335360 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (122190926218002432 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (142556080587669504 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (162921234957336576 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (141309234401771520 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (730236249540919296 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (853396945014620160 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (1024076334017544192 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (1194755723020468224 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (1365435112023392256 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (697757638129090560 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (1622666407097401344 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (1893110808280301568 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (2163555209463201792 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (916007672585650176 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (2093731823052914688 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (567136893699883008 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (3472911929935134720 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (4138282490995408896 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (4827996239494643712 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (5517709987993878528 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (5030445467226341376 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (11702932935454752768 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (13374780497662574592 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (6667440709856919552 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (2308050828562268160 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (7913317126499205120 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (696452655265873920 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (3921331254649159680 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (4574886463757352960 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (5228441672865546240 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (10798380662202040320 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (24682012942176092160 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (12800261482893803520 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    - (2119638516026572800 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a5 * b7
    - (2422444018316083200 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    - (13323442100738457600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    - (10341679953346560 : R) * h ^ 56 * a7 ^ 9 * a0
    + (556798132176814080 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (667720225998766080 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (700336293543936000 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (1004825981359226880 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (588854189673676800 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (319030041897861120 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (427653630284267520 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    - (2384120196932567040 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (3169101405298360320 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (912304526013235200 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (1360259092316160000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (5687460117872640000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    - (2342011306770432000 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    + (36752739526508544 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (366640965554798592 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (402490228645822464 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (200682572391383040 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (863528652606799872 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (2538735386046234624 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (605090557621960704 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (1431252788595130368 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (3794732532344291328 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (1362624760302796800 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (8061206937993216 : R) * h ^ 54 * a7 ^ 9 * b2
    + (42003130887438336 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (91097699457171456 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (106068512342016000 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (127282214810419200 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (148495917278822400 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (169709619747225600 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (301009450045538304 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (1159143297311047680 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (1373011434333536256 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (1601846673389125632 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (1830681912444715008 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (848446359550820352 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (1964494917086478336 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (2245137048098832384 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (1113840600748130304 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (899454799907389440 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (3838378874769506304 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (4470211994720403456 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (5108813708251889664 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (5967708898600157184 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (13631353735027359744 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (3075683805026058240 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (692667586487255040 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (5981354937412485120 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (6835834214185697280 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (17999852520402321408 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (397432221754982400 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (5904707294645452800 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    - (72455980843008000 : R) * h ^ 48 * a7 ^ 10 * a1
    - (552536845477478400 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (484508517563105280 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (243961975359406080 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (218050518193274880 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (1869732352905707520 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (474274676185497600 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    - (183299841164574720 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    - (907048033651261440 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (1887359490588672000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    + (351301696015564800 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 6
    - (38602309210472448 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (267165866083221504 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (361143701084307456 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (938353339454717952 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (1464335807400640512 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (2010116959500238848 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (215571495282278400 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (3977569212825600 : R) * h ^ 46 * a7 ^ 10 * b3
    - (68454597512921088 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (126386585280184320 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (149397499633729536 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (174297082906017792 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (199196666178306048 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (427319653627330560 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (1214665273701826560 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (1412318815038996480 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (1614078645758853120 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (898993146757644288 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (2050849838777499648 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (853958829816152064 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (4400726295818797056 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (5027456994622046208 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (7558190779286421504 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (1138477718568960000 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (9653334272190185472 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (965192538547814400 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    + (71064004256071680 : R) * h ^ 40 * a7 ^ 11 * a2
    + (322196920766300160 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (506723012255416320 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (1006927556168908800 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (1605748953804963840 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (1055547194301480960 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (271793073527193600 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (26815497567731712 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (243891984220028928 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (178182712052416512 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (1068238568184348672 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (369626382021427200 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (5626050675474432 : R) * h ^ 38 * a7 ^ 11 * b4
    + (88538345625354240 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (125099549072031744 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (145365031679164416 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (166131464776187904 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (385903402640474112 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (1221699123523092480 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (1395060584176680960 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (977132358652133376 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (1004053839118073856 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (5527521943860805632 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (1800170825551183872 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (45182806634004480 : R) * h ^ 32 * a7 ^ 12 * a3
    - (387733444488069120 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (281438599690321920 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (1358184227190865920 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (237117324719554560 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (21988692634632192 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (241935216524918784 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (245269292528959488 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (6748944507863040 : R) * h ^ 30 * a7 ^ 12 * b5
    - (75959943240351744 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (115391089392746496 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (131737161383804928 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (388958114763767808 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (1323247392836812800 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (1272254798493646848 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (42085657726156800 : R) * h ^ 24 * a7 ^ 13 * a4
    + (408510862175109120 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (330696101572116480 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (19785183000920064 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (78832690816352256 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (5502050670477312 : R) * h ^ 22 * a7 ^ 13 * b6
    + (69473747351371776 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (112964023665819648 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (429187500494290944 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (38757585625866240 : R) * h ^ 16 * a7 ^ 14 * a5
    - (136769641217556480 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (12312955018764288 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (4685987376365568 : R) * h ^ 14 * a7 ^ 14 * b7
    - (69636530074288128 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (24422762117806080 : R) * h ^ 8 * a7 ^ 15 * a6
    + (750260764141056 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (4374530079424512 : R) * h ^ 6 * a7 ^ 15 * b8
    - (1618917633957120 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Combined integer polynomial of compact-block expansions `15`–`17`. -/
def degreeZeroExpansionGroup5810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6485183463413514240 : R) * h ^ 112 * a6 * a1 * a0
    - (576460752303423488 : R) * h ^ 110 * a6 * a2 * b1
    - (1152921504606846976 : R) * h ^ 110 * a6 * a1 * b2
    - (1729382256910270464 : R) * h ^ 110 * a6 * a0 * b3
    - (2837267765243412480 : R) * h ^ 104 * a7 ^ 2 * a1 * a0
    - (1621295865853378560 : R) * h ^ 104 * a7 * a6 * a2 * a0
    - (810647932926689280 : R) * h ^ 104 * a7 * a6 * a1 ^ 2
    - (13781014859753717760 : R) * h ^ 104 * a6 * a4 * a3 * a2
    - (2296835809958952960 : R) * h ^ 104 * a6 * a3 ^ 3
    - (2296835809958952960 : R) * h ^ 104 * a5 ^ 3 * a0
    + (1459166279268040704 : R) * h ^ 103 * a7 * a6 * a3 * a0 * lambda
    + (1459166279268040704 : R) * h ^ 103 * a7 * a6 * a2 * a1 * lambda
    + (252201579132747776 : R) * h ^ 102 * a7 ^ 2 * a2 * b1
    + (504403158265495552 : R) * h ^ 102 * a7 ^ 2 * a1 * b2
    + (756604737398243328 : R) * h ^ 102 * a7 ^ 2 * a0 * b3
    + (216172782113783808 : R) * h ^ 102 * a7 * a6 * a3 * b1
    + (432345564227567616 : R) * h ^ 102 * a7 * a6 * a2 * b2
    + (648518346341351424 : R) * h ^ 102 * a7 * a6 * a1 * b3
    + (864691128455135232 : R) * h ^ 102 * a7 * a6 * a0 * b4
    + (972777519512027136 : R) * h ^ 102 * a6 * a4 ^ 2 * b3
    + (2594073385365405696 : R) * h ^ 102 * a6 * a4 * a3 * b4
    + (3242591731706757120 : R) * h ^ 102 * a6 * a4 * a2 * b5
    + (3891110078048108544 : R) * h ^ 102 * a6 * a4 * a1 * b6
    + (4539628424389459968 : R) * h ^ 102 * a6 * a4 * a0 * b7
    + (1621295865853378560 : R) * h ^ 102 * a6 * a3 ^ 2 * b5
    + (3891110078048108544 : R) * h ^ 102 * a6 * a3 * a2 * b6
    + (4539628424389459968 : R) * h ^ 102 * a6 * a3 * a1 * b7
    + (5188146770730811392 : R) * h ^ 102 * a6 * a3 * a0 * b8
    + (2269814212194729984 : R) * h ^ 102 * a6 * a2 ^ 2 * b7
    + (5188146770730811392 : R) * h ^ 102 * a6 * a2 * a1 * b8
    + (216172782113783808 : R) * h ^ 102 * a5 ^ 3 * b2
    + (709316941310853120 : R) * h ^ 96 * a7 ^ 3 * a2 * a0
    + (354658470655426560 : R) * h ^ 96 * a7 ^ 3 * a1 ^ 2
    - (3343922723322593280 : R) * h ^ 96 * a7 ^ 2 * a6 * a3 * a0
    - (3343922723322593280 : R) * h ^ 96 * a7 ^ 2 * a6 * a2 * a1
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a4 * a3 * a2
    + (1004865666857041920 : R) * h ^ 96 * a7 ^ 2 * a3 ^ 3
    + (5167880572407644160 : R) * h ^ 96 * a7 * a6 * a5 ^ 2 * a0
    + (8613134287346073600 : R) * h ^ 96 * a7 * a6 * a5 * a3 * a2
    + (6890507429876858880 : R) * h ^ 96 * a7 * a6 * a4 ^ 2 * a2
    + (8613134287346073600 : R) * h ^ 96 * a7 * a6 * a4 * a3 ^ 2
    + (287104476244869120 : R) * h ^ 96 * a7 * a5 ^ 3 * a1
    + (1794402976530432000 : R) * h ^ 96 * a5 ^ 4 * a3
    + (3588805953060864000 : R) * h ^ 96 * a5 ^ 3 * a4 ^ 2
    - (638385247179767808 : R) * h ^ 95 * a7 ^ 3 * a3 * a0 * lambda
    - (638385247179767808 : R) * h ^ 95 * a7 ^ 3 * a2 * a1 * lambda
    - (1367968386813788160 : R) * h ^ 95 * a7 ^ 2 * a6 * a4 * a0 * lambda
    - (1367968386813788160 : R) * h ^ 95 * a7 ^ 2 * a6 * a3 * a1 * lambda
    - (683984193406894080 : R) * h ^ 95 * a7 ^ 2 * a6 * a2 ^ 2 * lambda
    - (516788057240764416 : R) * h ^ 95 * a7 * a5 ^ 3 * a2 * lambda
    - (94575592174780416 : R) * h ^ 94 * a7 ^ 3 * a3 * b1
    - (189151184349560832 : R) * h ^ 94 * a7 ^ 3 * a2 * b2
    - (283726776524341248 : R) * h ^ 94 * a7 ^ 3 * a1 * b3
    - (378302368699121664 : R) * h ^ 94 * a7 ^ 3 * a0 * b4
    - (54043195528445952 : R) * h ^ 94 * a7 ^ 2 * a6 * a4 * b1
    - (108086391056891904 : R) * h ^ 94 * a7 ^ 2 * a6 * a3 * b2
    - (162129586585337856 : R) * h ^ 94 * a7 ^ 2 * a6 * a2 * b3
    - (216172782113783808 : R) * h ^ 94 * a7 ^ 2 * a6 * a1 * b4
    - (270215977642229760 : R) * h ^ 94 * a7 ^ 2 * a6 * a0 * b5
    - (425590164786511872 : R) * h ^ 94 * a7 ^ 2 * a4 ^ 2 * b3
    - (1134907106097364992 : R) * h ^ 94 * a7 ^ 2 * a4 * a3 * b4
    - (1418633882621706240 : R) * h ^ 94 * a7 ^ 2 * a4 * a2 * b5
    - (1702360659146047488 : R) * h ^ 94 * a7 ^ 2 * a4 * a1 * b6
    - (1986087435670388736 : R) * h ^ 94 * a7 ^ 2 * a4 * a0 * b7
    - (709316941310853120 : R) * h ^ 94 * a7 ^ 2 * a3 ^ 2 * b5
    - (1702360659146047488 : R) * h ^ 94 * a7 ^ 2 * a3 * a2 * b6
    - (1986087435670388736 : R) * h ^ 94 * a7 ^ 2 * a3 * a1 * b7
    - (2269814212194729984 : R) * h ^ 94 * a7 ^ 2 * a3 * a0 * b8
    - (993043717835194368 : R) * h ^ 94 * a7 ^ 2 * a2 ^ 2 * b7
    - (2269814212194729984 : R) * h ^ 94 * a7 ^ 2 * a2 * a1 * b8
    - (486388759756013568 : R) * h ^ 94 * a7 * a6 * a5 ^ 2 * b2
    - (1215971899390033920 : R) * h ^ 94 * a7 * a6 * a5 * a4 * b3
    - (1621295865853378560 : R) * h ^ 94 * a7 * a6 * a5 * a3 * b4
    - (2026619832316723200 : R) * h ^ 94 * a7 * a6 * a5 * a2 * b5
    - (2431943798780067840 : R) * h ^ 94 * a7 * a6 * a5 * a1 * b6
    - (2837267765243412480 : R) * h ^ 94 * a7 * a6 * a5 * a0 * b7
    - (1783425452438716416 : R) * h ^ 94 * a7 * a6 * a4 ^ 2 * b4
    - (4458563631096791040 : R) * h ^ 94 * a7 * a6 * a4 * a3 * b5
    - (5350276357316149248 : R) * h ^ 94 * a7 * a6 * a4 * a2 * b6
    - (6241989083535507456 : R) * h ^ 94 * a7 * a6 * a4 * a1 * b7
    - (7133701809754865664 : R) * h ^ 94 * a7 * a6 * a4 * a0 * b8
    - (2675138178658074624 : R) * h ^ 94 * a7 * a6 * a3 ^ 2 * b6
    - (6241989083535507456 : R) * h ^ 94 * a7 * a6 * a3 * a2 * b7
    - (7133701809754865664 : R) * h ^ 94 * a7 * a6 * a3 * a1 * b8
    - (3566850904877432832 : R) * h ^ 94 * a7 * a6 * a2 ^ 2 * b8
    - (81064793292668928 : R) * h ^ 94 * a7 * a5 ^ 3 * b3
    - (287104476244869120 : R) * h ^ 94 * a5 ^ 4 * b5
    - (1378101485975371776 : R) * h ^ 94 * a5 ^ 3 * a4 * b6
    - (1607785066971267072 : R) * h ^ 94 * a5 ^ 3 * a3 * b7
    - (1837468647967162368 : R) * h ^ 94 * a5 ^ 3 * a2 * b8
    - (2411677600456900608 : R) * h ^ 94 * a5 ^ 2 * a4 ^ 2 * b7
    + (1462966191453634560 : R) * h ^ 88 * a7 ^ 4 * a3 * a0
    + (1462966191453634560 : R) * h ^ 88 * a7 ^ 4 * a2 * a1
    + (3901243177209692160 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    + (3901243177209692160 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    + (1950621588604846080 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    - (1507298500285562880 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    - (3768246250713907200 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    - (3014597000571125760 : R) * h ^ 88 * a7 ^ 3 * a4 ^ 2 * a2
    - (3768246250713907200 : R) * h ^ 88 * a7 ^ 3 * a4 * a3 ^ 2
    - (3875910429305733120 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a5 * a0
    - (3229925357754777600 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    - (645985071550955520 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 ^ 2 * a1
    - (6459850715509555200 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    - (4306567143673036800 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    - (5598537286774947840 : R) * h ^ 88 * a7 ^ 2 * a6 * a4 ^ 2 * a3
    + (1256082083571302400 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 3 * a2
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 * a5 ^ 3 * a3
    - (8074813394386944000 : R) * h ^ 88 * a7 * a6 * a5 ^ 2 * a4 ^ 2
    - (5383208929591296000 : R) * h ^ 88 * a7 * a5 ^ 4 * a4
    + (598486169231032320 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (598486169231032320 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (299243084615516160 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (626985510622986240 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (786581822417928192 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (786581822417928192 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (1162773128791719936 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (419890296508121088 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 3 * a3 * lambda
    + (339142162564251648 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 2 * a4 ^ 2 * lambda
    + (80748133943869440 : R) * h ^ 87 * a7 * a5 ^ 5 * lambda
    + (23643898043695104 : R) * h ^ 86 * a7 ^ 4 * a4 * b1
    + (47287796087390208 : R) * h ^ 86 * a7 ^ 4 * a3 * b2
    + (70931694131085312 : R) * h ^ 86 * a7 ^ 4 * a2 * b3
    + (94575592174780416 : R) * h ^ 86 * a7 ^ 4 * a1 * b4
    + (118219490218475520 : R) * h ^ 86 * a7 ^ 4 * a0 * b5
    + (11258999068426240 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (22517998136852480 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (33776997205278720 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (45035996273704960 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (56294995342131200 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (67553994410557440 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6
    + (141863388262170624 : R) * h ^ 86 * a7 ^ 3 * a5 ^ 2 * b2
    + (531987705983139840 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (709316941310853120 : R) * h ^ 86 * a7 ^ 3 * a5 * a3 * b4
    + (886646176638566400 : R) * h ^ 86 * a7 ^ 3 * a5 * a2 * b5
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 3 * a5 * a1 * b6
    + (1241304647293992960 : R) * h ^ 86 * a7 ^ 3 * a5 * a0 * b7
    + (780248635441938432 : R) * h ^ 86 * a7 ^ 3 * a4 ^ 2 * b4
    + (1950621588604846080 : R) * h ^ 86 * a7 ^ 3 * a4 * a3 * b5
    + (2340745906325815296 : R) * h ^ 86 * a7 ^ 3 * a4 * a2 * b6
    + (2730870224046784512 : R) * h ^ 86 * a7 ^ 3 * a4 * a1 * b7
    + (3120994541767753728 : R) * h ^ 86 * a7 ^ 3 * a4 * a0 * b8
    + (1170372953162907648 : R) * h ^ 86 * a7 ^ 3 * a3 ^ 2 * b6
    + (2730870224046784512 : R) * h ^ 86 * a7 ^ 3 * a3 * a2 * b7
    + (3120994541767753728 : R) * h ^ 86 * a7 ^ 3 * a3 * a1 * b8
    + (1560497270883876864 : R) * h ^ 86 * a7 ^ 3 * a2 ^ 2 * b8
    + (364791569817010176 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a5 * b2
    + (455989462271262720 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (607985949695016960 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a3 * b4
    + (759982437118771200 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a2 * b5
    + (911978924542525440 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a1 * b6
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a0 * b7
    + (562387003467890688 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 ^ 2 * b3
    + (1823957849085050880 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a4 * b4
    + (2279947311356313600 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a3 * b5
    + (2735936773627576320 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a2 * b6
    + (3191926235898839040 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a1 * b7
    + (3647915698170101760 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a0 * b8
    + (1671961361661296640 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 ^ 2 * b5
    + (4012707267987111936 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a3 * b6
    + (4681491812651630592 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a2 * b7
    + (5350276357316149248 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a1 * b8
    + (2340745906325815296 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 ^ 2 * b7
    + (5350276357316149248 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 * a2 * b8
    + (20266198323167232 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 3 * b4
    + (861313428734607360 : R) * h ^ 86 * a7 * a6 * a5 ^ 3 * b5
    + (3100728343444586496 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a4 * b6
    + (3617516400685350912 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a3 * b7
    + (4134304457926115328 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a2 * b8
    + (3617516400685350912 : R) * h ^ 86 * a7 * a6 * a5 * a4 ^ 2 * b7
    + (1076641785918259200 : R) * h ^ 86 * a7 * a5 ^ 4 * b6
    + (5024328334285209600 : R) * h ^ 86 * a7 * a5 ^ 3 * a4 * b7
    + (2296835809958952960 : R) * h ^ 86 * a7 * a5 ^ 3 * a3 * b8
    + (2411677600456900608 : R) * h ^ 86 * a7 * a5 ^ 2 * a4 ^ 2 * b8
    + (287104476244869120 : R) * h ^ 86 * a5 ^ 5 * b8
    - (1706793890029240320 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    - (1706793890029240320 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    - (853396945014620160 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    + (368908141351403520 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    - (2490525778307973120 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    - (370887262281400320 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    + (188412312535695360 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    + (2826184688035430400 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    + (1884123125356953600 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    + (2449360062964039680 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    + (968977607326433280 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 3 * a0
    + (484488803663216640 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    + (2153283571836518400 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (1480382455637606400 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    - (1480382455637606400 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    + (4575727590152601600 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (933089547795824640 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    + (336450558099456000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 3 * a3
    + (1224680031482019840 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 2 * a4 ^ 2
    + (6056110045790208000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a3
    + (6056110045790208000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 * a4 ^ 2
    + (14467373998276608000 : R) * h ^ 80 * a7 ^ 2 * a6 * a5 ^ 3 * a4
    + (1480382455637606400 : R) * h ^ 80 * a7 ^ 2 * a5 ^ 5
    - (274306160897556480 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (344129547307843584 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (344129547307843584 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (206620225091665920 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (306367919963504640 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (351254382655832064 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (175627191327916032 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (339142162564251648 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (872079846593789952 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (944753167143272448 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (508713243846377472 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (641947664853762048 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    - (302805502289510400 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 ^ 4 * lambda
    - (4925812092436480 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (9851624184872960 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (14777436277309440 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (19703248369745920 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (24629060462182400 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (29554872554618880 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (2111062325329920 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (217017207043915776 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (305576271591505920 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (407435028788674560 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (509293785985843200 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (611152543183011840 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (713011300380180480 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (219444928718045184 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (797981558974709760 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (997476948718387200 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (1196972338462064640 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (1396467728205742080 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (1595963117949419520 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (731483095726817280 : R) * h ^ 78 * a7 ^ 4 * a4 ^ 2 * b5
    - (1755559429744361472 : R) * h ^ 78 * a7 ^ 4 * a4 * a3 * b6
    - (2048152668035088384 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (2340745906325815296 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (1024076334017544192 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (2340745906325815296 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (91197892454252544 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 3 * b2
    - (421790252600918016 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (633318697598976000 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (791648371998720000 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (949978046398464000 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (1108307720798208000 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (1266637395197952000 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (488922034546409472 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (1456633004477644800 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (1747959605373173760 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (2039286206268702720 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (2330612807164231680 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (1086774885079842816 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 ^ 2 * b6
    - (2535808065186299904 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (2898066360212914176 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (1449033180106457088 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (255438541364920320 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 3 * b5
    - (904379100171337728 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a4 * b6
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a3 * b7
    - (1205838800228450304 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (1055108950199894016 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 ^ 2 * b7
    - (968977607326433280 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b5
    - (2325546257583439872 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b6
    - (2713137300514013184 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * b7
    - (3100728343444586496 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a2 * b8
    - (1356568650257006592 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * b7
    - (2906932821979299840 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 3 * b6
    - (10174264876927549440 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a4 * b7
    - (5167880572407644160 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a3 * b8
    - (3617516400685350912 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * a4 ^ 2 * b8
    - (2041133385803366400 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 4 * b7
    - (4593671619917905920 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 3 * a4 * b8
    - (1076641785918259200 : R) * h ^ 78 * a7 * a6 * a5 ^ 4 * b8
    + (498045782033694720 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (1089605028009738240 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (780491077755863040 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    - (207807697649664000 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    + (731483095726817280 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (200880774394675200 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    - (365395201700659200 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    + (235515390669619200 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    - (2001880820691763200 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    - (408226677160673280 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    - (121122200915804160 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    + (1278512120777932800 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (1429914871922688000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (1598140150972416000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (2846371721521397760 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (1974544212846182400 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    - (3028055022895104000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    - (1514027511447552000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    - (14383261358751744000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    - (4359838482038784000 : R) * h ^ 72 * a7 ^ 3 * a6 * a5 ^ 4
    + (133239368809709568 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (134035964984033280 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (153673792411926528 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (76836896205963264 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (93513463942348800 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (630280746971430912 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (132789118798135296 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (275553007083454464 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (148374696121860096 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (218019961648447488 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (708564875357454336 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (190767466442391552 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (1285409357218971648 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (303751769484165120 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (454208253434265600 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda
    + (1231453023109120 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (32879795717013504 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (46410385808424960 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (61880514411233280 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (77350643014041600 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (92820771616849920 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (108290900219658240 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (80537027711336448 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (267933391502966784 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (412659908043866112 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (515824885054832640 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (618989862065799168 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (722154839076765696 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (825319816087732224 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (207253543789264896 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (637276939458969600 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (764732327350763520 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (892187715242557440 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (1019643103134351360 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (475464012222431232 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (1109416028519006208 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (1267904032593149952 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (633952016296574976 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (87635474780258304 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (335025591029858304 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (471030781339238400 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (565236937607086080 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (659443093874933760 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (753649250142781440 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (871604857570590720 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (2187799440855662592 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (2552432680998273024 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (2917065921140883456 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (1346039726909423616 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (1267904032593149952 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (825095515715665920 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (2885063535702835200 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (1507298500285562880 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (1055108950199894016 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (484488803663216640 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (581386564395859968 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (678284325128503296 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (775182085861146624 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (2906932821979299840 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b6
    + (6782843251285032960 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (3875910429305733120 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (1356568650257006592 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (5008627308240568320 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 3 * b7
    + (9205287269601116160 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 2 * a4 * b8
    + (1951413236976844800 : R) * h ^ 70 * a7 ^ 3 * a5 ^ 4 * b8
    + (1614962678877388800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a5 ^ 3 * b8
    - (167210979573104640 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (402454241114849280 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (324266594874163200 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (123494053655347200 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    - (210751640033034240 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (1125018923150868480 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    + (443582847941345280 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (73598559584256000 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    + (462198954189127680 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    - (403740669719347200 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (1061922074001408000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (983276756045660160 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    + (4205106272246169600 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (460954788062822400 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    + (567760316792832000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (6245363484721152000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (4949503132041216000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    - (18743821395296256 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (59598134430400512 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (127373130678140928 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (58095239474184192 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (225601231760916480 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (455176785739382784 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (133490469777702912 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (363319289387679744 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (177141218839363584 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (844827351387734016 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (775308254820433920 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (340656190075699200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (134690174402560 : R) * h ^ 62 * a7 ^ 8 * b1
    - (23701072648339456 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (39396876012748800 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (59317552806887424 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (74146941008609280 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (88976329210331136 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (103805717412052992 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (118635105613774848 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (76865758386192384 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (214842373044174848 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (303014409498787840 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (363617291398545408 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (424220173298302976 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (484823055198060544 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (215080967067402240 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (561496399049392128 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (655079132224290816 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (748661865399189504 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (358087297666646016 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (554708014259503104 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (59017386132504576 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (616595125740503040 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (760576173397770240 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (887338868964065280 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (1014101564530360320 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (1792935128507351040 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (4214132300637536256 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (2696512684702040064 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (1029063718761136128 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (1381534436155195392 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (2602445066899292160 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (90841650686853120 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (1271783109615943680 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (1483746961218600960 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (968977607326433280 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (4513063673706577920 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (6056110045790208000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (4860589062676807680 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    - (1211222009158041600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    + (34793358266204160 : R) * h ^ 56 * a7 ^ 9 * a0
    + (171667480589107200 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (292559686006210560 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (79627147479613440 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (483193097929359360 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (281121758600232960 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    - (120293444026368000 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    - (90618226488115200 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    - (211595858804736000 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (2657565130987929600 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (972913816004198400 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    - (993580554387456000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (2667290654932992000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    + (8175122355585024 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (77626263950327808 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (78585403161968640 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (25945115751088128 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (166346814973280256 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (488383806424743936 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (177976044517588992 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (181399421215309824 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (737910986731683840 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (127746071278387200 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (2308012345655296 : R) * h ^ 54 * a7 ^ 9 * b2
    + (21618829553565696 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (30594873115541504 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (42410568665006080 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (50892682398007296 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (59374796131008512 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (67856909864009728 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (50640756796293120 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (246474772819476480 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (308742865079500800 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (360200009259417600 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (411657153439334400 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (297294887450050560 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (707689114345930752 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (520281205682208768 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (219410294101770240 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (136212998007029760 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (1160939968030310400 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (1360768097480343552 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (972262948070227968 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (2534827472613015552 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (3558429745320296448 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (1210179672134909952 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (204393714045419520 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (1761949516447088640 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7
    + (1302063659844894720 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (4482783123477626880 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (454208253434265600 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    - (24998199479500800 : R) * h ^ 48 * a7 ^ 10 * a1
    - (187424158672486400 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (126344870410321920 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (27011392921927680 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (150480546504376320 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (25946198082846720 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (99234897922621440 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (535068099477504000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (649679784955084800 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (663865578749952000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    - (8360860632219648 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (52309060069883904 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (72465628815949824 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (155549627968389120 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (326603991775444992 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (311114911092572160 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (19161910691758080 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (1978198048899072 : R) * h ^ 46 * a7 ^ 10 * b3
    - (13597432667439104 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (29032647481098240 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (36378252738035712 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (42441294861041664 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (48504336984047616 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (71758209047592960 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (356925955689676800 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (420295127240540160 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (325780313147965440 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (365051595190173696 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (544464826496188416 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (241177531955281920 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (1470523031792123904 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (1133376998228361216 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (2189517255975370752 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (250051106187509760 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7
    - (1814940479347752960 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (68131238015139840 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    + (21677719326556160 : R) * h ^ 40 * a7 ^ 11 * a2
    + (88651223405690880 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (88529326194032640 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (31550840493834240 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (242395990185738240 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    - (135025839518515200 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (57441375800524800 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (5329839162654720 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (44568258967240704 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (41298106427375616 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (195928601672024064 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (49235464971878400 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (1171532055314432 : R) * h ^ 38 * a7 ^ 11 * b4
    + (15584974686126080 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (35682110480056320 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (42080985491177472 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (34568819523452928 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (106067127215063040 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (410665262686142464 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (330549294509588480 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (291241078969860096 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (273637685745156096 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (1278422287241969664 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (272761518859223040 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (11192613973524480 : R) * h ^ 32 * a7 ^ 12 * a3
    - (57342865692426240 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (61544098871377920 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (182665177328517120 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (3443943014400000 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (4214592733446144 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (47749713792860160 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (38761806981758976 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (1197421698744320 : R) * h ^ 30 * a7 ^ 12 * b5
    - (20369798772817920 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (37895869768400896 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (31690547995344896 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (111910660840882176 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (329135919288287232 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (243013301909323776 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (7718165198929920 : R) * h ^ 24 * a7 ^ 13 * a4
    + (75888907182407680 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (44617285396070400 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (4039798400483328 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (13587094401712128 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (1440126169251840 : R) * h ^ 22 * a7 ^ 13 * b6
    + (20174094393671680 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (28808032636895232 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (90606592529006592 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (7981281637826560 : R) * h ^ 16 * a7 ^ 14 * a5
    - (23188659638108160 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (2224398476574720 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (1350888785182720 : R) * h ^ 14 * a7 ^ 14 * b7
    - (15410896599777280 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (4549179262566400 : R) * h ^ 8 * a7 ^ 15 * a6
    + (139032053379072 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (989028220665856 : R) * h ^ 6 * a7 ^ 15 * b8
    - (315961928826880 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Combined integer polynomial of compact-block expansions `18`–`20`. -/
def degreeZeroExpansionGroup6810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6485183463413514240 : R) * h ^ 112 * a5 * a2 * a0
    + (3242591731706757120 : R) * h ^ 112 * a5 * a1 ^ 2
    - (576460752303423488 : R) * h ^ 110 * a5 * a3 * b1
    - (1152921504606846976 : R) * h ^ 110 * a5 * a2 * b2
    - (1729382256910270464 : R) * h ^ 110 * a5 * a1 * b3
    - (2305843009213693952 : R) * h ^ 110 * a5 * a0 * b4
    - (4863887597560135680 : R) * h ^ 104 * a7 * a6 * a2 * a0
    - (2431943798780067840 : R) * h ^ 104 * a7 * a6 * a1 ^ 2
    - (2431943798780067840 : R) * h ^ 104 * a7 * a5 * a3 * a0
    - (2431943798780067840 : R) * h ^ 104 * a7 * a5 * a2 * a1
    - (6890507429876858880 : R) * h ^ 104 * a5 ^ 2 * a4 * a1
    - (6890507429876858880 : R) * h ^ 104 * a5 ^ 2 * a3 * a2
    - (6890507429876858880 : R) * h ^ 104 * a5 * a4 ^ 2 * a2
    - (6890507429876858880 : R) * h ^ 104 * a5 * a4 * a3 ^ 2
    - (2296835809958952960 : R) * h ^ 104 * a4 ^ 3 * a3
    + (1459166279268040704 : R) * h ^ 103 * a7 * a5 * a4 * a0 * lambda
    + (1459166279268040704 : R) * h ^ 103 * a7 * a5 * a3 * a1 * lambda
    + (729583139634020352 : R) * h ^ 103 * a7 * a5 * a2 ^ 2 * lambda
    + (432345564227567616 : R) * h ^ 102 * a7 * a6 * a3 * b1
    + (864691128455135232 : R) * h ^ 102 * a7 * a6 * a2 * b2
    + (1297036692682702848 : R) * h ^ 102 * a7 * a6 * a1 * b3
    + (1729382256910270464 : R) * h ^ 102 * a7 * a6 * a0 * b4
    + (288230376151711744 : R) * h ^ 102 * a7 * a5 * a4 * b1
    + (576460752303423488 : R) * h ^ 102 * a7 * a5 * a3 * b2
    + (864691128455135232 : R) * h ^ 102 * a7 * a5 * a2 * b3
    + (1152921504606846976 : R) * h ^ 102 * a7 * a5 * a1 * b4
    + (1441151880758558720 : R) * h ^ 102 * a7 * a5 * a0 * b5
    + (972777519512027136 : R) * h ^ 102 * a5 ^ 2 * a4 * b3
    + (1297036692682702848 : R) * h ^ 102 * a5 ^ 2 * a3 * b4
    + (1621295865853378560 : R) * h ^ 102 * a5 ^ 2 * a2 * b5
    + (1945555039024054272 : R) * h ^ 102 * a5 ^ 2 * a1 * b6
    + (2269814212194729984 : R) * h ^ 102 * a5 ^ 2 * a0 * b7
    + (1297036692682702848 : R) * h ^ 102 * a5 * a4 ^ 2 * b4
    + (3242591731706757120 : R) * h ^ 102 * a5 * a4 * a3 * b5
    + (3891110078048108544 : R) * h ^ 102 * a5 * a4 * a2 * b6
    + (4539628424389459968 : R) * h ^ 102 * a5 * a4 * a1 * b7
    + (5188146770730811392 : R) * h ^ 102 * a5 * a4 * a0 * b8
    + (1945555039024054272 : R) * h ^ 102 * a5 * a3 ^ 2 * b6
    + (4539628424389459968 : R) * h ^ 102 * a5 * a3 * a2 * b7
    + (5188146770730811392 : R) * h ^ 102 * a5 * a3 * a1 * b8
    + (2594073385365405696 : R) * h ^ 102 * a5 * a2 ^ 2 * b8
    + (1418633882621706240 : R) * h ^ 96 * a7 ^ 3 * a2 * a0
    + (709316941310853120 : R) * h ^ 96 * a7 ^ 3 * a1 ^ 2
    + (1823957849085050880 : R) * h ^ 96 * a7 ^ 2 * a6 * a3 * a0
    + (1823957849085050880 : R) * h ^ 96 * a7 ^ 2 * a6 * a2 * a1
    - (3039929748475084800 : R) * h ^ 96 * a7 ^ 2 * a5 * a4 * a0
    - (3039929748475084800 : R) * h ^ 96 * a7 ^ 2 * a5 * a3 * a1
    - (1519964874237542400 : R) * h ^ 96 * a7 ^ 2 * a5 * a2 ^ 2
    + (10335761144815288320 : R) * h ^ 96 * a7 * a6 * a5 * a4 * a1
    + (10335761144815288320 : R) * h ^ 96 * a7 * a6 * a5 * a3 * a2
    + (5167880572407644160 : R) * h ^ 96 * a7 * a6 * a4 ^ 2 * a2
    + (5167880572407644160 : R) * h ^ 96 * a7 * a6 * a4 * a3 ^ 2
    + (4306567143673036800 : R) * h ^ 96 * a7 * a5 ^ 3 * a1
    + (13781014859753717760 : R) * h ^ 96 * a7 * a5 ^ 2 * a4 * a2
    + (6890507429876858880 : R) * h ^ 96 * a7 * a5 ^ 2 * a3 ^ 2
    + (13781014859753717760 : R) * h ^ 96 * a7 * a5 * a4 ^ 2 * a3
    + (1148417904979476480 : R) * h ^ 96 * a7 * a4 ^ 4
    - (1094374709451030528 : R) * h ^ 95 * a7 ^ 2 * a6 * a4 * a0 * lambda
    - (1094374709451030528 : R) * h ^ 95 * a7 ^ 2 * a6 * a3 * a1 * lambda
    - (547187354725515264 : R) * h ^ 95 * a7 ^ 2 * a6 * a2 ^ 2 * lambda
    - (1231171548132409344 : R) * h ^ 95 * a7 ^ 2 * a5 ^ 2 * a0 * lambda
    - (1550364171722293248 : R) * h ^ 95 * a7 ^ 2 * a5 * a4 * a1 * lambda
    - (1550364171722293248 : R) * h ^ 95 * a7 ^ 2 * a5 * a3 * a2 * lambda
    - (1550364171722293248 : R) * h ^ 95 * a7 * a5 ^ 2 * a4 * a3 * lambda
    - (516788057240764416 : R) * h ^ 95 * a7 * a5 * a4 ^ 3 * lambda
    - (126100789566373888 : R) * h ^ 94 * a7 ^ 3 * a3 * b1
    - (252201579132747776 : R) * h ^ 94 * a7 ^ 3 * a2 * b2
    - (378302368699121664 : R) * h ^ 94 * a7 ^ 3 * a1 * b3
    - (504403158265495552 : R) * h ^ 94 * a7 ^ 3 * a0 * b4
    - (216172782113783808 : R) * h ^ 94 * a7 ^ 2 * a6 * a4 * b1
    - (432345564227567616 : R) * h ^ 94 * a7 ^ 2 * a6 * a3 * b2
    - (648518346341351424 : R) * h ^ 94 * a7 ^ 2 * a6 * a2 * b3
    - (864691128455135232 : R) * h ^ 94 * a7 ^ 2 * a6 * a1 * b4
    - (1080863910568919040 : R) * h ^ 94 * a7 ^ 2 * a6 * a0 * b5
    - (90071992547409920 : R) * h ^ 94 * a7 ^ 2 * a5 ^ 2 * b1
    - (180143985094819840 : R) * h ^ 94 * a7 ^ 2 * a5 * a4 * b2
    - (270215977642229760 : R) * h ^ 94 * a7 ^ 2 * a5 * a3 * b3
    - (360287970189639680 : R) * h ^ 94 * a7 ^ 2 * a5 * a2 * b4
    - (450359962737049600 : R) * h ^ 94 * a7 ^ 2 * a5 * a1 * b5
    - (540431955284459520 : R) * h ^ 94 * a7 ^ 2 * a5 * a0 * b6
    - (1459166279268040704 : R) * h ^ 94 * a7 * a6 * a5 * a4 * b3
    - (1945555039024054272 : R) * h ^ 94 * a7 * a6 * a5 * a3 * b4
    - (2431943798780067840 : R) * h ^ 94 * a7 * a6 * a5 * a2 * b5
    - (2918332558536081408 : R) * h ^ 94 * a7 * a6 * a5 * a1 * b6
    - (3404721318292094976 : R) * h ^ 94 * a7 * a6 * a5 * a0 * b7
    - (972777519512027136 : R) * h ^ 94 * a7 * a6 * a4 ^ 2 * b4
    - (2431943798780067840 : R) * h ^ 94 * a7 * a6 * a4 * a3 * b5
    - (2918332558536081408 : R) * h ^ 94 * a7 * a6 * a4 * a2 * b6
    - (3404721318292094976 : R) * h ^ 94 * a7 * a6 * a4 * a1 * b7
    - (3891110078048108544 : R) * h ^ 94 * a7 * a6 * a4 * a0 * b8
    - (1459166279268040704 : R) * h ^ 94 * a7 * a6 * a3 ^ 2 * b6
    - (3404721318292094976 : R) * h ^ 94 * a7 * a6 * a3 * a2 * b7
    - (3891110078048108544 : R) * h ^ 94 * a7 * a6 * a3 * a1 * b8
    - (1945555039024054272 : R) * h ^ 94 * a7 * a6 * a2 ^ 2 * b8
    - (607985949695016960 : R) * h ^ 94 * a7 * a5 ^ 3 * b3
    - (2756202971950743552 : R) * h ^ 94 * a7 * a5 ^ 2 * a4 * b4
    - (3445253714938429440 : R) * h ^ 94 * a7 * a5 ^ 2 * a3 * b5
    - (4134304457926115328 : R) * h ^ 94 * a7 * a5 ^ 2 * a2 * b6
    - (4823355200913801216 : R) * h ^ 94 * a7 * a5 ^ 2 * a1 * b7
    - (5512405943901487104 : R) * h ^ 94 * a7 * a5 ^ 2 * a0 * b8
    - (2431943798780067840 : R) * h ^ 94 * a7 * a5 * a4 ^ 2 * b5
    - (5836665117072162816 : R) * h ^ 94 * a7 * a5 * a4 * a3 * b6
    - (6809442636584189952 : R) * h ^ 94 * a7 * a5 * a4 * a2 * b7
    - (7782220156096217088 : R) * h ^ 94 * a7 * a5 * a4 * a1 * b8
    - (3404721318292094976 : R) * h ^ 94 * a7 * a5 * a3 ^ 2 * b7
    - (7782220156096217088 : R) * h ^ 94 * a7 * a5 * a3 * a2 * b8
    - (5512405943901487104 : R) * h ^ 94 * a5 ^ 2 * a4 * a3 * b8
    - (1837468647967162368 : R) * h ^ 94 * a5 * a4 ^ 3 * b8
    - (531987705983139840 : R) * h ^ 88 * a7 ^ 4 * a3 * a0
    - (531987705983139840 : R) * h ^ 88 * a7 ^ 4 * a2 * a1
    + (2279947311356313600 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    + (2279947311356313600 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    + (1139973655678156800 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    + (3217258983802798080 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    + (1266637395197952000 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    + (1266637395197952000 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    - (1507298500285562880 : R) * h ^ 88 * a7 ^ 3 * a4 ^ 2 * a2
    - (1507298500285562880 : R) * h ^ 88 * a7 ^ 3 * a4 * a3 ^ 2
    - (3875910429305733120 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    - (3875910429305733120 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    - (8074813394386944000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 ^ 2 * a1
    - (17441596931875799040 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    - (8720798465937899520 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    - (8720798465937899520 : R) * h ^ 88 * a7 ^ 2 * a6 * a4 ^ 2 * a3
    - (4844888036632166400 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 3 * a2
    - (10766417859182592000 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 2 * a4 * a3
    - (3588805953060864000 : R) * h ^ 88 * a7 ^ 2 * a5 * a4 ^ 3
    + (319192623589883904 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (319192623589883904 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (159596311794941952 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (1504765225495166976 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (1162773128791719936 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (1162773128791719936 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (860680110037008384 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (980377343883214848 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (490188671941607424 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (2325546257583439872 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (387591042930573312 : R) * h ^ 87 * a7 ^ 2 * a6 * a4 ^ 3 * lambda
    + (968977607326433280 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 3 * a3 * lambda
    + (1744159693187579904 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 2 * a4 ^ 2 * lambda
    + (63050394783186944 : R) * h ^ 86 * a7 ^ 4 * a4 * b1
    + (126100789566373888 : R) * h ^ 86 * a7 ^ 4 * a3 * b2
    + (189151184349560832 : R) * h ^ 86 * a7 ^ 4 * a2 * b3
    + (252201579132747776 : R) * h ^ 86 * a7 ^ 4 * a1 * b4
    + (315251973915934720 : R) * h ^ 86 * a7 ^ 4 * a0 * b5
    + (90071992547409920 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (135107988821114880 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (202661983231672320 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (270215977642229760 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (337769972052787200 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (405323966463344640 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6
    + (45035996273704960 : R) * h ^ 86 * a7 ^ 3 * a5 ^ 2 * b2
    + (493144159197069312 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (657525545596092416 : R) * h ^ 86 * a7 ^ 3 * a5 * a3 * b4
    + (821906931995115520 : R) * h ^ 86 * a7 ^ 3 * a5 * a2 * b5
    + (986288318394138624 : R) * h ^ 86 * a7 ^ 3 * a5 * a1 * b6
    + (1150669704793161728 : R) * h ^ 86 * a7 ^ 3 * a5 * a0 * b7
    + (283726776524341248 : R) * h ^ 86 * a7 ^ 3 * a4 ^ 2 * b4
    + (709316941310853120 : R) * h ^ 86 * a7 ^ 3 * a4 * a3 * b5
    + (851180329573023744 : R) * h ^ 86 * a7 ^ 3 * a4 * a2 * b6
    + (993043717835194368 : R) * h ^ 86 * a7 ^ 3 * a4 * a1 * b7
    + (1134907106097364992 : R) * h ^ 86 * a7 ^ 3 * a4 * a0 * b8
    + (425590164786511872 : R) * h ^ 86 * a7 ^ 3 * a3 ^ 2 * b6
    + (993043717835194368 : R) * h ^ 86 * a7 ^ 3 * a3 * a2 * b7
    + (1134907106097364992 : R) * h ^ 86 * a7 ^ 3 * a3 * a1 * b8
    + (567453553048682496 : R) * h ^ 86 * a7 ^ 3 * a2 ^ 2 * b8
    + (547187354725515264 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (729583139634020352 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a3 * b4
    + (911978924542525440 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a2 * b5
    + (1094374709451030528 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a1 * b6
    + (1276770494359535616 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a0 * b7
    + (1139973655678156800 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 ^ 2 * b3
    + (3526318508231098368 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a4 * b4
    + (4407898135288872960 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a3 * b5
    + (5289477762346647552 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a2 * b6
    + (6171057389404422144 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a1 * b7
    + (7052637016462196736 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a0 * b8
    + (1823957849085050880 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 ^ 2 * b5
    + (4377498837804122112 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a3 * b6
    + (5107081977438142464 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a2 * b7
    + (5836665117072162816 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a1 * b8
    + (2553540988719071232 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 ^ 2 * b7
    + (5836665117072162816 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 * a2 * b8
    + (1013309916158361600 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 3 * b4
    + (3242591731706757120 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a4 * b5
    + (3891110078048108544 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a3 * b6
    + (4539628424389459968 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a2 * b7
    + (5188146770730811392 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a1 * b8
    + (2371145203810566144 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 ^ 2 * b6
    + (5532672142224654336 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a3 * b7
    + (6323053876828176384 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a2 * b8
    + (3161526938414088192 : R) * h ^ 86 * a7 ^ 2 * a5 * a3 ^ 2 * b8
    + (8268608915852230656 : R) * h ^ 86 * a7 * a6 * a5 * a4 * a3 * b8
    + (1378101485975371776 : R) * h ^ 86 * a7 * a6 * a4 ^ 3 * b8
    + (3445253714938429440 : R) * h ^ 86 * a7 * a5 ^ 3 * a3 * b8
    + (6201456686889172992 : R) * h ^ 86 * a7 * a5 ^ 2 * a4 ^ 2 * b8
    - (664984632478924800 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    - (664984632478924800 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    - (332492316239462400 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    - (4042156587425464320 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    - (949978046398464000 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    - (949978046398464000 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    - (356043855306424320 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    + (1825936970015047680 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    + (912968485007523840 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    + (2425808523897077760 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    + (4844888036632166400 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    + (5329376840295383040 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (2664688420147691520 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    + (7940233171147161600 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    + (10228096966223462400 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (1704682827703910400 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    + (1233652046364672000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 3 * a3
    + (1130473875214172160 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 2 * a4 ^ 2
    - (416169549159727104 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (339142162564251648 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (339142162564251648 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (436039923296894976 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (984652245092007936 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (735283007912411136 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (367641503956205568 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (436396165064294400 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (1152085875769737216 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (113047387521417216 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (872079846593789952 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (1816833013737062400 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (2252872937033957376 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (1332344210073845760 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    - (23643898043695104 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (39406496739491840 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (59109745109237760 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (78812993478983680 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (98516241848729600 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (118219490218475520 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (16888498602639360 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (43628621390151680 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (369858119397801984 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (493144159197069312 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (616430198996336640 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (739716238795603968 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (863002278594871296 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (330645136704798720 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (1003880504438554624 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (1254850630548193280 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (1505820756657831936 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (1756790882767470592 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (2007761008877109248 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (531987705983139840 : R) * h ^ 78 * a7 ^ 4 * a4 ^ 2 * b5
    - (1276770494359535616 : R) * h ^ 78 * a7 ^ 4 * a4 * a3 * b6
    - (1489565576752791552 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (1702360659146047488 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (744782788376395776 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (1702360659146047488 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (683984193406894080 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (1094374709451030528 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (1367968386813788160 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (1641562064176545792 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (1915155741539303424 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (2188749418902061056 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (1684627735613276160 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (3850577681401774080 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (4620693217682128896 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (5390808753962483712 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (6160924290242838528 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (1778358902857924608 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 ^ 2 * b6
    - (4149504106668490752 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (4742290407621132288 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (2371145203810566144 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (886646176638566400 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 3 * b5
    - (2447143447522443264 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a4 * b6
    - (2855000688776183808 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a3 * b7
    - (3262857930029924352 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (1613696041482190848 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 ^ 2 * b7
    - (6100125695273336832 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 * a3 * b8
    - (401946266742816768 : R) * h ^ 78 * a7 ^ 3 * a4 ^ 3 * b8
    - (3100728343444586496 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 * a3 * b8
    - (6459850715509555200 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a3 * b8
    - (8010214887231848448 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * a4 ^ 2 * b8
    - (4737223858040340480 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 3 * a4 * b8
    + (1129319388005007360 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (606798477137018880 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (606798477137018880 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    + (1221909262180024320 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    + (363663470886912000 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (662906555502428160 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    - (331453277751214080 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    - (682301940616396800 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    - (1000247718020382720 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    - (427852959716474880 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    - (908416506868531200 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (4113108072765849600 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (1993469556739276800 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (765425019676262400 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    + (314581271822991360 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    + (1157950670792294400 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    + (237316390715916288 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (266928987630993408 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (214457543974453248 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (107228771987226624 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (254356621923188736 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (480035781570723840 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (864064406827302912 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (685141979150942208 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (726599614832050176 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (1090099808242237440 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (708564875357454336 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (2240760716942376960 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (277571710432051200 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (7881299347898368 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (11452513114914816 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (61326360550834176 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (81768480734445568 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (102210600918056960 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (122652721101668352 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (143094841285279744 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (7388718138654720 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (388092420232839168 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (619913451833131008 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (774891814791413760 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (929870177749696512 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (1084848540707979264 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (1239826903666262016 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (453359430457622528 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (1057818146850734080 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (1269381776220880896 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (1480945405591027712 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (1692509034961174528 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (518688013333561344 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (1210272031111643136 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (1383168035556163584 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (691584017778081792 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (128247036263792640 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (888229473382563840 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (1063975411966279680 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (1276770494359535616 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (1489565576752791552 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (1702360659146047488 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (1363614320767795200 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (2772985917437116416 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (3235150237009969152 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (3697314556582821888 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (1210272031111643136 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (4575094271455002624 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (548612321795112960 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (1396467728205742080 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (3385880087038525440 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (3106586541397377024 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (3875910429305733120 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (2519341779048726528 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (7967149215795118080 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 2 * a4 * b8
    + (986921637091737600 : R) * h ^ 70 * a7 ^ 3 * a5 ^ 4 * b8
    - (675548190442782720 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (459815762735923200 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (260019381684142080 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (130009690842071040 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    - (72472934555320320 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (557574028756254720 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (269154261726658560 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    - (535104821447884800 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    - (556924629701099520 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (662387036258304000 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    - (302805502289510400 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    - (556405110456975360 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2
    - (2763941334787031040 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    - (422315544281088000 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    - (32123606595010560 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (133178758231228416 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (128889013615460352 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (177831437263699968 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (114553993329377280 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (790578409745940480 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (465463266773041152 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (665971719042760704 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (204393714045419520 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (1197974268432875520 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (558297644846284800 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (862017116176384 : R) * h ^ 62 * a7 ^ 8 * b1
    - (3355709487972352 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (54600647923728384 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (87710241570947072 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (109637801963683840 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (131565362356420608 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (153492922749157376 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (175420483141894144 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (105081425778180096 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (469322140269674496 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (571702065978408960 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (686042479174090752 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (800382892369772544 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (914723305565454336 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (356274752748257280 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (750462865445486592 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (875540009686401024 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (1000617153927315456 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (352996009074229248 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (1070625258291068928 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (146059124633763840 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (653109906898944000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (703221248846462976 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (820424790320873472 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (937628331795283968 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (798040932602609664 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (1530295885492125696 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (3868548099446145024 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (2047321437244489728 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (270565622339862528 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (2788779302458490880 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (726733205494824960 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (4259464065539112960 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (1985058292786790400 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    + (93087746783969280 : R) * h ^ 56 * a7 ^ 9 * a0
    + (230307828722565120 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (149588331473141760 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (246074213432033280 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (117184059502755840 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (961691968402882560 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (629289331080560640 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (1043411108553031680 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    + (166779593057894400 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    + (1830448747260149760 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    + (964316365219430400 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3
    + (17205827966337024 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (58482095768469504 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (133047138958442496 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (75482899175964672 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (207541444037050368 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (700055428452581376 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (154363778908028928 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (200135511669473280 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (400980723734937600 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (350194453446656 : R) * h ^ 54 * a7 ^ 9 * b2
    + (28262671514075136 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (61597012209958912 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (76234638711848960 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (91481566454218752 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (106728494196588544 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (121975421938958336 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (112562502893568000 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (332570656442941440 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (366468874805182464 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (427547020606046208 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (488625166406909952 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (204933024498843648 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (410668417608056832 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (757841687979491328 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (382816413686956032 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (96853230511718400 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (354401184934526976 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (362208817003364352 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (996853525625438208 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (377248899120758784 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (2943492133358665728 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (625079782094143488 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (711592930380349440 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (1425709239946444800 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    - (38468325558190080 : R) * h ^ 48 * a7 ^ 10 * a1
    - (72425026879488000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (235231928196792320 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (134666761462087680 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (314618332022046720 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (1271893178890321920 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (296865900747816960 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    - (350986273617346560 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    - (759806558208000000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    - (7312233361047552 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (65299829143633920 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (100950506100228096 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (169062114772647936 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (216549507653959680 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (121092630065971200 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (2486116049485824 : R) * h ^ 46 * a7 ^ 10 * b3
    - (28590386108694528 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (41904900690411520 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (47064114190614528 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (54908133222383616 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (62752152254152704 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (71752410841743360 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (175759081183641600 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (184537564839936000 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (365457049229721600 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (95759618021523456 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (480458174424416256 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (48348687369240576 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (157479270875136000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (705169446011928576 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (874050308869718016 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (430551573567897600 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    + (14657654001500160 : R) * h ^ 40 * a7 ^ 11 * a2
    + (126808938774528000 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (207450025523937280 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (336023616875397120 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (446852915244564480 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (245567426081587200 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    + (6461748903149568 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (46552325283643392 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (28885113542541312 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (95023675509571584 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (12974210364211200 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (2387240533622784 : R) * h ^ 38 * a7 ^ 11 * b4
    + (17486438580879360 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (21463294292262912 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (23010553576292352 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (39821510839369728 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (34727658151477248 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (76483702791602176 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (217961805643776000 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (128982221921976320 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (20051819325554688 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (379935439819112448 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (46130525739417600 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (14371120108011520 : R) * h ^ 32 * a7 ^ 12 * a3
    - (101231100658974720 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (63821256033566720 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (205919283912376320 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (27671846820249600 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (4161487924887552 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (24439832243601408 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (13125437538435072 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (1399388257648640 : R) * h ^ 30 * a7 ^ 12 * b5
    - (8180518310903808 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (9098656221233152 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (21239808084934656 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (14038550370582528 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (107107018388537344 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (51828915475316736 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (9663942557696000 : R) * h ^ 24 * a7 ^ 13 * a4
    + (55831609451479040 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (29470485381120000 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (2054361044090880 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (4889630078926848 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (631345747329024 : R) * h ^ 22 * a7 ^ 13 * b6
    + (3212450736373760 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (9674348113690624 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (20947247025881088 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (4892655314534400 : R) * h ^ 16 * a7 ^ 14 * a5
    - (11437753641861120 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (794083858219008 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (240237280231424 : R) * h ^ 14 * a7 ^ 14 * b7
    - (3625068778225664 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (1918887555235840 : R) * h ^ 8 * a7 ^ 15 * a6
    + (47425100599296 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (227478164078592 : R) * h ^ 6 * a7 ^ 15 * b8
    - (117583398768640 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Combined integer polynomial of compact-block expansions `21`–`23`. -/
def degreeZeroExpansionGroup7810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (4611686018427387904 : R) * h ^ 118 * a0 * b1
    + (6485183463413514240 : R) * h ^ 112 * a4 * a3 * a0
    + (6485183463413514240 : R) * h ^ 112 * a4 * a2 * a1
    + (3242591731706757120 : R) * h ^ 112 * a3 ^ 2 * a1
    + (3242591731706757120 : R) * h ^ 112 * a3 * a2 ^ 2
    - (1297036692682702848 : R) * h ^ 111 * a7 * a1 * a0 * lambda
    - (576460752303423488 : R) * h ^ 110 * a7 * a1 * b1
    - (1152921504606846976 : R) * h ^ 110 * a7 * a0 * b2
    - (288230376151711744 : R) * h ^ 110 * a4 ^ 2 * b1
    - (1152921504606846976 : R) * h ^ 110 * a4 * a3 * b2
    - (1729382256910270464 : R) * h ^ 110 * a4 * a2 * b3
    - (2305843009213693952 : R) * h ^ 110 * a4 * a1 * b4
    - (2882303761517117440 : R) * h ^ 110 * a4 * a0 * b5
    - (864691128455135232 : R) * h ^ 110 * a3 ^ 2 * b3
    - (2305843009213693952 : R) * h ^ 110 * a3 * a2 * b4
    - (2882303761517117440 : R) * h ^ 110 * a3 * a1 * b5
    - (3458764513820540928 : R) * h ^ 110 * a3 * a0 * b6
    - (1441151880758558720 : R) * h ^ 110 * a2 ^ 2 * b5
    - (3458764513820540928 : R) * h ^ 110 * a2 * a1 * b6
    - (4035225266123964416 : R) * h ^ 110 * a2 * a0 * b7
    - (2017612633061982208 : R) * h ^ 110 * a1 ^ 2 * b7
    - (4611686018427387904 : R) * h ^ 110 * a1 * a0 * b8
    + (3242591731706757120 : R) * h ^ 104 * a7 ^ 2 * a1 * a0
    - (4053239664633446400 : R) * h ^ 104 * a7 * a5 * a3 * a0
    - (4053239664633446400 : R) * h ^ 104 * a7 * a5 * a2 * a1
    - (3242591731706757120 : R) * h ^ 104 * a7 * a4 ^ 2 * a0
    - (6485183463413514240 : R) * h ^ 104 * a7 * a4 * a3 * a1
    - (3242591731706757120 : R) * h ^ 104 * a7 * a4 * a2 ^ 2
    - (3242591731706757120 : R) * h ^ 104 * a7 * a3 ^ 2 * a2
    + (891712726219358208 : R) * h ^ 103 * a7 ^ 2 * a2 * a0 * lambda
    + (445856363109679104 : R) * h ^ 103 * a7 ^ 2 * a1 ^ 2 * lambda
    + (729583139634020352 : R) * h ^ 103 * a7 * a4 ^ 2 * a1 * lambda
    + (1459166279268040704 : R) * h ^ 103 * a7 * a4 * a3 * a2 * lambda
    + (243194379878006784 : R) * h ^ 103 * a7 * a3 ^ 3 * lambda
    + (72057594037927936 : R) * h ^ 102 * a7 ^ 2 * a2 * b1
    + (144115188075855872 : R) * h ^ 102 * a7 ^ 2 * a1 * b2
    + (216172782113783808 : R) * h ^ 102 * a7 ^ 2 * a0 * b3
    + (360287970189639680 : R) * h ^ 102 * a7 * a5 * a4 * b1
    + (720575940379279360 : R) * h ^ 102 * a7 * a5 * a3 * b2
    + (1080863910568919040 : R) * h ^ 102 * a7 * a5 * a2 * b3
    + (1441151880758558720 : R) * h ^ 102 * a7 * a5 * a1 * b4
    + (1801439850948198400 : R) * h ^ 102 * a7 * a5 * a0 * b5
    + (648518346341351424 : R) * h ^ 102 * a7 * a4 ^ 2 * b2
    + (1945555039024054272 : R) * h ^ 102 * a7 * a4 * a3 * b3
    + (2594073385365405696 : R) * h ^ 102 * a7 * a4 * a2 * b4
    + (3242591731706757120 : R) * h ^ 102 * a7 * a4 * a1 * b5
    + (3891110078048108544 : R) * h ^ 102 * a7 * a4 * a0 * b6
    + (1297036692682702848 : R) * h ^ 102 * a7 * a3 ^ 2 * b4
    + (3242591731706757120 : R) * h ^ 102 * a7 * a3 * a2 * b5
    + (3891110078048108544 : R) * h ^ 102 * a7 * a3 * a1 * b6
    + (4539628424389459968 : R) * h ^ 102 * a7 * a3 * a0 * b7
    + (1945555039024054272 : R) * h ^ 102 * a7 * a2 ^ 2 * b6
    + (4539628424389459968 : R) * h ^ 102 * a7 * a2 * a1 * b7
    + (5188146770730811392 : R) * h ^ 102 * a7 * a2 * a0 * b8
    + (2594073385365405696 : R) * h ^ 102 * a7 * a1 ^ 2 * b8
    + (540431955284459520 : R) * h ^ 102 * a4 ^ 3 * b5
    + (1945555039024054272 : R) * h ^ 102 * a4 ^ 2 * a3 * b6
    + (2269814212194729984 : R) * h ^ 102 * a4 ^ 2 * a2 * b7
    + (2594073385365405696 : R) * h ^ 102 * a4 ^ 2 * a1 * b8
    + (2269814212194729984 : R) * h ^ 102 * a4 * a3 ^ 2 * b7
    + (5188146770730811392 : R) * h ^ 102 * a4 * a3 * a2 * b8
    + (864691128455135232 : R) * h ^ 102 * a3 ^ 3 * b8
    - (2702159776422297600 : R) * h ^ 96 * a7 ^ 3 * a2 * a0
    - (1351079888211148800 : R) * h ^ 96 * a7 ^ 3 * a1 ^ 2
    + (1519964874237542400 : R) * h ^ 96 * a7 ^ 2 * a6 * a3 * a0
    + (1519964874237542400 : R) * h ^ 96 * a7 ^ 2 * a6 * a2 * a1
    + (3039929748475084800 : R) * h ^ 96 * a7 ^ 2 * a5 * a4 * a0
    + (3039929748475084800 : R) * h ^ 96 * a7 ^ 2 * a5 * a3 * a1
    + (1519964874237542400 : R) * h ^ 96 * a7 ^ 2 * a5 * a2 ^ 2
    - (415457065624928256 : R) * h ^ 95 * a7 ^ 3 * a3 * a0 * lambda
    - (415457065624928256 : R) * h ^ 95 * a7 ^ 3 * a2 * a1 * lambda
    - (911978924542525440 : R) * h ^ 95 * a7 ^ 2 * a5 * a4 * a1 * lambda
    - (911978924542525440 : R) * h ^ 95 * a7 ^ 2 * a5 * a3 * a2 * lambda
    - (1231171548132409344 : R) * h ^ 95 * a7 ^ 2 * a4 ^ 2 * a2 * lambda
    - (1231171548132409344 : R) * h ^ 95 * a7 ^ 2 * a4 * a3 ^ 2 * lambda
    - (9007199254740992 : R) * h ^ 94 * a7 ^ 3 * a3 * b1
    - (18014398509481984 : R) * h ^ 94 * a7 ^ 3 * a2 * b2
    - (27021597764222976 : R) * h ^ 94 * a7 ^ 3 * a1 * b3
    - (36028797018963968 : R) * h ^ 94 * a7 ^ 3 * a0 * b4
    - (135107988821114880 : R) * h ^ 94 * a7 ^ 2 * a6 * a4 * b1
    - (270215977642229760 : R) * h ^ 94 * a7 ^ 2 * a6 * a3 * b2
    - (405323966463344640 : R) * h ^ 94 * a7 ^ 2 * a6 * a2 * b3
    - (540431955284459520 : R) * h ^ 94 * a7 ^ 2 * a6 * a1 * b4
    - (675539944105574400 : R) * h ^ 94 * a7 ^ 2 * a6 * a0 * b5
    - (112589990684262400 : R) * h ^ 94 * a7 ^ 2 * a5 ^ 2 * b1
    - (630503947831869440 : R) * h ^ 94 * a7 ^ 2 * a5 * a4 * b2
    - (945755921747804160 : R) * h ^ 94 * a7 ^ 2 * a5 * a3 * b3
    - (1261007895663738880 : R) * h ^ 94 * a7 ^ 2 * a5 * a2 * b4
    - (1576259869579673600 : R) * h ^ 94 * a7 ^ 2 * a5 * a1 * b5
    - (1891511843495608320 : R) * h ^ 94 * a7 ^ 2 * a5 * a0 * b6
    - (607985949695016960 : R) * h ^ 94 * a7 ^ 2 * a4 ^ 2 * b3
    - (1621295865853378560 : R) * h ^ 94 * a7 ^ 2 * a4 * a3 * b4
    - (2026619832316723200 : R) * h ^ 94 * a7 ^ 2 * a4 * a2 * b5
    - (2431943798780067840 : R) * h ^ 94 * a7 ^ 2 * a4 * a1 * b6
    - (2837267765243412480 : R) * h ^ 94 * a7 ^ 2 * a4 * a0 * b7
    - (1013309916158361600 : R) * h ^ 94 * a7 ^ 2 * a3 ^ 2 * b5
    - (2431943798780067840 : R) * h ^ 94 * a7 ^ 2 * a3 * a2 * b6
    - (2837267765243412480 : R) * h ^ 94 * a7 ^ 2 * a3 * a1 * b7
    - (3242591731706757120 : R) * h ^ 94 * a7 ^ 2 * a3 * a0 * b8
    - (1418633882621706240 : R) * h ^ 94 * a7 ^ 2 * a2 ^ 2 * b7
    - (3242591731706757120 : R) * h ^ 94 * a7 ^ 2 * a2 * a1 * b8
    - (1013309916158361600 : R) * h ^ 94 * a7 * a5 * a4 ^ 2 * b5
    - (2431943798780067840 : R) * h ^ 94 * a7 * a5 * a4 * a3 * b6
    - (2837267765243412480 : R) * h ^ 94 * a7 * a5 * a4 * a2 * b7
    - (3242591731706757120 : R) * h ^ 94 * a7 * a5 * a4 * a1 * b8
    - (1418633882621706240 : R) * h ^ 94 * a7 * a5 * a3 ^ 2 * b7
    - (3242591731706757120 : R) * h ^ 94 * a7 * a5 * a3 * a2 * b8
    - (1378101485975371776 : R) * h ^ 94 * a7 * a4 ^ 3 * b6
    - (4823355200913801216 : R) * h ^ 94 * a7 * a4 ^ 2 * a3 * b7
    - (5512405943901487104 : R) * h ^ 94 * a7 * a4 ^ 2 * a2 * b8
    - (5512405943901487104 : R) * h ^ 94 * a7 * a4 * a3 ^ 2 * b8
    + (1060808818478284800 : R) * h ^ 88 * a7 ^ 4 * a3 * a0
    + (1060808818478284800 : R) * h ^ 88 * a7 ^ 4 * a2 * a1
    - (1013309916158361600 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    - (1013309916158361600 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    - (506654958079180800 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    - (633318697598976000 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    + (886646176638566400 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    + (886646176638566400 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    + (2583940286203822080 : R) * h ^ 88 * a7 ^ 3 * a4 ^ 2 * a2
    + (2583940286203822080 : R) * h ^ 88 * a7 ^ 3 * a4 * a3 ^ 2
    + (156429718306947072 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (156429718306947072 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda
    + (78214859153473536 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (341992096703447040 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (341992096703447040 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (284993413919539200 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (1310969704029880320 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (655484852014940160 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (1145673523956547584 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (30680772461461504 : R) * h ^ 86 * a7 ^ 4 * a4 * b1
    + (61361544922923008 : R) * h ^ 86 * a7 ^ 4 * a3 * b2
    + (92042317384384512 : R) * h ^ 86 * a7 ^ 4 * a2 * b3
    + (122723089845846016 : R) * h ^ 86 * a7 ^ 4 * a1 * b4
    + (153403862307307520 : R) * h ^ 86 * a7 ^ 4 * a0 * b5
    + (84442493013196800 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (213920982300098560 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (320881473450147840 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (427841964600197120 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (534802455750246400 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (641762946900295680 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6
    + (140737488355328000 : R) * h ^ 86 * a7 ^ 3 * a5 ^ 2 * b2
    + (489766459476541440 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (653021945968721920 : R) * h ^ 86 * a7 ^ 3 * a5 * a3 * b4
    + (816277432460902400 : R) * h ^ 86 * a7 ^ 3 * a5 * a2 * b5
    + (979532918953082880 : R) * h ^ 86 * a7 ^ 3 * a5 * a1 * b6
    + (1142788405445263360 : R) * h ^ 86 * a7 ^ 3 * a5 * a0 * b7
    + (371546969258065920 : R) * h ^ 86 * a7 ^ 3 * a4 ^ 2 * b4
    + (928867423145164800 : R) * h ^ 86 * a7 ^ 3 * a4 * a3 * b5
    + (1114640907774197760 : R) * h ^ 86 * a7 ^ 3 * a4 * a2 * b6
    + (1300414392403230720 : R) * h ^ 86 * a7 ^ 3 * a4 * a1 * b7
    + (1486187877032263680 : R) * h ^ 86 * a7 ^ 3 * a4 * a0 * b8
    + (557320453887098880 : R) * h ^ 86 * a7 ^ 3 * a3 ^ 2 * b6
    + (1300414392403230720 : R) * h ^ 86 * a7 ^ 3 * a3 * a2 * b7
    + (1486187877032263680 : R) * h ^ 86 * a7 ^ 3 * a3 * a1 * b8
    + (743093938516131840 : R) * h ^ 86 * a7 ^ 3 * a2 ^ 2 * b8
    + (379991218559385600 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 ^ 2 * b5
    + (911978924542525440 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a3 * b6
    + (1063975411966279680 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a2 * b7
    + (1215971899390033920 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a1 * b8
    + (531987705983139840 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 ^ 2 * b7
    + (1215971899390033920 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 * a2 * b8
    + (633318697598976000 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a4 * b5
    + (759982437118771200 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a3 * b6
    + (886646176638566400 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a2 * b7
    + (1013309916158361600 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a1 * b8
    + (2279947311356313600 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 ^ 2 * b6
    + (5319877059831398400 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a3 * b7
    + (6079859496950169600 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a2 * b8
    + (3039929748475084800 : R) * h ^ 86 * a7 ^ 2 * a5 * a3 ^ 2 * b8
    + (1808758200342675456 : R) * h ^ 86 * a7 ^ 2 * a4 ^ 3 * b7
    + (6201456686889172992 : R) * h ^ 86 * a7 ^ 2 * a4 ^ 2 * a3 * b8
    - (346741986935439360 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    - (346741986935439360 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    - (173370993467719680 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    + (395824185999360000 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    - (435406604599296000 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    - (435406604599296000 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    - (474989023199232000 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    - (3111178101954969600 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    - (1555589050977484800 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    - (3068429089867038720 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    - (48686374877921280 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (125713761473396736 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (125713761473396736 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (213745060439654400 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (463114297619251200 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (231557148809625600 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (338429679029452800 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (1075850137546260480 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (258275281364582400 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (18612532834992128 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (45106365017882624 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (67659547526823936 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (90212730035765248 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (112765912544706560 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (135319095053647872 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (15832967439974400 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (91479367430963200 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (151996487423754240 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3
    - (202661983231672320 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (253327479039590400 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (303992974847508480 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (354658470655426560 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (89720148826521600 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (258956978573803520 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (323696223217254400 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (388435467860705280 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (453174712504156160 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (517913957147607040 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (257285720899584000 : R) * h ^ 78 * a7 ^ 4 * a4 ^ 2 * b5
    - (617485730159001600 : R) * h ^ 78 * a7 ^ 4 * a4 * a3 * b6
    - (720400018518835200 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (823314306878668800 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (360200009259417600 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (823314306878668800 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (474989023199232000 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (569986827839078400 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (664984632478924800 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (759982437118771200 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (816981119902679040 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 ^ 2 * b6
    - (1906289279772917760 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (2178616319740477440 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (1089308159870238720 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (131941395333120000 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 3 * b5
    - (1234971460318003200 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a4 * b6
    - (1440800037037670400 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a3 * b7
    - (1646628613757337600 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (2682104684331663360 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 ^ 2 * b7
    - (6130524992758087680 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 * a3 * b8
    - (1636495514595753984 : R) * h ^ 78 * a7 ^ 3 * a4 ^ 3 * b8
    + (99780680220672000 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (292580044151193600 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (292580044151193600 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    - (59373627899904000 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0
    + (400771988324352000 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    + (1144723545910149120 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    + (572361772955074560 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    + (875761011523584000 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    + (3035773594522091520 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    + (767107272466759680 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    + (13052302533328896 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (61194419155501056 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (113665862812041216 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (56832931406020608 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (40077198832435200 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (236010170902118400 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (360694789491916800 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (242689704040857600 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (328410379321344000 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (6944515441033216 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (18814842974502912 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (30623597856817152 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (40831463809089536 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (51039329761361920 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (61247195713634304 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (71455061665906688 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (14513553486643200 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (52776558133248000 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (74309393851613184 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (92886742314516480 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (111464090777419776 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (130041439240323072 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (148618787703226368 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (41341637204377600 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (212183753928212480 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (254620504713854976 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (297057255499497472 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (339494006285139968 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (243313127133806592 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (567730629978882048 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (648835005690150912 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (324417502845075456 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (89060441849856000 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (106872530219827200 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (124684618589798400 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (142496706959769600 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (148434069749760000 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (878729692918579200 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (1025184641738342400 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (1171639590558105600 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (919895408262512640 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (2102618076028600320 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (217703302299648000 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6
    + (1288407725427916800 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (1472465971917619200 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (2203949067644436480 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    - (25703833078333440 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (146203435534909440 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (304784623219507200 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (152392311609753600 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    - (82257213652992000 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    - (629484150797107200 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    - (1039211661329694720 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    - (716070691484467200 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    - (1009252718251868160 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    - (2439575783866368 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (21179067852128256 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (53973720137465856 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (79218644550156288 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (40912140474777600 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (159752167568179200 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (105085755105214464 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (133451505834393600 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (759556376363008 : R) * h ^ 62 * a7 ^ 8 * b1
    - (5892282813251584 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (10339257591791616 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (14392607207587840 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (17990759009484800 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (21588910811381760 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (25187062613278720 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (28785214415175680 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (7504166859571200 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (22474017671741440 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (67980055166320640 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (81576066199584768 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (95172077232848896 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (108768088266113024 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (48055530081484800 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (226579659670683648 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6
    - (264342936282464256 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (302106212894244864 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (216945463910203392 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (495875346080464896 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (55662776156160000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (155855773237248000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (181831735443456000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (207807697649664000 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (230072808112128000 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (872792330128588800 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (997476948718387200 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (724833249402028032 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (199149043580928000 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (955915409188454400 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    + (6996673523875840 : R) * h ^ 56 * a7 ^ 9 * a0
    + (51221350475366400 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (150334592778240000 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (234165181800775680 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    + (112129570190131200 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    + (480338834463129600 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    + (327977446617907200 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    + (423408183961190400 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    + (2577167208677376 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (18250355422789632 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (34028433180721152 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (21965014655041536 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (26057137088102400 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (83626363327610880 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (17249662402560000 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (593959617298432 : R) * h ^ 54 * a7 ^ 9 * b2
    + (2887042656632832 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (4228721720426496 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (9684163410001920 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (11620996092002304 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (13557828774002688 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (15494661456003072 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (2943942383370240 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (32289564131328000 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (76350774627532800 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (89075903732121600 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (101801032836710400 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (54138234564771840 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (195043398443335680 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (222906741078097920 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (157016032882458624 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (6957847019520000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (80711025426432000 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (146980652816793600 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (167977888933478400 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (199149043580928000 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (618574246670499840 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (132766029053952000 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    - (6748263352893440 : R) * h ^ 48 * a7 ^ 10 * a1
    - (51660081384652800 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (104054199523737600 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (69429628103557120 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    - (79815202622668800 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    - (269390441978265600 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    - (56416542916608000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    - (1994170898055168 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (10961208584699904 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (17149706165551104 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (12958555208417280 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (15826927642214400 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (274889718104064 : R) * h ^ 46 * a7 ^ 10 * b3
    - (1085217976614912 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (4105435757936640 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (8875616489177088 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (10354885904039936 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (11834155318902784 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (5540185689292800 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (36798506698014720 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (64355446365880320 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (73549081561006080 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (42941061550571520 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (130502409490268160 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (9393093476352000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (65886945804288000 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (99271468898058240 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (126354501874483200 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    + (5775583451545600 : R) * h ^ 40 * a7 ^ 11 * a2
    + (34051818069688320 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (55804978496798720 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    + (42394548436992000 : R) * h ^ 40 * a7 ^ 9 * a6 ^ 2 * a4
    + (52554696228864000 : R) * h ^ 40 * a7 ^ 9 * a6 * a5 ^ 2
    + (1142264822759424 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (5266822630735872 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (3191291730984960 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (4777812217036800 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (98819144417280 : R) * h ^ 38 * a7 ^ 11 * b4
    + (1345266301009920 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (4082503048495104 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (6925462295019520 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (7914814051450880 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (6267876629544960 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (28014954980311040 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (41414651648409600 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (26118361846906880 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (7204270768128000 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (39682920834662400 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    - (3590949322096640 : R) * h ^ 32 * a7 ^ 12 * a3
    - (17391768777523200 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (10690219737088000 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (16113274454016000 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    - (532032714178560 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (1910072527552512 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (473856108134400 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (103239164887040 : R) * h ^ 30 * a7 ^ 12 * b5
    - (1367237373984768 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (2946699064508416 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (4283699046645760 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (4540681905242112 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (16252176649158656 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (4107384599347200 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (1772094163517440 : R) * h ^ 24 * a7 ^ 13 * a4
    + (6496503233249280 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (1623724130304000 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (189918712037376 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (281654233399296 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (97981698146304 : R) * h ^ 22 * a7 ^ 13 * b6
    + (946045861232640 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (1653722128056320 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (2501063542308864 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (651253280276480 : R) * h ^ 16 * a7 ^ 14 * a5
    - (973213374873600 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (55523301507072 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (65251722461184 : R) * h ^ 14 * a7 ^ 14 * b7
    - (504861435101184 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (193434983956480 : R) * h ^ 8 * a7 ^ 15 * a6
    + (3630577595904 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (33800365211648 : R) * h ^ 6 * a7 ^ 15 * b8
    - (12752198502400 : R) * a7 ^ 17

end DegreeZeroCompactExpansions810

/-! ## Block-by-block `2^{34} · compact(bars / integers)` -/

section DegreeZeroCompactBlockClearing810

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock0_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock0_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock0Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock0_810,
    degreeZeroCompactBlock0Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock1_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock1_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock1Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock1_810,
    degreeZeroCompactBlock1Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock2_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock2_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock2Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock2_810,
    degreeZeroCompactBlock2Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock3_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock3_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock3Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock3_810,
    degreeZeroCompactBlock3Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock4_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock4_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock4Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock4_810,
    degreeZeroCompactBlock4Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock5_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock5_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock5Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock5_810,
    degreeZeroCompactBlock5Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock6_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock6_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock6Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock6_810,
    degreeZeroCompactBlock6Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock7_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock7_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock7Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock7_810,
    degreeZeroCompactBlock7Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock8_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock8_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock8Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock8_810,
    degreeZeroCompactBlock8Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock9_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock9_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock9Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock9_810,
    degreeZeroCompactBlock9Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock10_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock10_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock10Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock10_810,
    degreeZeroCompactBlock10Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock11_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock11_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock11Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock11_810,
    degreeZeroCompactBlock11Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock12_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock12_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock12Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock12_810,
    degreeZeroCompactBlock12Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock13_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock13_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock13Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock13_810,
    degreeZeroCompactBlock13Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock14_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock14_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock14Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock14_810,
    degreeZeroCompactBlock14Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock15_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock15_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock15Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock15_810,
    degreeZeroCompactBlock15Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock16_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock16_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock16Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock16_810,
    degreeZeroCompactBlock16Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock17_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock17_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock17Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock17_810,
    degreeZeroCompactBlock17Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock18_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock18_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock18Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock18_810,
    degreeZeroCompactBlock18Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock19_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock19_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock19Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock19_810,
    degreeZeroCompactBlock19Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock20_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock20_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock20Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock20_810,
    degreeZeroCompactBlock20Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock21_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock21_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock21Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock21_810,
    degreeZeroCompactBlock21Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock22_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock22_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock22Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock22_810,
    degreeZeroCompactBlock22Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

set_option maxHeartbeats 800000000 in
theorem degreeZeroCompactBlock23_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock23_810
        (degreeZeroLBar810 h lambda / 4)
        (degreeZeroABar810 h a7 a6 / 16)
        (degreeZeroBBar810 h a7 a6 a5 / 32)
        (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
        (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
        (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (degreeZeroPBar810 h a7 b8 lambda / 64)
        (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
        (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
        (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
        (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
        (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
        (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock23Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [degreeZeroCompactBlock23_810,
    degreeZeroCompactBlock23Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

#print axioms degreeZeroCompactBlock0_eq_expansion
#print axioms degreeZeroCompactBlock23_eq_expansion

set_option maxHeartbeats 800000000 in
/-- Sum of the 24 compact-block expansions. -/
theorem degreeZeroCompact_eq_sum_expansions
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
        degreeZeroClearedCompact810
          (degreeZeroLBar810 h lambda / 4)
          (degreeZeroABar810 h a7 a6 / 16)
          (degreeZeroBBar810 h a7 a6 a5 / 32)
          (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
          (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
          (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
          (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
          (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
          (degreeZeroPBar810 h a7 b8 lambda / 64)
          (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
          (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
          (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
          (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
          (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
          (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
          (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864) =
      degreeZeroCompactBlock0Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock1Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock2Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock3Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock4Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock5Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock6Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock7Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock8Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock9Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock10Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock11Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock12Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock13Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock14Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock15Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock16Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock17Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock18Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock19Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock20Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock21Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock22Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock23Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have hsum :=
    degreeZeroCompact810_blockSum
      (degreeZeroLBar810 h lambda / 4)
      (degreeZeroABar810 h a7 a6 / 16)
      (degreeZeroBBar810 h a7 a6 a5 / 32)
      (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
      (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
      (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
      (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
      (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
      (degreeZeroPBar810 h a7 b8 lambda / 64)
      (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
      (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
      (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
      (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
      (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
      (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
      (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)
  have hb0 :=
    degreeZeroCompactBlock0_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb1 :=
    degreeZeroCompactBlock1_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb2 :=
    degreeZeroCompactBlock2_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb3 :=
    degreeZeroCompactBlock3_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb4 :=
    degreeZeroCompactBlock4_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb5 :=
    degreeZeroCompactBlock5_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb6 :=
    degreeZeroCompactBlock6_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb7 :=
    degreeZeroCompactBlock7_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb8 :=
    degreeZeroCompactBlock8_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb9 :=
    degreeZeroCompactBlock9_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb10 :=
    degreeZeroCompactBlock10_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb11 :=
    degreeZeroCompactBlock11_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb12 :=
    degreeZeroCompactBlock12_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb13 :=
    degreeZeroCompactBlock13_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb14 :=
    degreeZeroCompactBlock14_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb15 :=
    degreeZeroCompactBlock15_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb16 :=
    degreeZeroCompactBlock16_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb17 :=
    degreeZeroCompactBlock17_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb18 :=
    degreeZeroCompactBlock18_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb19 :=
    degreeZeroCompactBlock19_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb20 :=
    degreeZeroCompactBlock20_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb21 :=
    degreeZeroCompactBlock21_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb22 :=
    degreeZeroCompactBlock22_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb23 :=
    degreeZeroCompactBlock23_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  rw [hsum, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add]
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23]

#print axioms degreeZeroCompact_eq_sum_expansions

end DegreeZeroCompactBlockClearing810

/-! ## Source numerator equals the grouped expansions -/

section DegreeZeroSourceEqExpansion810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup0810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup0810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock0Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock1Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock2Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup0810, degreeZeroCompactBlock0Expansion810, degreeZeroCompactBlock1Expansion810, degreeZeroCompactBlock2Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup1810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup1810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock3Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock4Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock5Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup1810, degreeZeroCompactBlock3Expansion810, degreeZeroCompactBlock4Expansion810, degreeZeroCompactBlock5Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup2810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup2810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock6Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock7Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock8Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup2810, degreeZeroCompactBlock6Expansion810, degreeZeroCompactBlock7Expansion810, degreeZeroCompactBlock8Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup3810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup3810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock9Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock10Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock11Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup3810, degreeZeroCompactBlock9Expansion810, degreeZeroCompactBlock10Expansion810, degreeZeroCompactBlock11Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup4810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup4810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock12Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock13Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock14Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup4810, degreeZeroCompactBlock12Expansion810, degreeZeroCompactBlock13Expansion810, degreeZeroCompactBlock14Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup5810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup5810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock15Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock16Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock17Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup5810, degreeZeroCompactBlock15Expansion810, degreeZeroCompactBlock16Expansion810, degreeZeroCompactBlock17Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup6810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup6810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock18Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock19Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock20Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup6810, degreeZeroCompactBlock18Expansion810, degreeZeroCompactBlock19Expansion810, degreeZeroCompactBlock20Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup7810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup7810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock21Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock22Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock23Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup7810, degreeZeroCompactBlock21Expansion810, degreeZeroCompactBlock22Expansion810, degreeZeroCompactBlock23Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
/-- The `977`-term source is the sum of the eight expansion groups. -/
theorem degreeZeroClearedSource810_eq_sum_groups
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSource810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
        b3 b2 b1 lambda =
      degreeZeroExpansionGroup0810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup1810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup2810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup3810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup4810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup5810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup6810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup7810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroClearedSource810, degreeZeroClearedSourceBlock0_810, degreeZeroClearedSourceBlock1_810, degreeZeroClearedSourceBlock2_810, degreeZeroClearedSourceBlock3_810, degreeZeroClearedSourceBlock4_810, degreeZeroClearedSourceBlock5_810, degreeZeroClearedSourceBlock6_810, degreeZeroClearedSourceBlock7_810, degreeZeroClearedSourceBlock8_810, degreeZeroClearedSourceBlock9_810, degreeZeroClearedSourceBlock10_810, degreeZeroClearedSourceBlock11_810, degreeZeroClearedSourceBlock12_810, degreeZeroClearedSourceBlock13_810, degreeZeroClearedSourceBlock14_810, degreeZeroClearedSourceBlock15_810, degreeZeroClearedSourceBlock16_810, degreeZeroClearedSourceBlock17_810, degreeZeroClearedSourceBlock18_810, degreeZeroClearedSourceBlock19_810, degreeZeroClearedSourceBlock20_810, degreeZeroClearedSourceBlock21_810, degreeZeroClearedSourceBlock22_810, degreeZeroClearedSourceBlock23_810, degreeZeroClearedSourceBlock24_810,
    degreeZeroExpansionGroup0810, degreeZeroExpansionGroup1810, degreeZeroExpansionGroup2810, degreeZeroExpansionGroup3810, degreeZeroExpansionGroup4810, degreeZeroExpansionGroup5810, degreeZeroExpansionGroup6810, degreeZeroExpansionGroup7810]
  ring

#print axioms degreeZeroClearedSource810_eq_sum_groups

set_option maxHeartbeats 800000000 in
theorem degreeZeroClearedSource810_eq_sum_expansions
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSource810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
        b3 b2 b1 lambda =
      degreeZeroCompactBlock0Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock1Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock2Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock3Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock4Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock5Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock6Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock7Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock8Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock9Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock10Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock11Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock12Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock13Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock14Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock15Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock16Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock17Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock18Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock19Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock20Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock21Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock22Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock23Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have hsrc :=
    degreeZeroClearedSource810_eq_sum_groups h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg0 := degreeZeroExpansionGroup0810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg1 := degreeZeroExpansionGroup1810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg2 := degreeZeroExpansionGroup2810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg3 := degreeZeroExpansionGroup3810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg4 := degreeZeroExpansionGroup4810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg5 := degreeZeroExpansionGroup5810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg6 := degreeZeroExpansionGroup6810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg7 := degreeZeroExpansionGroup7810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  rw [hsrc, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7]

#print axioms degreeZeroClearedSource810_eq_sum_expansions

end DegreeZeroSourceEqExpansion810


/-! ## Field identity `source = 2^{34} · compact(bars)` then `2^{62} h^{119} ρ` -/

section DegreeZeroSourceRho810

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
theorem degreeZeroClearedSource810_eq_scaledCompact
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    degreeZeroClearedSource810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
        b3 b2 b1 lambda =
      (degreeZeroCompactToSourceIntegerScale810 : F) *
        degreeZeroClearedCompact810
          (degreeZeroLBar810 h lambda / 4)
          (degreeZeroABar810 h a7 a6 / 16)
          (degreeZeroBBar810 h a7 a6 a5 / 32)
          (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
          (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
          (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
          (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
          (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
          (degreeZeroPBar810 h a7 b8 lambda / 64)
          (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
          (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
          (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
          (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
          (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
          (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
          (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda /
            67108864) := by
  have hsrc :=
    degreeZeroClearedSource810_eq_sum_expansions h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hexp :=
    degreeZeroCompact_eq_sum_expansions h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7
      b6 b5 b4 b3 b2 b1 lambda
  rw [hsrc, ← hexp]

set_option maxHeartbeats 800000000 in
/-- Algebraic clearing of the degree-zero primitive against `h^{119}`
on the ninth-power face. -/
theorem degreeZeroClearedSource810_eq_scaledSourceRho
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    degreeZeroClearedSource810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
        b3 b2 b1 lambda =
      (degreeZeroClearedIntegerScale810 : F) *
        h ^ degreeZeroSourceClearingPower810 *
          sourceRhoResidual810 h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5
            b4 b3 b2 b1 := by
  have hcompact :=
    degreeZeroClearedSource810_eq_scaledCompact h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hL := degreeZeroScaledDepressedL810 h a7 b9 lambda hh hN
  have hA := degreeZeroScaledDepressedA810 h a7 a6 hh
  have hB := degreeZeroScaledDepressedB810 h a7 a6 a5 hh
  have hC := degreeZeroScaledDepressedC810 h a7 a6 a5 a4 hh
  have hD0 := degreeZeroScaledDepressedD810 h a7 a6 a5 a4 a3 hh
  have hE0 := degreeZeroScaledDepressedE810 h a7 a6 a5 a4 a3 a2 hh
  have hF0 := degreeZeroScaledDepressedF810 h a7 a6 a5 a4 a3 a2 a1 hh
  have hG0 := degreeZeroScaledDepressedG810 h a7 a6 a5 a4 a3 a2 a1 a0 hh
  have hP := degreeZeroScaledDepressedP810 h a7 b9 b8 lambda hh hN
  have hQ := degreeZeroScaledDepressedQ810 h a7 b9 b8 b7 lambda hh hN
  have hR := degreeZeroScaledDepressedR810 h a7 b9 b8 b7 b6 lambda hh hN
  have hS := degreeZeroScaledDepressedS810 h a7 b9 b8 b7 b6 b5 lambda hh
    hN
  have hT0 := degreeZeroScaledDepressedT810 h a7 b9 b8 b7 b6 b5 b4 lambda
    hh hN
  have hU0 := degreeZeroScaledDepressedU810 h a7 b9 b8 b7 b6 b5 b4 b3
    lambda hh hN
  have hV0 := degreeZeroScaledDepressedV810 h a7 b9 b8 b7 b6 b5 b4 b3 b2
    lambda hh hN
  have hW0 := degreeZeroScaledDepressedW810 h a7 b9 b8 b7 b6 b5 b4 b3 b2
    b1 lambda hh hN
  have hcoords :
      degreeZeroClearedCompact810
          (degreeZeroLBar810 h lambda / 4)
          (degreeZeroABar810 h a7 a6 / 16)
          (degreeZeroBBar810 h a7 a6 a5 / 32)
          (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
          (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
          (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
          (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
          (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
          (degreeZeroPBar810 h a7 b8 lambda / 64)
          (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
          (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
          (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
          (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
          (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
          (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
          (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda /
            67108864) =
        degreeZeroClearedCompact810
          (h ^ 7 * depressedL810 h (octicDepressionR810 h a7) b9)
          (h ^ 14 * depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (h ^ 21 * depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (h ^ 28 * depressedC810 h (octicDepressionR810 h a7) a7 a6 a5
            a4)
          (h ^ 35 * depressedD810 h (octicDepressionR810 h a7) a7 a6 a5
            a4 a3)
          (h ^ 42 * depressedE810 h (octicDepressionR810 h a7) a7 a6 a5
            a4 a3 a2)
          (h ^ 49 * depressedF810 h (octicDepressionR810 h a7) a7 a6 a5
            a4 a3 a2 a1)
          (h ^ 56 * depressedG810 h (octicDepressionR810 h a7) a7 a6 a5
            a4 a3 a2 a1 a0)
          (h ^ 14 * depressedP810 h (octicDepressionR810 h a7) b9 b8)
          (h ^ 21 * depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
          (h ^ 28 * depressedR810 h (octicDepressionR810 h a7) b9 b8 b7
            b6)
          (h ^ 35 * depressedS810 h (octicDepressionR810 h a7) b9 b8 b7
            b6 b5)
          (h ^ 42 * depressedT810 h (octicDepressionR810 h a7) b9 b8 b7
            b6 b5 b4)
          (h ^ 49 * depressedU810 h (octicDepressionR810 h a7) b9 b8 b7
            b6 b5 b4 b3)
          (h ^ 56 * depressedV810 h (octicDepressionR810 h a7) b9 b8 b7
            b6 b5 b4 b3 b2)
          (h ^ 63 * depressedW810 h (octicDepressionR810 h a7) b9 b8 b7
            b6 b5 b4 b3 b2 b1) := by
    simp only [degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810,
      degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810,
      degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810,
      degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810,
      degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810,
      degreeZeroWBar810]
    rw [hL, hA, hB, hC, hD0, hE0, hF0, hG0, hP, hQ, hR, hS, hT0, hU0,
      hV0, hW0]
  have hwt := degreeZeroClearedCompact810_weightedScale h
    (depressedL810 h (octicDepressionR810 h a7) b9)
    (depressedA810 h (octicDepressionR810 h a7) a7 a6)
    (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
    (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
    (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
    (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
    (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1)
    (depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 a0)
    (depressedP810 h (octicDepressionR810 h a7) b9 b8)
    (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
    (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
    (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
    (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4)
    (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3)
    (depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2)
    (depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2
      b1)
  have hrho := rhoResidual810_eq_clearedCompact
    (depressedL810 h (octicDepressionR810 h a7) b9)
    (depressedA810 h (octicDepressionR810 h a7) a7 a6)
    (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
    (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
    (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
    (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
    (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1)
    (depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 a0)
    (depressedP810 h (octicDepressionR810 h a7) b9 b8)
    (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
    (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
    (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
    (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4)
    (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3)
    (depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2)
    (depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2
      b1)
  have hscale :
      (degreeZeroCompactToSourceIntegerScale810 : F) *
          (degreeZeroGroupedIntegerScale810 : F) =
        (degreeZeroClearedIntegerScale810 : F) := by
    simp only [degreeZeroClearedIntegerScale810_eq_grouped_mul_compact]
    ring
  rw [hcompact, hcoords, hwt, hrho, sourceRhoResidual810]
  simp only [degreeZeroSourceClearingPower810]
  rw [← mul_assoc, hscale]
  ac_rfl

#print axioms degreeZeroClearedSource810_eq_scaledCompact
#print axioms degreeZeroClearedSource810_eq_scaledSourceRho

end DegreeZeroSourceRho810

/-! ## Left-jet restriction and remaining-`17` clearing -/

section DegreeZeroLeftJetIdentity810

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
theorem degreeZeroClearedSource810_leftJet_eq_scaledLeftJet
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0) :
    degreeZeroClearedSource810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
        a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3
        b2 b1 lambda =
      (degreeZeroClearedIntegerScale810 : F) *
        h ^ degreeZeroSourceClearingPower810 *
          sourceRhoResidualLeftJet810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 lambda := by
  have hN := degreeZeroLeftJet_ninthPower810 h t0 lambda
  have hsrc := degreeZeroClearedSource810_eq_scaledSourceRho h
    (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0
    ((5 * (h ^ 6 * t0) * h ^ 2 - lambda * h ^ 9) / 4)
    (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda hh hN
  simpa [sourceRhoResidualLeftJet810] using hsrc

set_option maxHeartbeats 800000000 in
theorem degreeZeroSourceJetQuotient810_eq_scaledLeftJet
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0) :
    degreeZeroSourceJetQuotient810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroEffectiveTowerLength810 *
        ((degreeZeroClearedIntegerScale810 : F) *
          sourceRhoResidualLeftJet810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 lambda) := by
  have hfact := degreeZeroClearedSource810_leftJet_factored h t0 v1 u1
    a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hsrc := degreeZeroClearedSource810_leftJet_eq_scaledLeftJet h t0
    v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda hh
  have hhpow : h ^ degreeZeroSourceBaseOrder810 ≠ 0 :=
    pow_ne_zero degreeZeroSourceBaseOrder810 hh
  apply mul_left_cancel₀ hhpow
  calc
    h ^ degreeZeroSourceBaseOrder810 *
          degreeZeroSourceJetQuotient810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda =
        degreeZeroClearedSource810 h (h ^ 6 * t0) (h ^ 4 * v1)
          (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda := hfact.symm
    _ = (degreeZeroClearedIntegerScale810 : F) *
          h ^ degreeZeroSourceClearingPower810 *
            sourceRhoResidualLeftJet810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
              w1 b62 b5 b4 b3 b2 b1 lambda := hsrc
    _ = h ^ degreeZeroSourceBaseOrder810 *
          (h ^ degreeZeroEffectiveTowerLength810 *
            ((degreeZeroClearedIntegerScale810 : F) *
              sourceRhoResidualLeftJet810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
                w1 b62 b5 b4 b3 b2 b1 lambda)) := by
      simp only [degreeZeroSourceBaseOrder810,
        degreeZeroEffectiveTowerLength810,
        degreeZeroSourceClearingPower810]
      ring

#print axioms degreeZeroClearedSource810_leftJet_eq_scaledLeftJet
#print axioms degreeZeroSourceJetQuotient810_eq_scaledLeftJet

end DegreeZeroLeftJetIdentity810

section DegreeZeroAlgebraMapClearing810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
theorem degreeZeroSourceJetQuotient810_algebraMap_eq_pow_scaledLeftJet
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda : k) (hh0 : h0 ≠ 0) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
      (algebraMap k[X] (RatFunc k) h0) ^
          degreeZeroEffectiveTowerLength810 *
        ((degreeZeroClearedIntegerScale810 : RatFunc k) *
          sourceRhoResidualLeftJet810
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) t0)
            (algebraMap k[X] (RatFunc k) v1)
            (algebraMap k[X] (RatFunc k) u1)
            (algebraMap k[X] (RatFunc k) a4)
            (algebraMap k[X] (RatFunc k) a3)
            (algebraMap k[X] (RatFunc k) a2)
            (algebraMap k[X] (RatFunc k) a1)
            (algebraMap k[X] (RatFunc k) a0)
            (algebraMap k[X] (RatFunc k) s1)
            (algebraMap k[X] (RatFunc k) w1)
            (algebraMap k[X] (RatFunc k) b62)
            (algebraMap k[X] (RatFunc k) b5)
            (algebraMap k[X] (RatFunc k) b4)
            (algebraMap k[X] (RatFunc k) b3)
            (algebraMap k[X] (RatFunc k) b2)
            (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
  let phi : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)
  have hhRF : phi h0 ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hfield := degreeZeroSourceJetQuotient810_eq_scaledLeftJet
    (phi h0) (phi t0) (phi v1) (phi u1) (phi a4) (phi a3) (phi a2)
    (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5) (phi b4)
    (phi b3) (phi b2) (phi b1) (RatFunc.C lambda) hhRF
  have hmap := degreeZeroSourceJetQuotient810_map phi h0 t0 v1 u1 a4 a3
    a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)
  rw [hmap]
  simpa [phi, RatFunc.algebraMap_C] using hfield

#print axioms degreeZeroSourceJetQuotient810_algebraMap_eq_pow_scaledLeftJet

end DegreeZeroAlgebraMapClearing810

/-! ## Linear-root False and the nonzero-face exclusion -/

section DegreeZeroLinearRootFalse810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- Source-facing contradiction at a linear root of `h₀`.  Clearing is
the block identity; the simple pole is the scaled left jet; the ceiling
is order `118`. -/
theorem degreeZeroFace810_linearRoot
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hj : j ≠ 0) : False := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, _hq9d, _hq6, _hsplit⟩ :=
    nonzeroFace810_linearRoot_fifteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  have ha6 : p.coeff 6 = h0 ^ 4 * v1 := by
    rw [hv0, hv1]
    ring
  have ha5 : p.coeff 5 = h0 ^ 2 * u1 := by
    rw [hu0, hu1]
    ring
  have hb8 : q.coeff 8 = h0 ^ 6 * s1 := by
    rw [hs0, hs1]
    ring
  have hb7 : q.coeff 7 = h0 ^ 4 * w1 := by
    rw [hw0, hw1]
    ring
  have hclear :=
    degreeZeroSourceJetQuotient810_algebraMap_eq_pow_scaledLeftJet
      h0 t0 v1 u1 (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
      (p.coeff 0) s1 w1 b62 (q.coeff 5) (q.coeff 4) (q.coeff 3)
      (q.coeff 2) (q.coeff 1) lambda hh0
  have hderiv :=
    sourceRhoResidualLeftJet810_deriv_eq_simplePole_of_source p q H h0
      j lambda t0 v1 u1 s1 w1 b62 hp hq hh0 hH hp8 hq10 hN hD ht0 ha6
      ha5 hb8 hb7 hb62
  have hscale_ne : (degreeZeroClearedIntegerScale810 : k) ≠ 0 := by
    rw [degreeZeroClearedIntegerScale810_eq]
    norm_num
  exact degreeZeroFace810_linearRoot_order118Ceiling h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda ((degreeZeroClearedIntegerScale810 : k) * j) a hh0
    hh0degree hroot hclear hderiv (mul_ne_zero hscale_ne hj)

#print axioms degreeZeroFace810_linearRoot

end DegreeZeroLinearRootFalse810

section NonzeroFaceExclusion810

variable {K : Type*} [Field K] [CharZero K]

/-- Polynomial-level linear-root False implies the source-facing
nonzero-face exclusion. -/
theorem normalized810ScaleTwo_nonzeroFace_false :
    PlaneKeller810NonzeroFaceExclusion (K := K) :=
  normalized810ScaleTwo_nonzeroFace_false_of_linearRootFalse
    degreeZeroFace810_linearRoot

/-- **CLOSED.** The nonzero scale-two `(8,10)` first-face, in the
linear-root packet of `normalized810ScaleTwo_nonzeroFace_has_linear_root`. -/
theorem planeKeller810NonzeroFaceExclusion_closed :
    PlaneKeller810NonzeroFaceExclusion (K := K) :=
  normalized810ScaleTwo_nonzeroFace_false

#print axioms normalized810ScaleTwo_nonzeroFace_false
#print axioms planeKeller810NonzeroFaceExclusion_closed

end NonzeroFaceExclusion810

end Max11DegreeRoutes
