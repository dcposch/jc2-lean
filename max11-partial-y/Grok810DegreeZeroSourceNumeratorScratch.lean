import Grok810DegreeZeroPoleAndClearingScratch

/-! # Cleared source numerator of the `(8,10)` degree-zero primitive

Lane Z6 of the `(8,10)` chamber map.  Lanes Z4–Z5 recorded the order-`1`
pole obstruction and the source-homogeneous clearing `h^{119}` of the
weight-`17` grouped primitive, with grouped integer scale `2^{28}`.
This file expands that numerator.

The integer compact of the Z1 grouped primitive is homogeneous of weight
`17` and has `215` terms after clearing the grouped scale
`2^{28}`.  The nested residual expansion `compact = 2^{28} ρ` is a
later compact-bridge; this file uses the compact only through its
weight-`17` source scaling.  Substituting the octic-depression coordinates `h^{7d}` at
depth `d`, and clearing the remaining coordinate denominators, produces a
`977`-term source polynomial of generic `h`-degree `119`
and integer scale `2^{62}`.  The raw source has `H_MIN = 0`.  After the
same six unsolved valuation substitutions used by the degree-one `π`
tower (`a₇ = h⁶ t₀`, `a₆ = h⁴ v₁`, `a₅ = h² u₁`, `b₈ = h⁶ s₁`,
`b₇ = h⁴ w₁`, `b₆ = h² b₆₂`), the lowest surviving power is `102`.

The four scalar load solves are not inserted as polynomial identities.
The first frozen head is the `h⁰` coefficient of the order-`102`
quotient, a `244`-term form of weighted degree `17` in
`t₀, v₁, u₁, a₄, s₁, w₁, b₆₂, b₅`.  It does not factor into coordinate
monomials.  The Z4 pole obstruction, applied to a remaining order-`17`
clearing of the scaled left-jet primitive, forces that head to vanish
at a linear root of `h₀`.  The clearing identity itself is the
hypothesis the later source wrapper discharges.

The `977`-term source is split into `25` blocks
so each jet identity is a bounded `ring` goal.  The order-`102` quotient
is definitionally `Head + h · Plus`.

No chamber is closed.  After degree `0` there is no unused Keller row.
The next unused compact-numerator order on this jet is `103`.

CAS dump: compact `215` terms, scale `2^{28}`; cleared
source `977` terms, scale `2^{62}`; base order `102`;
head `244` terms; plus `733` terms; `25`
source blocks.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Bookkeeping: extracted base order -/

def degreeZeroSourceBaseOrder810 : ℕ := 102

def degreeZeroEffectiveTowerLength810 : ℕ := 17

def degreeZeroClearedIntegerScale810 : ℕ := 4611686018427387904

theorem degreeZeroSourceBaseOrder810_eq :
    degreeZeroSourceBaseOrder810 = 102 := rfl

theorem degreeZeroEffectiveTowerLength810_eq :
    degreeZeroEffectiveTowerLength810 = 17 := rfl

theorem degreeZeroClearedIntegerScale810_eq :
    degreeZeroClearedIntegerScale810 = 4611686018427387904 := rfl

theorem degreeZeroEffectiveTowerLength810_eq_sub :
    degreeZeroEffectiveTowerLength810 =
      degreeZeroSourceClearingPower810 - degreeZeroSourceBaseOrder810 :=
  rfl

theorem degreeZeroClearedIntegerScale810_eq_pow :
    degreeZeroClearedIntegerScale810 = 2 ^ 62 := rfl

theorem degreeZeroSourceBaseOrder810_ne_sixtyNine :
    degreeZeroSourceBaseOrder810 ≠ 69 := by decide

theorem degreeZeroSourceBaseOrder810_ne_ninetySix :
    degreeZeroSourceBaseOrder810 ≠ 96 := by decide

theorem degreeZeroClearedIntegerScale810_ne_grouped :
    degreeZeroClearedIntegerScale810 ≠
      degreeZeroGroupedIntegerScale810 := by decide

#print axioms degreeZeroEffectiveTowerLength810_eq_sub
#print axioms degreeZeroClearedIntegerScale810_eq_pow

/-! ## Compact integer numerator of the grouped primitive -/

section DegreeZeroCompact810

variable {S : Type*} [CommRing S]

set_option maxHeartbeats 800000000 in
/-- Integer `215`-term compact of the grouped degree-zero
primitive, obtained by clearing the grouped scale `2^{28}`.  The ring
is named `S` so the residual coordinate `R` is not shadowed. -/
def degreeZeroClearedCompact810 (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : S) : S :=
    - (7245315 : S) * L * A ^ 8
    + (66242880 : S) * L * A ^ 6 * C0
    + (198728640 : S) * L * A ^ 5 * B ^ 2
    - (77552640 : S) * L * A ^ 5 * E0
    - (387763200 : S) * L * A ^ 4 * B * D0
    - (193881600 : S) * L * A ^ 4 * C0 ^ 2
    + (94003200 : S) * L * A ^ 4 * G0
    - (775526400 : S) * L * A ^ 3 * B ^ 2 * C0
    + (376012800 : S) * L * A ^ 3 * B * F0
    + (376012800 : S) * L * A ^ 3 * C0 * E0
    + (188006400 : S) * L * A ^ 3 * D0 ^ 2
    - (193881600 : S) * L * A ^ 2 * B ^ 4
    + (564019200 : S) * L * A ^ 2 * B ^ 2 * E0
    + (1128038400 : S) * L * A ^ 2 * B * C0 * D0
    + (188006400 : S) * L * A ^ 2 * C0 ^ 3
    - (360972288 : S) * L * A ^ 2 * C0 * G0
    - (360972288 : S) * L * A ^ 2 * D0 * F0
    - (180486144 : S) * L * A ^ 2 * E0 ^ 2
    + (376012800 : S) * L * A * B ^ 3 * D0
    + (564019200 : S) * L * A * B ^ 2 * C0 ^ 2
    - (360972288 : S) * L * A * B ^ 2 * G0
    - (721944576 : S) * L * A * B * C0 * F0
    - (721944576 : S) * L * A * B * D0 * E0
    - (360972288 : S) * L * A * C0 ^ 2 * E0
    - (360972288 : S) * L * A * C0 * D0 ^ 2
    + (339738624 : S) * L * A * E0 * G0
    + (169869312 : S) * L * A * F0 ^ 2
    + (94003200 : S) * L * B ^ 4 * C0
    - (120324096 : S) * L * B ^ 3 * F0
    - (360972288 : S) * L * B ^ 2 * C0 * E0
    - (180486144 : S) * L * B ^ 2 * D0 ^ 2
    - (360972288 : S) * L * B * C0 ^ 2 * D0
    + (339738624 : S) * L * B * D0 * G0
    + (339738624 : S) * L * B * E0 * F0
    - (30081024 : S) * L * C0 ^ 4
    + (169869312 : S) * L * C0 ^ 2 * G0
    + (339738624 : S) * L * C0 * D0 * F0
    + (169869312 : S) * L * C0 * E0 ^ 2
    + (169869312 : S) * L * D0 ^ 2 * E0
    - (150994944 : S) * L * G0 ^ 2
    - (64402800 : S) * A ^ 7 * B
    + (7360320 : S) * A ^ 7 * Q
    + (58882560 : S) * A ^ 6 * B * P
    + (73603200 : S) * A ^ 6 * D0
    - (7180800 : S) * A ^ 6 * S0
    + (441619200 : S) * A ^ 5 * B * C0
    - (51701760 : S) * A ^ 5 * B * R
    - (60318720 : S) * A ^ 5 * C0 * Q
    - (68935680 : S) * A ^ 5 * D0 * P
    - (86169600 : S) * A ^ 5 * F0
    + (6266880 : S) * A ^ 5 * U0
    + (368016000 : S) * A ^ 4 * B ^ 3
    - (150796800 : S) * A ^ 4 * B ^ 2 * Q
    - (344678400 : S) * A ^ 4 * B * C0 * P
    - (430848000 : S) * A ^ 4 * B * E0
    + (41779200 : S) * A ^ 4 * B * T0
    - (430848000 : S) * A ^ 4 * C0 * D0
    + (52224000 : S) * A ^ 4 * C0 * S0
    + (62668800 : S) * A ^ 4 * D0 * R
    + (73113600 : S) * A ^ 4 * E0 * Q
    + (83558400 : S) * A ^ 4 * F0 * P
    - (3342336 : S) * A ^ 4 * W0
    - (229785600 : S) * A ^ 3 * B ^ 3 * P
    - (861696000 : S) * A ^ 3 * B ^ 2 * D0
    + (104448000 : S) * A ^ 3 * B ^ 2 * S0
    - (861696000 : S) * A ^ 3 * B * C0 ^ 2
    + (250675200 : S) * A ^ 3 * B * C0 * R
    + (292454400 : S) * A ^ 3 * B * D0 * Q
    + (334233600 : S) * A ^ 3 * B * E0 * P
    + (417792000 : S) * A ^ 3 * B * G0
    - (26738688 : S) * A ^ 3 * B * V0
    + (146227200 : S) * A ^ 3 * C0 ^ 2 * Q
    + (334233600 : S) * A ^ 3 * C0 * D0 * P
    + (417792000 : S) * A ^ 3 * C0 * F0
    - (40108032 : S) * A ^ 3 * C0 * U0
    + (417792000 : S) * A ^ 3 * D0 * E0
    - (53477376 : S) * A ^ 3 * D0 * T0
    - (66846720 : S) * A ^ 3 * E0 * S0
    - (80216064 : S) * A ^ 3 * F0 * R
    - (93585408 : S) * A ^ 3 * G0 * Q
    - (861696000 : S) * A ^ 2 * B ^ 3 * C0
    + (125337600 : S) * A ^ 2 * B ^ 3 * R
    + (438681600 : S) * A ^ 2 * B ^ 2 * C0 * Q
    + (501350400 : S) * A ^ 2 * B ^ 2 * D0 * P
    + (626688000 : S) * A ^ 2 * B ^ 2 * F0
    - (60162048 : S) * A ^ 2 * B ^ 2 * U0
    + (501350400 : S) * A ^ 2 * B * C0 ^ 2 * P
    + (1253376000 : S) * A ^ 2 * B * C0 * E0
    - (160432128 : S) * A ^ 2 * B * C0 * T0
    + (626688000 : S) * A ^ 2 * B * D0 ^ 2
    - (200540160 : S) * A ^ 2 * B * D0 * S0
    - (240648192 : S) * A ^ 2 * B * E0 * R
    - (280756224 : S) * A ^ 2 * B * F0 * Q
    - (320864256 : S) * A ^ 2 * B * G0 * P
    + (626688000 : S) * A ^ 2 * C0 ^ 2 * D0
    - (100270080 : S) * A ^ 2 * C0 ^ 2 * S0
    - (240648192 : S) * A ^ 2 * C0 * D0 * R
    - (280756224 : S) * A ^ 2 * C0 * E0 * Q
    - (320864256 : S) * A ^ 2 * C0 * F0 * P
    + (18874368 : S) * A ^ 2 * C0 * W0
    - (140378112 : S) * A ^ 2 * D0 ^ 2 * Q
    - (320864256 : S) * A ^ 2 * D0 * E0 * P
    - (401080320 : S) * A ^ 2 * D0 * G0
    + (37748736 : S) * A ^ 2 * D0 * V0
    - (401080320 : S) * A ^ 2 * E0 * F0
    + (56623104 : S) * A ^ 2 * E0 * U0
    + (75497472 : S) * A ^ 2 * F0 * T0
    + (94371840 : S) * A ^ 2 * G0 * S0
    - (86169600 : S) * A * B ^ 5
    + (73113600 : S) * A * B ^ 4 * Q
    + (334233600 : S) * A * B ^ 3 * C0 * P
    + (417792000 : S) * A * B ^ 3 * E0
    - (53477376 : S) * A * B ^ 3 * T0
    + (1253376000 : S) * A * B ^ 2 * C0 * D0
    - (200540160 : S) * A * B ^ 2 * C0 * S0
    - (240648192 : S) * A * B ^ 2 * D0 * R
    - (280756224 : S) * A * B ^ 2 * E0 * Q
    - (320864256 : S) * A * B ^ 2 * F0 * P
    + (18874368 : S) * A * B ^ 2 * W0
    + (417792000 : S) * A * B * C0 ^ 3
    - (240648192 : S) * A * B * C0 ^ 2 * R
    - (561512448 : S) * A * B * C0 * D0 * Q
    - (641728512 : S) * A * B * C0 * E0 * P
    - (802160640 : S) * A * B * C0 * G0
    + (75497472 : S) * A * B * C0 * V0
    - (320864256 : S) * A * B * D0 ^ 2 * P
    - (802160640 : S) * A * B * D0 * F0
    + (113246208 : S) * A * B * D0 * U0
    - (401080320 : S) * A * B * E0 ^ 2
    + (150994944 : S) * A * B * E0 * T0
    + (188743680 : S) * A * B * F0 * S0
    + (226492416 : S) * A * B * G0 * R
    - (93585408 : S) * A * C0 ^ 3 * Q
    - (320864256 : S) * A * C0 ^ 2 * D0 * P
    - (401080320 : S) * A * C0 ^ 2 * F0
    + (56623104 : S) * A * C0 ^ 2 * U0
    - (802160640 : S) * A * C0 * D0 * E0
    + (150994944 : S) * A * C0 * D0 * T0
    + (188743680 : S) * A * C0 * E0 * S0
    + (226492416 : S) * A * C0 * F0 * R
    + (264241152 : S) * A * C0 * G0 * Q
    - (133693440 : S) * A * D0 ^ 3
    + (94371840 : S) * A * D0 ^ 2 * S0
    + (226492416 : S) * A * D0 * E0 * R
    + (264241152 : S) * A * D0 * F0 * Q
    + (301989888 : S) * A * D0 * G0 * P
    + (132120576 : S) * A * E0 ^ 2 * Q
    + (301989888 : S) * A * E0 * F0 * P
    - (33554432 : S) * A * E0 * W0
    + (377487360 : S) * A * F0 * G0
    - (67108864 : S) * A * F0 * V0
    - (100663296 : S) * A * G0 * U0
    + (16711680 : S) * B ^ 5 * P
    + (104448000 : S) * B ^ 4 * D0
    - (16711680 : S) * B ^ 4 * S0
    + (208896000 : S) * B ^ 3 * C0 ^ 2
    - (80216064 : S) * B ^ 3 * C0 * R
    - (93585408 : S) * B ^ 3 * D0 * Q
    - (106954752 : S) * B ^ 3 * E0 * P
    - (133693440 : S) * B ^ 3 * G0
    + (12582912 : S) * B ^ 3 * V0
    - (140378112 : S) * B ^ 2 * C0 ^ 2 * Q
    - (320864256 : S) * B ^ 2 * C0 * D0 * P
    - (401080320 : S) * B ^ 2 * C0 * F0
    + (56623104 : S) * B ^ 2 * C0 * U0
    - (401080320 : S) * B ^ 2 * D0 * E0
    + (75497472 : S) * B ^ 2 * D0 * T0
    + (94371840 : S) * B ^ 2 * E0 * S0
    + (113246208 : S) * B ^ 2 * F0 * R
    + (132120576 : S) * B ^ 2 * G0 * Q
    - (106954752 : S) * B * C0 ^ 3 * P
    - (401080320 : S) * B * C0 ^ 2 * E0
    + (75497472 : S) * B * C0 ^ 2 * T0
    - (401080320 : S) * B * C0 * D0 ^ 2
    + (188743680 : S) * B * C0 * D0 * S0
    + (226492416 : S) * B * C0 * E0 * R
    + (264241152 : S) * B * C0 * F0 * Q
    + (301989888 : S) * B * C0 * G0 * P
    + (113246208 : S) * B * D0 ^ 2 * R
    + (264241152 : S) * B * D0 * E0 * Q
    + (301989888 : S) * B * D0 * F0 * P
    - (33554432 : S) * B * D0 * W0
    + (150994944 : S) * B * E0 ^ 2 * P
    + (377487360 : S) * B * E0 * G0
    - (67108864 : S) * B * E0 * V0
    + (188743680 : S) * B * F0 ^ 2
    - (100663296 : S) * B * F0 * U0
    - (134217728 : S) * B * G0 * T0
    - (133693440 : S) * C0 ^ 3 * D0
    + (31457280 : S) * C0 ^ 3 * S0
    + (113246208 : S) * C0 ^ 2 * D0 * R
    + (132120576 : S) * C0 ^ 2 * E0 * Q
    + (150994944 : S) * C0 ^ 2 * F0 * P
    - (16777216 : S) * C0 ^ 2 * W0
    + (132120576 : S) * C0 * D0 ^ 2 * Q
    + (301989888 : S) * C0 * D0 * E0 * P
    + (377487360 : S) * C0 * D0 * G0
    - (67108864 : S) * C0 * D0 * V0
    + (377487360 : S) * C0 * E0 * F0
    - (100663296 : S) * C0 * E0 * U0
    - (134217728 : S) * C0 * F0 * T0
    - (167772160 : S) * C0 * G0 * S0
    + (50331648 : S) * D0 ^ 3 * P
    + (188743680 : S) * D0 ^ 2 * F0
    - (50331648 : S) * D0 ^ 2 * U0
    + (188743680 : S) * D0 * E0 ^ 2
    - (134217728 : S) * D0 * E0 * T0
    - (167772160 : S) * D0 * F0 * S0
    - (201326592 : S) * D0 * G0 * R
    - (83886080 : S) * E0 ^ 2 * S0
    - (201326592 : S) * E0 * F0 * R
    - (234881024 : S) * E0 * G0 * Q
    - (117440512 : S) * F0 ^ 2 * Q
    - (268435456 : S) * F0 * G0 * P
    + (268435456 : S) * G0 * W0

end DegreeZeroCompact810

section DegreeZeroCompactFieldBridge810

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- Weight `17` of the compact numerator, with source-scale weight `7`
per unit of residual weight. -/
theorem degreeZeroClearedCompact810_weightedScale
    (h L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) :
    degreeZeroClearedCompact810 (h ^ 7 * L) (h ^ 14 * A) (h ^ 21 * B)
        (h ^ 28 * C0) (h ^ 35 * D0) (h ^ 42 * E0) (h ^ 49 * F0)
        (h ^ 56 * G0) (h ^ 14 * P) (h ^ 21 * Q) (h ^ 28 * R)
        (h ^ 35 * S0) (h ^ 42 * T0) (h ^ 49 * U0) (h ^ 56 * V0)
        (h ^ 63 * W0) =
      h ^ degreeZeroSourceClearingPower810 *
        degreeZeroClearedCompact810 L A B C0 D0 E0 F0 G0 P Q R S0 T0
          U0 V0 W0 := by
  simp only [degreeZeroClearedCompact810, degreeZeroSourceClearingPower810]
  ring

#print axioms degreeZeroClearedCompact810_weightedScale

end DegreeZeroCompactFieldBridge810

/-! ## `h^{119}`-cleared source numerator, in jet blocks -/

section DegreeZeroClearedSource810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 200000000 in
/-- Source block `0` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock0_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (648518346341351424 : R) * h ^ 119 * a0 ^ 2 * lambda
    + (4611686018427387904 : R) * h ^ 118 * a0 * b1
    + (6485183463413514240 : R) * h ^ 112 * a6 * a1 * a0
    + (6485183463413514240 : R) * h ^ 112 * a5 * a2 * a0
    + (3242591731706757120 : R) * h ^ 112 * a5 * a1 ^ 2
    + (6485183463413514240 : R) * h ^ 112 * a4 * a3 * a0
    + (6485183463413514240 : R) * h ^ 112 * a4 * a2 * a1
    + (3242591731706757120 : R) * h ^ 112 * a3 ^ 2 * a1
    + (3242591731706757120 : R) * h ^ 112 * a3 * a2 ^ 2
    - (1459166279268040704 : R) * h ^ 111 * a7 * a1 * a0 * lambda
    - (1459166279268040704 : R) * h ^ 111 * a6 * a2 * a0 * lambda
    - (729583139634020352 : R) * h ^ 111 * a6 * a1 ^ 2 * lambda
    - (1459166279268040704 : R) * h ^ 111 * a5 * a3 * a0 * lambda
    - (1459166279268040704 : R) * h ^ 111 * a5 * a2 * a1 * lambda
    - (729583139634020352 : R) * h ^ 111 * a4 ^ 2 * a0 * lambda
    - (1459166279268040704 : R) * h ^ 111 * a4 * a3 * a1 * lambda
    - (729583139634020352 : R) * h ^ 111 * a4 * a2 ^ 2 * lambda
    - (729583139634020352 : R) * h ^ 111 * a3 ^ 2 * a2 * lambda
    - (576460752303423488 : R) * h ^ 110 * a7 * a1 * b1
    - (1152921504606846976 : R) * h ^ 110 * a7 * a0 * b2
    - (576460752303423488 : R) * h ^ 110 * a6 * a2 * b1
    - (1152921504606846976 : R) * h ^ 110 * a6 * a1 * b2
    - (1729382256910270464 : R) * h ^ 110 * a6 * a0 * b3
    - (576460752303423488 : R) * h ^ 110 * a5 * a3 * b1
    - (1152921504606846976 : R) * h ^ 110 * a5 * a2 * b2
    - (1729382256910270464 : R) * h ^ 110 * a5 * a1 * b3
    - (2305843009213693952 : R) * h ^ 110 * a5 * a0 * b4
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

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `0`. -/
def degreeZeroSourceJetHeadBlock0_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `0`. -/
def degreeZeroSourceJetPlusBlock0_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (648518346341351424 : R) * h ^ 16 * a0 ^ 2 * lambda
    + (4611686018427387904 : R) * h ^ 15 * a0 * b1
    - (1459166279268040704 : R) * h ^ 14 * t0 * a1 * a0 * lambda
    - (576460752303423488 : R) * h ^ 13 * t0 * a1 * b1
    - (1152921504606846976 : R) * h ^ 13 * t0 * a0 * b2
    + (6485183463413514240 : R) * h ^ 13 * v1 * a1 * a0
    - (1459166279268040704 : R) * h ^ 12 * v1 * a2 * a0 * lambda
    - (729583139634020352 : R) * h ^ 12 * v1 * a1 ^ 2 * lambda
    - (576460752303423488 : R) * h ^ 11 * v1 * a2 * b1
    - (1152921504606846976 : R) * h ^ 11 * v1 * a1 * b2
    - (1729382256910270464 : R) * h ^ 11 * v1 * a0 * b3
    + (6485183463413514240 : R) * h ^ 11 * u1 * a2 * a0
    + (3242591731706757120 : R) * h ^ 11 * u1 * a1 ^ 2
    - (4035225266123964416 : R) * h ^ 11 * a2 * a0 * w1
    - (2017612633061982208 : R) * h ^ 11 * a1 ^ 2 * w1
    - (1459166279268040704 : R) * h ^ 10 * u1 * a3 * a0 * lambda
    - (1459166279268040704 : R) * h ^ 10 * u1 * a2 * a1 * lambda
    - (576460752303423488 : R) * h ^ 9 * u1 * a3 * b1
    - (1152921504606846976 : R) * h ^ 9 * u1 * a2 * b2
    - (1729382256910270464 : R) * h ^ 9 * u1 * a1 * b3
    - (2305843009213693952 : R) * h ^ 9 * u1 * a0 * b4
    + (6485183463413514240 : R) * h ^ 9 * a4 * a3 * a0
    + (6485183463413514240 : R) * h ^ 9 * a4 * a2 * a1
    + (3242591731706757120 : R) * h ^ 9 * a3 ^ 2 * a1
    + (3242591731706757120 : R) * h ^ 9 * a3 * a2 ^ 2
    - (3458764513820540928 : R) * h ^ 9 * a3 * a0 * b62
    - (3458764513820540928 : R) * h ^ 9 * a2 * a1 * b62
    - (729583139634020352 : R) * h ^ 8 * a4 ^ 2 * a0 * lambda
    - (1459166279268040704 : R) * h ^ 8 * a4 * a3 * a1 * lambda
    - (729583139634020352 : R) * h ^ 8 * a4 * a2 ^ 2 * lambda
    - (729583139634020352 : R) * h ^ 8 * a3 ^ 2 * a2 * lambda
    - (288230376151711744 : R) * h ^ 7 * a4 ^ 2 * b1
    - (1152921504606846976 : R) * h ^ 7 * a4 * a3 * b2
    - (1729382256910270464 : R) * h ^ 7 * a4 * a2 * b3
    - (2305843009213693952 : R) * h ^ 7 * a4 * a1 * b4
    - (2882303761517117440 : R) * h ^ 7 * a4 * a0 * b5
    - (864691128455135232 : R) * h ^ 7 * a3 ^ 2 * b3
    - (2305843009213693952 : R) * h ^ 7 * a3 * a2 * b4
    - (2882303761517117440 : R) * h ^ 7 * a3 * a1 * b5
    - (1441151880758558720 : R) * h ^ 7 * a2 ^ 2 * b5

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock0_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock0_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock0_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock0_810,
    degreeZeroSourceJetHeadBlock0_810,
    degreeZeroSourceJetPlusBlock0_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `1` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock1_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4611686018427387904 : R) * h ^ 110 * a1 * a0 * b8
    + (405323966463344640 : R) * h ^ 104 * a7 ^ 2 * a1 * a0
    - (6485183463413514240 : R) * h ^ 104 * a7 * a6 * a2 * a0
    - (3242591731706757120 : R) * h ^ 104 * a7 * a6 * a1 ^ 2
    - (6485183463413514240 : R) * h ^ 104 * a7 * a5 * a3 * a0
    - (6485183463413514240 : R) * h ^ 104 * a7 * a5 * a2 * a1
    - (3242591731706757120 : R) * h ^ 104 * a7 * a4 ^ 2 * a0
    - (6485183463413514240 : R) * h ^ 104 * a7 * a4 * a3 * a1
    - (3242591731706757120 : R) * h ^ 104 * a7 * a4 * a2 ^ 2
    - (3242591731706757120 : R) * h ^ 104 * a7 * a3 ^ 2 * a2
    - (6890507429876858880 : R) * h ^ 104 * a6 ^ 2 * a3 * a0
    - (6890507429876858880 : R) * h ^ 104 * a6 ^ 2 * a2 * a1
    - (13781014859753717760 : R) * h ^ 104 * a6 * a5 * a4 * a0
    - (13781014859753717760 : R) * h ^ 104 * a6 * a5 * a3 * a1
    - (6890507429876858880 : R) * h ^ 104 * a6 * a5 * a2 ^ 2
    - (6890507429876858880 : R) * h ^ 104 * a6 * a4 ^ 2 * a1
    - (13781014859753717760 : R) * h ^ 104 * a6 * a4 * a3 * a2
    - (2296835809958952960 : R) * h ^ 104 * a6 * a3 ^ 3
    - (2296835809958952960 : R) * h ^ 104 * a5 ^ 3 * a0
    - (6890507429876858880 : R) * h ^ 104 * a5 ^ 2 * a4 * a1
    - (6890507429876858880 : R) * h ^ 104 * a5 ^ 2 * a3 * a2
    - (6890507429876858880 : R) * h ^ 104 * a5 * a4 ^ 2 * a2
    - (6890507429876858880 : R) * h ^ 104 * a5 * a4 * a3 ^ 2
    - (2296835809958952960 : R) * h ^ 104 * a4 ^ 3 * a3
    + (1550364171722293248 : R) * h ^ 103 * a7 ^ 2 * a2 * a0 * lambda
    + (775182085861146624 : R) * h ^ 103 * a7 ^ 2 * a1 ^ 2 * lambda
    + (3100728343444586496 : R) * h ^ 103 * a7 * a6 * a3 * a0 * lambda
    + (3100728343444586496 : R) * h ^ 103 * a7 * a6 * a2 * a1 * lambda
    + (3100728343444586496 : R) * h ^ 103 * a7 * a5 * a4 * a0 * lambda
    + (3100728343444586496 : R) * h ^ 103 * a7 * a5 * a3 * a1 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a7 * a5 * a2 ^ 2 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a7 * a4 ^ 2 * a1 * lambda
    + (3100728343444586496 : R) * h ^ 103 * a7 * a4 * a3 * a2 * lambda
    + (516788057240764416 : R) * h ^ 103 * a7 * a3 ^ 3 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 ^ 2 * a4 * a0 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 ^ 2 * a3 * a1 * lambda
    + (775182085861146624 : R) * h ^ 103 * a6 ^ 2 * a2 ^ 2 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 * a5 ^ 2 * a0 * lambda
    + (3100728343444586496 : R) * h ^ 103 * a6 * a5 * a4 * a1 * lambda
    + (3100728343444586496 : R) * h ^ 103 * a6 * a5 * a3 * a2 * lambda

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `1`. -/
def degreeZeroSourceJetHeadBlock1_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `1`. -/
def degreeZeroSourceJetPlusBlock1_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (405323966463344640 : R) * h ^ 13 * t0 ^ 2 * a1 * a0
    - (4611686018427387904 : R) * h ^ 13 * a1 * a0 * s1
    + (1550364171722293248 : R) * h ^ 12 * t0 ^ 2 * a2 * a0 * lambda
    + (775182085861146624 : R) * h ^ 12 * t0 ^ 2 * a1 ^ 2 * lambda
    - (6485183463413514240 : R) * h ^ 11 * t0 * v1 * a2 * a0
    - (3242591731706757120 : R) * h ^ 11 * t0 * v1 * a1 ^ 2
    + (3100728343444586496 : R) * h ^ 10 * t0 * v1 * a3 * a0 * lambda
    + (3100728343444586496 : R) * h ^ 10 * t0 * v1 * a2 * a1 * lambda
    - (6485183463413514240 : R) * h ^ 9 * t0 * u1 * a3 * a0
    - (6485183463413514240 : R) * h ^ 9 * t0 * u1 * a2 * a1
    - (6890507429876858880 : R) * h ^ 9 * v1 ^ 2 * a3 * a0
    - (6890507429876858880 : R) * h ^ 9 * v1 ^ 2 * a2 * a1
    + (3100728343444586496 : R) * h ^ 8 * t0 * u1 * a4 * a0 * lambda
    + (3100728343444586496 : R) * h ^ 8 * t0 * u1 * a3 * a1 * lambda
    + (1550364171722293248 : R) * h ^ 8 * t0 * u1 * a2 ^ 2 * lambda
    + (1550364171722293248 : R) * h ^ 8 * v1 ^ 2 * a4 * a0 * lambda
    + (1550364171722293248 : R) * h ^ 8 * v1 ^ 2 * a3 * a1 * lambda
    + (775182085861146624 : R) * h ^ 8 * v1 ^ 2 * a2 ^ 2 * lambda
    + (1550364171722293248 : R) * h ^ 8 * v1 * u1 ^ 2 * a0 * lambda
    - (3242591731706757120 : R) * h ^ 7 * t0 * a4 ^ 2 * a0
    - (6485183463413514240 : R) * h ^ 7 * t0 * a4 * a3 * a1
    - (3242591731706757120 : R) * h ^ 7 * t0 * a4 * a2 ^ 2
    - (3242591731706757120 : R) * h ^ 7 * t0 * a3 ^ 2 * a2
    - (13781014859753717760 : R) * h ^ 7 * v1 * u1 * a4 * a0
    - (13781014859753717760 : R) * h ^ 7 * v1 * u1 * a3 * a1
    - (6890507429876858880 : R) * h ^ 7 * v1 * u1 * a2 ^ 2
    - (2296835809958952960 : R) * h ^ 7 * u1 ^ 3 * a0
    + (1550364171722293248 : R) * h ^ 6 * t0 * a4 ^ 2 * a1 * lambda
    + (3100728343444586496 : R) * h ^ 6 * t0 * a4 * a3 * a2 * lambda
    + (516788057240764416 : R) * h ^ 6 * t0 * a3 ^ 3 * lambda
    + (3100728343444586496 : R) * h ^ 6 * v1 * u1 * a4 * a1 * lambda
    + (3100728343444586496 : R) * h ^ 6 * v1 * u1 * a3 * a2 * lambda
    - (6890507429876858880 : R) * h ^ 5 * v1 * a4 ^ 2 * a1
    - (13781014859753717760 : R) * h ^ 5 * v1 * a4 * a3 * a2
    - (2296835809958952960 : R) * h ^ 5 * v1 * a3 ^ 3
    - (6890507429876858880 : R) * h ^ 5 * u1 ^ 2 * a4 * a1
    - (6890507429876858880 : R) * h ^ 5 * u1 ^ 2 * a3 * a2
    - (6890507429876858880 : R) * h ^ 3 * u1 * a4 ^ 2 * a2
    - (6890507429876858880 : R) * h ^ 3 * u1 * a4 * a3 ^ 2
    - (2296835809958952960 : R) * h * a4 ^ 3 * a3

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock1_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock1_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock1_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock1_810,
    degreeZeroSourceJetHeadBlock1_810,
    degreeZeroSourceJetPlusBlock1_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `2` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock2_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1550364171722293248 : R) * h ^ 103 * a6 * a4 ^ 2 * a2 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a6 * a4 * a3 ^ 2 * lambda
    + (516788057240764416 : R) * h ^ 103 * a5 ^ 3 * a1 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a5 ^ 2 * a4 * a2 * lambda
    + (775182085861146624 : R) * h ^ 103 * a5 ^ 2 * a3 ^ 2 * lambda
    + (1550364171722293248 : R) * h ^ 103 * a5 * a4 ^ 2 * a3 * lambda
    + (129197014310191104 : R) * h ^ 103 * a4 ^ 4 * lambda
    + (324259173170675712 : R) * h ^ 102 * a7 ^ 2 * a2 * b1
    + (648518346341351424 : R) * h ^ 102 * a7 ^ 2 * a1 * b2
    + (972777519512027136 : R) * h ^ 102 * a7 ^ 2 * a0 * b3
    + (648518346341351424 : R) * h ^ 102 * a7 * a6 * a3 * b1
    + (1297036692682702848 : R) * h ^ 102 * a7 * a6 * a2 * b2
    + (1945555039024054272 : R) * h ^ 102 * a7 * a6 * a1 * b3
    + (2594073385365405696 : R) * h ^ 102 * a7 * a6 * a0 * b4
    + (648518346341351424 : R) * h ^ 102 * a7 * a5 * a4 * b1
    + (1297036692682702848 : R) * h ^ 102 * a7 * a5 * a3 * b2
    + (1945555039024054272 : R) * h ^ 102 * a7 * a5 * a2 * b3
    + (2594073385365405696 : R) * h ^ 102 * a7 * a5 * a1 * b4
    + (3242591731706757120 : R) * h ^ 102 * a7 * a5 * a0 * b5
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
    + (324259173170675712 : R) * h ^ 102 * a6 ^ 2 * a4 * b1
    + (648518346341351424 : R) * h ^ 102 * a6 ^ 2 * a3 * b2
    + (972777519512027136 : R) * h ^ 102 * a6 ^ 2 * a2 * b3
    + (1297036692682702848 : R) * h ^ 102 * a6 ^ 2 * a1 * b4
    + (1621295865853378560 : R) * h ^ 102 * a6 ^ 2 * a0 * b5
    + (324259173170675712 : R) * h ^ 102 * a6 * a5 ^ 2 * b1
    + (1297036692682702848 : R) * h ^ 102 * a6 * a5 * a4 * b2
    + (1945555039024054272 : R) * h ^ 102 * a6 * a5 * a3 * b3

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `2`. -/
def degreeZeroSourceJetHeadBlock2_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `2`. -/
def degreeZeroSourceJetPlusBlock2_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (324259173170675712 : R) * h ^ 11 * t0 ^ 2 * a2 * b1
    + (648518346341351424 : R) * h ^ 11 * t0 ^ 2 * a1 * b2
    + (972777519512027136 : R) * h ^ 11 * t0 ^ 2 * a0 * b3
    + (5188146770730811392 : R) * h ^ 11 * t0 * a2 * a0 * s1
    + (2594073385365405696 : R) * h ^ 11 * t0 * a1 ^ 2 * s1
    + (648518346341351424 : R) * h ^ 9 * t0 * v1 * a3 * b1
    + (1297036692682702848 : R) * h ^ 9 * t0 * v1 * a2 * b2
    + (1945555039024054272 : R) * h ^ 9 * t0 * v1 * a1 * b3
    + (2594073385365405696 : R) * h ^ 9 * t0 * v1 * a0 * b4
    + (4539628424389459968 : R) * h ^ 9 * t0 * a3 * a0 * w1
    + (4539628424389459968 : R) * h ^ 9 * t0 * a2 * a1 * w1
    + (648518346341351424 : R) * h ^ 7 * t0 * u1 * a4 * b1
    + (1297036692682702848 : R) * h ^ 7 * t0 * u1 * a3 * b2
    + (1945555039024054272 : R) * h ^ 7 * t0 * u1 * a2 * b3
    + (2594073385365405696 : R) * h ^ 7 * t0 * u1 * a1 * b4
    + (3242591731706757120 : R) * h ^ 7 * t0 * u1 * a0 * b5
    + (3891110078048108544 : R) * h ^ 7 * t0 * a4 * a0 * b62
    + (3891110078048108544 : R) * h ^ 7 * t0 * a3 * a1 * b62
    + (1945555039024054272 : R) * h ^ 7 * t0 * a2 ^ 2 * b62
    + (324259173170675712 : R) * h ^ 7 * v1 ^ 2 * a4 * b1
    + (648518346341351424 : R) * h ^ 7 * v1 ^ 2 * a3 * b2
    + (972777519512027136 : R) * h ^ 7 * v1 ^ 2 * a2 * b3
    + (1297036692682702848 : R) * h ^ 7 * v1 ^ 2 * a1 * b4
    + (1621295865853378560 : R) * h ^ 7 * v1 ^ 2 * a0 * b5
    + (324259173170675712 : R) * h ^ 7 * v1 * u1 ^ 2 * b1
    + (516788057240764416 : R) * h ^ 6 * u1 ^ 3 * a1 * lambda
    + (648518346341351424 : R) * h ^ 5 * t0 * a4 ^ 2 * b2
    + (1945555039024054272 : R) * h ^ 5 * t0 * a4 * a3 * b3
    + (2594073385365405696 : R) * h ^ 5 * t0 * a4 * a2 * b4
    + (3242591731706757120 : R) * h ^ 5 * t0 * a4 * a1 * b5
    + (1297036692682702848 : R) * h ^ 5 * t0 * a3 ^ 2 * b4
    + (3242591731706757120 : R) * h ^ 5 * t0 * a3 * a2 * b5
    + (1297036692682702848 : R) * h ^ 5 * v1 * u1 * a4 * b2
    + (1945555039024054272 : R) * h ^ 5 * v1 * u1 * a3 * b3
    + (1550364171722293248 : R) * h ^ 4 * v1 * a4 ^ 2 * a2 * lambda
    + (1550364171722293248 : R) * h ^ 4 * v1 * a4 * a3 ^ 2 * lambda
    + (1550364171722293248 : R) * h ^ 4 * u1 ^ 2 * a4 * a2 * lambda
    + (775182085861146624 : R) * h ^ 4 * u1 ^ 2 * a3 ^ 2 * lambda
    + (1550364171722293248 : R) * h ^ 2 * u1 * a4 ^ 2 * a3 * lambda
    + (129197014310191104 : R) * a4 ^ 4 * lambda

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock2_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock2_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock2_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock2_810,
    degreeZeroSourceJetHeadBlock2_810,
    degreeZeroSourceJetPlusBlock2_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `3` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock3_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2594073385365405696 : R) * h ^ 102 * a6 * a5 * a2 * b4
    + (3242591731706757120 : R) * h ^ 102 * a6 * a5 * a1 * b5
    + (3891110078048108544 : R) * h ^ 102 * a6 * a5 * a0 * b6
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
    + (540431955284459520 : R) * h ^ 102 * a4 ^ 3 * b5
    + (1945555039024054272 : R) * h ^ 102 * a4 ^ 2 * a3 * b6
    + (2269814212194729984 : R) * h ^ 102 * a4 ^ 2 * a2 * b7
    + (2594073385365405696 : R) * h ^ 102 * a4 ^ 2 * a1 * b8
    + (2269814212194729984 : R) * h ^ 102 * a4 * a3 ^ 2 * b7
    + (5188146770730811392 : R) * h ^ 102 * a4 * a3 * a2 * b8
    + (864691128455135232 : R) * h ^ 102 * a3 ^ 3 * b8
    - (574208952489738240 : R) * h ^ 96 * a7 ^ 3 * a2 * a0
    - (287104476244869120 : R) * h ^ 96 * a7 ^ 3 * a1 ^ 2
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a6 * a3 * a0
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a6 * a2 * a1

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `3`. -/
def degreeZeroSourceJetHeadBlock3_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (540431955284459520 : R) * a4 ^ 3 * b5

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `3`. -/
def degreeZeroSourceJetPlusBlock3_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (574208952489738240 : R) * h ^ 11 * t0 ^ 3 * a2 * a0
    - (287104476244869120 : R) * h ^ 11 * t0 ^ 3 * a1 ^ 2
    + (6029194001142251520 : R) * h ^ 9 * t0 ^ 2 * v1 * a3 * a0
    + (6029194001142251520 : R) * h ^ 9 * t0 ^ 2 * v1 * a2 * a1
    + (5188146770730811392 : R) * h ^ 9 * v1 * a3 * a0 * s1
    + (5188146770730811392 : R) * h ^ 9 * v1 * a2 * a1 * s1
    + (3891110078048108544 : R) * h ^ 7 * v1 * u1 * a0 * b62
    + (4539628424389459968 : R) * h ^ 7 * v1 * a4 * a0 * w1
    + (4539628424389459968 : R) * h ^ 7 * v1 * a3 * a1 * w1
    + (2269814212194729984 : R) * h ^ 7 * v1 * a2 ^ 2 * w1
    + (2269814212194729984 : R) * h ^ 7 * u1 ^ 2 * a0 * w1
    + (5188146770730811392 : R) * h ^ 7 * u1 * a4 * a0 * s1
    + (5188146770730811392 : R) * h ^ 7 * u1 * a3 * a1 * s1
    + (2594073385365405696 : R) * h ^ 7 * u1 * a2 ^ 2 * s1
    + (2594073385365405696 : R) * h ^ 5 * v1 * u1 * a2 * b4
    + (3242591731706757120 : R) * h ^ 5 * v1 * u1 * a1 * b5
    + (3891110078048108544 : R) * h ^ 5 * v1 * a4 * a1 * b62
    + (3891110078048108544 : R) * h ^ 5 * v1 * a3 * a2 * b62
    + (216172782113783808 : R) * h ^ 5 * u1 ^ 3 * b2
    + (1945555039024054272 : R) * h ^ 5 * u1 ^ 2 * a1 * b62
    + (4539628424389459968 : R) * h ^ 5 * u1 * a4 * a1 * w1
    + (4539628424389459968 : R) * h ^ 5 * u1 * a3 * a2 * w1
    + (2594073385365405696 : R) * h ^ 5 * a4 ^ 2 * a1 * s1
    + (5188146770730811392 : R) * h ^ 5 * a4 * a3 * a2 * s1
    + (864691128455135232 : R) * h ^ 5 * a3 ^ 3 * s1
    + (972777519512027136 : R) * h ^ 3 * v1 * a4 ^ 2 * b3
    + (2594073385365405696 : R) * h ^ 3 * v1 * a4 * a3 * b4
    + (3242591731706757120 : R) * h ^ 3 * v1 * a4 * a2 * b5
    + (1621295865853378560 : R) * h ^ 3 * v1 * a3 ^ 2 * b5
    + (972777519512027136 : R) * h ^ 3 * u1 ^ 2 * a4 * b3
    + (1297036692682702848 : R) * h ^ 3 * u1 ^ 2 * a3 * b4
    + (1621295865853378560 : R) * h ^ 3 * u1 ^ 2 * a2 * b5
    + (3891110078048108544 : R) * h ^ 3 * u1 * a4 * a2 * b62
    + (1945555039024054272 : R) * h ^ 3 * u1 * a3 ^ 2 * b62
    + (2269814212194729984 : R) * h ^ 3 * a4 ^ 2 * a2 * w1
    + (2269814212194729984 : R) * h ^ 3 * a4 * a3 ^ 2 * w1
    + (1297036692682702848 : R) * h * u1 * a4 ^ 2 * b4
    + (3242591731706757120 : R) * h * u1 * a4 * a3 * b5
    + (1945555039024054272 : R) * h * a4 ^ 2 * a3 * b62

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock3_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock3_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock3_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock3_810,
    degreeZeroSourceJetHeadBlock3_810,
    degreeZeroSourceJetPlusBlock3_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `4` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock4_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a5 * a4 * a0
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a5 * a3 * a1
    + (3014597000571125760 : R) * h ^ 96 * a7 ^ 2 * a5 * a2 ^ 2
    + (3014597000571125760 : R) * h ^ 96 * a7 ^ 2 * a4 ^ 2 * a1
    + (6029194001142251520 : R) * h ^ 96 * a7 ^ 2 * a4 * a3 * a2
    + (1004865666857041920 : R) * h ^ 96 * a7 ^ 2 * a3 ^ 3
    + (13781014859753717760 : R) * h ^ 96 * a7 * a6 ^ 2 * a4 * a0
    + (13781014859753717760 : R) * h ^ 96 * a7 * a6 ^ 2 * a3 * a1
    + (6890507429876858880 : R) * h ^ 96 * a7 * a6 ^ 2 * a2 ^ 2
    + (13781014859753717760 : R) * h ^ 96 * a7 * a6 * a5 ^ 2 * a0
    + (27562029719507435520 : R) * h ^ 96 * a7 * a6 * a5 * a4 * a1
    + (27562029719507435520 : R) * h ^ 96 * a7 * a6 * a5 * a3 * a2
    + (13781014859753717760 : R) * h ^ 96 * a7 * a6 * a4 ^ 2 * a2
    + (13781014859753717760 : R) * h ^ 96 * a7 * a6 * a4 * a3 ^ 2
    + (4593671619917905920 : R) * h ^ 96 * a7 * a5 ^ 3 * a1
    + (13781014859753717760 : R) * h ^ 96 * a7 * a5 ^ 2 * a4 * a2
    + (6890507429876858880 : R) * h ^ 96 * a7 * a5 ^ 2 * a3 ^ 2
    + (13781014859753717760 : R) * h ^ 96 * a7 * a5 * a4 ^ 2 * a3
    + (1148417904979476480 : R) * h ^ 96 * a7 * a4 ^ 4
    + (7177611906121728000 : R) * h ^ 96 * a6 ^ 3 * a5 * a0
    + (7177611906121728000 : R) * h ^ 96 * a6 ^ 3 * a4 * a1
    + (7177611906121728000 : R) * h ^ 96 * a6 ^ 3 * a3 * a2
    + (10766417859182592000 : R) * h ^ 96 * a6 ^ 2 * a5 ^ 2 * a1
    + (21532835718365184000 : R) * h ^ 96 * a6 ^ 2 * a5 * a4 * a2
    + (10766417859182592000 : R) * h ^ 96 * a6 ^ 2 * a5 * a3 ^ 2
    + (10766417859182592000 : R) * h ^ 96 * a6 ^ 2 * a4 ^ 2 * a3
    + (7177611906121728000 : R) * h ^ 96 * a6 * a5 ^ 3 * a2
    + (21532835718365184000 : R) * h ^ 96 * a6 * a5 ^ 2 * a4 * a3
    + (7177611906121728000 : R) * h ^ 96 * a6 * a5 * a4 ^ 3
    + (1794402976530432000 : R) * h ^ 96 * a5 ^ 4 * a3
    + (3588805953060864000 : R) * h ^ 96 * a5 ^ 3 * a4 ^ 2
    - (1614962678877388800 : R) * h ^ 95 * a7 ^ 3 * a3 * a0 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a7 ^ 3 * a2 * a1 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a7 ^ 2 * a6 * a4 * a0 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a7 ^ 2 * a6 * a3 * a1 * lambda
    - (2422444018316083200 : R) * h ^ 95 * a7 ^ 2 * a6 * a2 ^ 2 * lambda
    - (2422444018316083200 : R) * h ^ 95 * a7 ^ 2 * a5 ^ 2 * a0 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a7 ^ 2 * a5 * a4 * a1 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a7 ^ 2 * a5 * a3 * a2 * lambda
    - (2422444018316083200 : R) * h ^ 95 * a7 ^ 2 * a4 ^ 2 * a2 * lambda

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `4`. -/
def degreeZeroSourceJetHeadBlock4_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1148417904979476480 : R) * t0 * a4 ^ 4
    + (7177611906121728000 : R) * v1 * u1 * a4 ^ 3
    + (3588805953060864000 : R) * u1 ^ 3 * a4 ^ 2

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `4`. -/
def degreeZeroSourceJetPlusBlock4_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1614962678877388800 : R) * h ^ 10 * t0 ^ 3 * a3 * a0 * lambda
    - (1614962678877388800 : R) * h ^ 10 * t0 ^ 3 * a2 * a1 * lambda
    - (4844888036632166400 : R) * h ^ 8 * t0 ^ 2 * v1 * a4 * a0 * lambda
    - (4844888036632166400 : R) * h ^ 8 * t0 ^ 2 * v1 * a3 * a1 * lambda
    - (2422444018316083200 : R) * h ^ 8 * t0 ^ 2 * v1 * a2 ^ 2 * lambda
    - (2422444018316083200 : R) * h ^ 8 * t0 ^ 2 * u1 ^ 2 * a0 * lambda
    + (6029194001142251520 : R) * h ^ 7 * t0 ^ 2 * u1 * a4 * a0
    + (6029194001142251520 : R) * h ^ 7 * t0 ^ 2 * u1 * a3 * a1
    + (3014597000571125760 : R) * h ^ 7 * t0 ^ 2 * u1 * a2 ^ 2
    + (13781014859753717760 : R) * h ^ 7 * t0 * v1 ^ 2 * a4 * a0
    + (13781014859753717760 : R) * h ^ 7 * t0 * v1 ^ 2 * a3 * a1
    + (6890507429876858880 : R) * h ^ 7 * t0 * v1 ^ 2 * a2 ^ 2
    + (13781014859753717760 : R) * h ^ 7 * t0 * v1 * u1 ^ 2 * a0
    + (7177611906121728000 : R) * h ^ 7 * v1 ^ 3 * u1 * a0
    - (4844888036632166400 : R) * h ^ 6 * t0 ^ 2 * u1 * a4 * a1 * lambda
    - (4844888036632166400 : R) * h ^ 6 * t0 ^ 2 * u1 * a3 * a2 * lambda
    + (3014597000571125760 : R) * h ^ 5 * t0 ^ 2 * a4 ^ 2 * a1
    + (6029194001142251520 : R) * h ^ 5 * t0 ^ 2 * a4 * a3 * a2
    + (1004865666857041920 : R) * h ^ 5 * t0 ^ 2 * a3 ^ 3
    + (27562029719507435520 : R) * h ^ 5 * t0 * v1 * u1 * a4 * a1
    + (27562029719507435520 : R) * h ^ 5 * t0 * v1 * u1 * a3 * a2
    + (4593671619917905920 : R) * h ^ 5 * t0 * u1 ^ 3 * a1
    + (7177611906121728000 : R) * h ^ 5 * v1 ^ 3 * a4 * a1
    + (7177611906121728000 : R) * h ^ 5 * v1 ^ 3 * a3 * a2
    + (10766417859182592000 : R) * h ^ 5 * v1 ^ 2 * u1 ^ 2 * a1
    - (2422444018316083200 : R) * h ^ 4 * t0 ^ 2 * a4 ^ 2 * a2 * lambda
    + (13781014859753717760 : R) * h ^ 3 * t0 * v1 * a4 ^ 2 * a2
    + (13781014859753717760 : R) * h ^ 3 * t0 * v1 * a4 * a3 ^ 2
    + (13781014859753717760 : R) * h ^ 3 * t0 * u1 ^ 2 * a4 * a2
    + (6890507429876858880 : R) * h ^ 3 * t0 * u1 ^ 2 * a3 ^ 2
    + (21532835718365184000 : R) * h ^ 3 * v1 ^ 2 * u1 * a4 * a2
    + (10766417859182592000 : R) * h ^ 3 * v1 ^ 2 * u1 * a3 ^ 2
    + (7177611906121728000 : R) * h ^ 3 * v1 * u1 ^ 3 * a2
    + (13781014859753717760 : R) * h * t0 * u1 * a4 ^ 2 * a3
    + (10766417859182592000 : R) * h * v1 ^ 2 * a4 ^ 2 * a3
    + (21532835718365184000 : R) * h * v1 * u1 ^ 2 * a4 * a3
    + (1794402976530432000 : R) * h * u1 ^ 4 * a3

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock4_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock4_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock4_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock4_810,
    degreeZeroSourceJetHeadBlock4_810,
    degreeZeroSourceJetPlusBlock4_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `5` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock5_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2422444018316083200 : R) * h ^ 95 * a7 ^ 2 * a4 * a3 ^ 2 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a7 * a6 ^ 2 * a5 * a0 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a7 * a6 ^ 2 * a4 * a1 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a7 * a6 ^ 2 * a3 * a2 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a7 * a6 * a5 ^ 2 * a1 * lambda
    - (9689776073264332800 : R) * h ^ 95 * a7 * a6 * a5 * a4 * a2 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a7 * a6 * a5 * a3 ^ 2 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a7 * a6 * a4 ^ 2 * a3 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a7 * a5 ^ 3 * a2 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a7 * a5 ^ 2 * a4 * a3 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a7 * a5 * a4 ^ 3 * lambda
    - (403740669719347200 : R) * h ^ 95 * a6 ^ 4 * a0 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a6 ^ 3 * a5 * a1 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a6 ^ 3 * a4 * a2 * lambda
    - (807481339438694400 : R) * h ^ 95 * a6 ^ 3 * a3 ^ 2 * lambda
    - (2422444018316083200 : R) * h ^ 95 * a6 ^ 2 * a5 ^ 2 * a2 * lambda
    - (4844888036632166400 : R) * h ^ 95 * a6 ^ 2 * a5 * a4 * a3 * lambda
    - (807481339438694400 : R) * h ^ 95 * a6 ^ 2 * a4 ^ 3 * lambda
    - (1614962678877388800 : R) * h ^ 95 * a6 * a5 ^ 3 * a3 * lambda
    - (2422444018316083200 : R) * h ^ 95 * a6 * a5 ^ 2 * a4 ^ 2 * lambda
    - (403740669719347200 : R) * h ^ 95 * a5 ^ 4 * a4 * lambda
    - (229683580995895296 : R) * h ^ 94 * a7 ^ 3 * a3 * b1
    - (459367161991790592 : R) * h ^ 94 * a7 ^ 3 * a2 * b2
    - (689050742987685888 : R) * h ^ 94 * a7 ^ 3 * a1 * b3
    - (918734323983581184 : R) * h ^ 94 * a7 ^ 3 * a0 * b4
    - (689050742987685888 : R) * h ^ 94 * a7 ^ 2 * a6 * a4 * b1
    - (1378101485975371776 : R) * h ^ 94 * a7 ^ 2 * a6 * a3 * b2
    - (2067152228963057664 : R) * h ^ 94 * a7 ^ 2 * a6 * a2 * b3
    - (2756202971950743552 : R) * h ^ 94 * a7 ^ 2 * a6 * a1 * b4
    - (3445253714938429440 : R) * h ^ 94 * a7 ^ 2 * a6 * a0 * b5
    - (344525371493842944 : R) * h ^ 94 * a7 ^ 2 * a5 ^ 2 * b1
    - (1378101485975371776 : R) * h ^ 94 * a7 ^ 2 * a5 * a4 * b2
    - (2067152228963057664 : R) * h ^ 94 * a7 ^ 2 * a5 * a3 * b3
    - (2756202971950743552 : R) * h ^ 94 * a7 ^ 2 * a5 * a2 * b4
    - (3445253714938429440 : R) * h ^ 94 * a7 ^ 2 * a5 * a1 * b5
    - (4134304457926115328 : R) * h ^ 94 * a7 ^ 2 * a5 * a0 * b6
    - (1033576114481528832 : R) * h ^ 94 * a7 ^ 2 * a4 ^ 2 * b3
    - (2756202971950743552 : R) * h ^ 94 * a7 ^ 2 * a4 * a3 * b4
    - (3445253714938429440 : R) * h ^ 94 * a7 ^ 2 * a4 * a2 * b5
    - (4134304457926115328 : R) * h ^ 94 * a7 ^ 2 * a4 * a1 * b6

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `5`. -/
def degreeZeroSourceJetHeadBlock5_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `5`. -/
def degreeZeroSourceJetPlusBlock5_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (229683580995895296 : R) * h ^ 9 * t0 ^ 3 * a3 * b1
    - (459367161991790592 : R) * h ^ 9 * t0 ^ 3 * a2 * b2
    - (689050742987685888 : R) * h ^ 9 * t0 ^ 3 * a1 * b3
    - (918734323983581184 : R) * h ^ 9 * t0 ^ 3 * a0 * b4
    - (4844888036632166400 : R) * h ^ 8 * t0 * v1 ^ 2 * u1 * a0 * lambda
    - (403740669719347200 : R) * h ^ 8 * v1 ^ 4 * a0 * lambda
    - (689050742987685888 : R) * h ^ 7 * t0 ^ 2 * v1 * a4 * b1
    - (1378101485975371776 : R) * h ^ 7 * t0 ^ 2 * v1 * a3 * b2
    - (2067152228963057664 : R) * h ^ 7 * t0 ^ 2 * v1 * a2 * b3
    - (2756202971950743552 : R) * h ^ 7 * t0 ^ 2 * v1 * a1 * b4
    - (3445253714938429440 : R) * h ^ 7 * t0 ^ 2 * v1 * a0 * b5
    - (344525371493842944 : R) * h ^ 7 * t0 ^ 2 * u1 ^ 2 * b1
    - (4134304457926115328 : R) * h ^ 7 * t0 ^ 2 * u1 * a0 * b62
    - (4844888036632166400 : R) * h ^ 6 * t0 * v1 ^ 2 * a4 * a1 * lambda
    - (4844888036632166400 : R) * h ^ 6 * t0 * v1 ^ 2 * a3 * a2 * lambda
    - (4844888036632166400 : R) * h ^ 6 * t0 * v1 * u1 ^ 2 * a1 * lambda
    - (1614962678877388800 : R) * h ^ 6 * v1 ^ 3 * u1 * a1 * lambda
    - (1378101485975371776 : R) * h ^ 5 * t0 ^ 2 * u1 * a4 * b2
    - (2067152228963057664 : R) * h ^ 5 * t0 ^ 2 * u1 * a3 * b3
    - (2756202971950743552 : R) * h ^ 5 * t0 ^ 2 * u1 * a2 * b4
    - (3445253714938429440 : R) * h ^ 5 * t0 ^ 2 * u1 * a1 * b5
    - (4134304457926115328 : R) * h ^ 5 * t0 ^ 2 * a4 * a1 * b62
    - (2422444018316083200 : R) * h ^ 4 * t0 ^ 2 * a4 * a3 ^ 2 * lambda
    - (9689776073264332800 : R) * h ^ 4 * t0 * v1 * u1 * a4 * a2 * lambda
    - (4844888036632166400 : R) * h ^ 4 * t0 * v1 * u1 * a3 ^ 2 * lambda
    - (1614962678877388800 : R) * h ^ 4 * t0 * u1 ^ 3 * a2 * lambda
    - (1614962678877388800 : R) * h ^ 4 * v1 ^ 3 * a4 * a2 * lambda
    - (807481339438694400 : R) * h ^ 4 * v1 ^ 3 * a3 ^ 2 * lambda
    - (2422444018316083200 : R) * h ^ 4 * v1 ^ 2 * u1 ^ 2 * a2 * lambda
    - (1033576114481528832 : R) * h ^ 3 * t0 ^ 2 * a4 ^ 2 * b3
    - (2756202971950743552 : R) * h ^ 3 * t0 ^ 2 * a4 * a3 * b4
    - (3445253714938429440 : R) * h ^ 3 * t0 ^ 2 * a4 * a2 * b5
    - (4844888036632166400 : R) * h ^ 2 * t0 * v1 * a4 ^ 2 * a3 * lambda
    - (4844888036632166400 : R) * h ^ 2 * t0 * u1 ^ 2 * a4 * a3 * lambda
    - (4844888036632166400 : R) * h ^ 2 * v1 ^ 2 * u1 * a4 * a3 * lambda
    - (1614962678877388800 : R) * h ^ 2 * v1 * u1 ^ 3 * a3 * lambda
    - (1614962678877388800 : R) * t0 * u1 * a4 ^ 3 * lambda
    - (807481339438694400 : R) * v1 ^ 2 * a4 ^ 3 * lambda
    - (2422444018316083200 : R) * v1 * u1 ^ 2 * a4 ^ 2 * lambda
    - (403740669719347200 : R) * u1 ^ 4 * a4 * lambda

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock5_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock5_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock5_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock5_810,
    degreeZeroSourceJetHeadBlock5_810,
    degreeZeroSourceJetPlusBlock5_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `6` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock6_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4823355200913801216 : R) * h ^ 94 * a7 ^ 2 * a4 * a0 * b7
    - (1722626857469214720 : R) * h ^ 94 * a7 ^ 2 * a3 ^ 2 * b5
    - (4134304457926115328 : R) * h ^ 94 * a7 ^ 2 * a3 * a2 * b6
    - (4823355200913801216 : R) * h ^ 94 * a7 ^ 2 * a3 * a1 * b7
    - (5512405943901487104 : R) * h ^ 94 * a7 ^ 2 * a3 * a0 * b8
    - (2411677600456900608 : R) * h ^ 94 * a7 ^ 2 * a2 ^ 2 * b7
    - (5512405943901487104 : R) * h ^ 94 * a7 ^ 2 * a2 * a1 * b8
    - (689050742987685888 : R) * h ^ 94 * a7 * a6 ^ 2 * a5 * b1
    - (1378101485975371776 : R) * h ^ 94 * a7 * a6 ^ 2 * a4 * b2
    - (2067152228963057664 : R) * h ^ 94 * a7 * a6 ^ 2 * a3 * b3
    - (2756202971950743552 : R) * h ^ 94 * a7 * a6 ^ 2 * a2 * b4
    - (3445253714938429440 : R) * h ^ 94 * a7 * a6 ^ 2 * a1 * b5
    - (4134304457926115328 : R) * h ^ 94 * a7 * a6 ^ 2 * a0 * b6
    - (1378101485975371776 : R) * h ^ 94 * a7 * a6 * a5 ^ 2 * b2
    - (4134304457926115328 : R) * h ^ 94 * a7 * a6 * a5 * a4 * b3
    - (5512405943901487104 : R) * h ^ 94 * a7 * a6 * a5 * a3 * b4
    - (6890507429876858880 : R) * h ^ 94 * a7 * a6 * a5 * a2 * b5
    - (8268608915852230656 : R) * h ^ 94 * a7 * a6 * a5 * a1 * b6
    - (9646710401827602432 : R) * h ^ 94 * a7 * a6 * a5 * a0 * b7
    - (2756202971950743552 : R) * h ^ 94 * a7 * a6 * a4 ^ 2 * b4
    - (6890507429876858880 : R) * h ^ 94 * a7 * a6 * a4 * a3 * b5
    - (8268608915852230656 : R) * h ^ 94 * a7 * a6 * a4 * a2 * b6
    - (9646710401827602432 : R) * h ^ 94 * a7 * a6 * a4 * a1 * b7
    - (11024811887802974208 : R) * h ^ 94 * a7 * a6 * a4 * a0 * b8
    - (4134304457926115328 : R) * h ^ 94 * a7 * a6 * a3 ^ 2 * b6
    - (9646710401827602432 : R) * h ^ 94 * a7 * a6 * a3 * a2 * b7
    - (11024811887802974208 : R) * h ^ 94 * a7 * a6 * a3 * a1 * b8
    - (5512405943901487104 : R) * h ^ 94 * a7 * a6 * a2 ^ 2 * b8
    - (689050742987685888 : R) * h ^ 94 * a7 * a5 ^ 3 * b3
    - (2756202971950743552 : R) * h ^ 94 * a7 * a5 ^ 2 * a4 * b4
    - (3445253714938429440 : R) * h ^ 94 * a7 * a5 ^ 2 * a3 * b5
    - (4134304457926115328 : R) * h ^ 94 * a7 * a5 ^ 2 * a2 * b6
    - (4823355200913801216 : R) * h ^ 94 * a7 * a5 ^ 2 * a1 * b7
    - (5512405943901487104 : R) * h ^ 94 * a7 * a5 ^ 2 * a0 * b8
    - (3445253714938429440 : R) * h ^ 94 * a7 * a5 * a4 ^ 2 * b5
    - (8268608915852230656 : R) * h ^ 94 * a7 * a5 * a4 * a3 * b6
    - (9646710401827602432 : R) * h ^ 94 * a7 * a5 * a4 * a2 * b7
    - (11024811887802974208 : R) * h ^ 94 * a7 * a5 * a4 * a1 * b8
    - (4823355200913801216 : R) * h ^ 94 * a7 * a5 * a3 ^ 2 * b7
    - (11024811887802974208 : R) * h ^ 94 * a7 * a5 * a3 * a2 * b8

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `6`. -/
def degreeZeroSourceJetHeadBlock6_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (3445253714938429440 : R) * t0 * u1 * a4 ^ 2 * b5

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `6`. -/
def degreeZeroSourceJetPlusBlock6_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5512405943901487104 : R) * h ^ 9 * t0 ^ 2 * a3 * a0 * s1
    - (5512405943901487104 : R) * h ^ 9 * t0 ^ 2 * a2 * a1 * s1
    - (4823355200913801216 : R) * h ^ 7 * t0 ^ 2 * a4 * a0 * w1
    - (4823355200913801216 : R) * h ^ 7 * t0 ^ 2 * a3 * a1 * w1
    - (2411677600456900608 : R) * h ^ 7 * t0 ^ 2 * a2 ^ 2 * w1
    - (689050742987685888 : R) * h ^ 7 * t0 * v1 ^ 2 * u1 * b1
    - (4134304457926115328 : R) * h ^ 7 * t0 * v1 ^ 2 * a0 * b62
    - (9646710401827602432 : R) * h ^ 7 * t0 * v1 * u1 * a0 * w1
    - (11024811887802974208 : R) * h ^ 7 * t0 * v1 * a4 * a0 * s1
    - (11024811887802974208 : R) * h ^ 7 * t0 * v1 * a3 * a1 * s1
    - (5512405943901487104 : R) * h ^ 7 * t0 * v1 * a2 ^ 2 * s1
    - (5512405943901487104 : R) * h ^ 7 * t0 * u1 ^ 2 * a0 * s1
    - (4134304457926115328 : R) * h ^ 5 * t0 ^ 2 * a3 * a2 * b62
    - (1378101485975371776 : R) * h ^ 5 * t0 * v1 ^ 2 * a4 * b2
    - (2067152228963057664 : R) * h ^ 5 * t0 * v1 ^ 2 * a3 * b3
    - (2756202971950743552 : R) * h ^ 5 * t0 * v1 ^ 2 * a2 * b4
    - (3445253714938429440 : R) * h ^ 5 * t0 * v1 ^ 2 * a1 * b5
    - (1378101485975371776 : R) * h ^ 5 * t0 * v1 * u1 ^ 2 * b2
    - (8268608915852230656 : R) * h ^ 5 * t0 * v1 * u1 * a1 * b62
    - (9646710401827602432 : R) * h ^ 5 * t0 * v1 * a4 * a1 * w1
    - (9646710401827602432 : R) * h ^ 5 * t0 * v1 * a3 * a2 * w1
    - (4823355200913801216 : R) * h ^ 5 * t0 * u1 ^ 2 * a1 * w1
    - (11024811887802974208 : R) * h ^ 5 * t0 * u1 * a4 * a1 * s1
    - (11024811887802974208 : R) * h ^ 5 * t0 * u1 * a3 * a2 * s1
    - (1722626857469214720 : R) * h ^ 3 * t0 ^ 2 * a3 ^ 2 * b5
    - (4134304457926115328 : R) * h ^ 3 * t0 * v1 * u1 * a4 * b3
    - (5512405943901487104 : R) * h ^ 3 * t0 * v1 * u1 * a3 * b4
    - (6890507429876858880 : R) * h ^ 3 * t0 * v1 * u1 * a2 * b5
    - (8268608915852230656 : R) * h ^ 3 * t0 * v1 * a4 * a2 * b62
    - (4134304457926115328 : R) * h ^ 3 * t0 * v1 * a3 ^ 2 * b62
    - (689050742987685888 : R) * h ^ 3 * t0 * u1 ^ 3 * b3
    - (4134304457926115328 : R) * h ^ 3 * t0 * u1 ^ 2 * a2 * b62
    - (9646710401827602432 : R) * h ^ 3 * t0 * u1 * a4 * a2 * w1
    - (4823355200913801216 : R) * h ^ 3 * t0 * u1 * a3 ^ 2 * w1
    - (2756202971950743552 : R) * h * t0 * v1 * a4 ^ 2 * b4
    - (6890507429876858880 : R) * h * t0 * v1 * a4 * a3 * b5
    - (2756202971950743552 : R) * h * t0 * u1 ^ 2 * a4 * b4
    - (3445253714938429440 : R) * h * t0 * u1 ^ 2 * a3 * b5
    - (8268608915852230656 : R) * h * t0 * u1 * a4 * a3 * b62

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock6_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock6_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock6_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock6_810,
    degreeZeroSourceJetHeadBlock6_810,
    degreeZeroSourceJetPlusBlock6_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `7` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock7_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1378101485975371776 : R) * h ^ 94 * a7 * a4 ^ 3 * b6
    - (4823355200913801216 : R) * h ^ 94 * a7 * a4 ^ 2 * a3 * b7
    - (5512405943901487104 : R) * h ^ 94 * a7 * a4 ^ 2 * a2 * b8
    - (5512405943901487104 : R) * h ^ 94 * a7 * a4 * a3 ^ 2 * b8
    - (57420895248973824 : R) * h ^ 94 * a6 ^ 4 * b1
    - (459367161991790592 : R) * h ^ 94 * a6 ^ 3 * a5 * b2
    - (689050742987685888 : R) * h ^ 94 * a6 ^ 3 * a4 * b3
    - (918734323983581184 : R) * h ^ 94 * a6 ^ 3 * a3 * b4
    - (1148417904979476480 : R) * h ^ 94 * a6 ^ 3 * a2 * b5
    - (1378101485975371776 : R) * h ^ 94 * a6 ^ 3 * a1 * b6
    - (1607785066971267072 : R) * h ^ 94 * a6 ^ 3 * a0 * b7
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
    - (287104476244869120 : R) * h ^ 94 * a5 ^ 4 * b5
    - (1378101485975371776 : R) * h ^ 94 * a5 ^ 3 * a4 * b6
    - (1607785066971267072 : R) * h ^ 94 * a5 ^ 3 * a3 * b7
    - (1837468647967162368 : R) * h ^ 94 * a5 ^ 3 * a2 * b8
    - (2411677600456900608 : R) * h ^ 94 * a5 ^ 2 * a4 ^ 2 * b7
    - (5512405943901487104 : R) * h ^ 94 * a5 ^ 2 * a4 * a3 * b8

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `7`. -/
def degreeZeroSourceJetHeadBlock7_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1378101485975371776 : R) * t0 * a4 ^ 3 * b62
    - (1722626857469214720 : R) * v1 ^ 2 * a4 ^ 2 * b5
    - (3445253714938429440 : R) * v1 * u1 ^ 2 * a4 * b5
    - (4134304457926115328 : R) * v1 * u1 * a4 ^ 2 * b62
    - (1607785066971267072 : R) * v1 * a4 ^ 3 * w1
    - (287104476244869120 : R) * u1 ^ 4 * b5
    - (1378101485975371776 : R) * u1 ^ 3 * a4 * b62
    - (2411677600456900608 : R) * u1 ^ 2 * a4 ^ 2 * w1

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `7`. -/
def degreeZeroSourceJetPlusBlock7_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (57420895248973824 : R) * h ^ 7 * v1 ^ 4 * b1
    - (1607785066971267072 : R) * h ^ 7 * v1 ^ 3 * a0 * w1
    - (5512405943901487104 : R) * h ^ 7 * v1 ^ 2 * u1 * a0 * s1
    - (459367161991790592 : R) * h ^ 5 * v1 ^ 3 * u1 * b2
    - (1378101485975371776 : R) * h ^ 5 * v1 ^ 3 * a1 * b62
    - (4823355200913801216 : R) * h ^ 5 * v1 ^ 2 * u1 * a1 * w1
    - (5512405943901487104 : R) * h ^ 5 * v1 ^ 2 * a4 * a1 * s1
    - (5512405943901487104 : R) * h ^ 5 * v1 ^ 2 * a3 * a2 * s1
    - (5512405943901487104 : R) * h ^ 5 * v1 * u1 ^ 2 * a1 * s1
    - (5512405943901487104 : R) * h ^ 3 * t0 * a4 ^ 2 * a2 * s1
    - (5512405943901487104 : R) * h ^ 3 * t0 * a4 * a3 ^ 2 * s1
    - (689050742987685888 : R) * h ^ 3 * v1 ^ 3 * a4 * b3
    - (918734323983581184 : R) * h ^ 3 * v1 ^ 3 * a3 * b4
    - (1148417904979476480 : R) * h ^ 3 * v1 ^ 3 * a2 * b5
    - (1033576114481528832 : R) * h ^ 3 * v1 ^ 2 * u1 ^ 2 * b3
    - (4134304457926115328 : R) * h ^ 3 * v1 ^ 2 * u1 * a2 * b62
    - (4823355200913801216 : R) * h ^ 3 * v1 ^ 2 * a4 * a2 * w1
    - (2411677600456900608 : R) * h ^ 3 * v1 ^ 2 * a3 ^ 2 * w1
    - (4823355200913801216 : R) * h ^ 3 * v1 * u1 ^ 2 * a2 * w1
    - (11024811887802974208 : R) * h ^ 3 * v1 * u1 * a4 * a2 * s1
    - (5512405943901487104 : R) * h ^ 3 * v1 * u1 * a3 ^ 2 * s1
    - (1837468647967162368 : R) * h ^ 3 * u1 ^ 3 * a2 * s1
    - (4823355200913801216 : R) * h * t0 * a4 ^ 2 * a3 * w1
    - (2756202971950743552 : R) * h * v1 ^ 2 * u1 * a4 * b4
    - (3445253714938429440 : R) * h * v1 ^ 2 * u1 * a3 * b5
    - (4134304457926115328 : R) * h * v1 ^ 2 * a4 * a3 * b62
    - (918734323983581184 : R) * h * v1 * u1 ^ 3 * b4
    - (4134304457926115328 : R) * h * v1 * u1 ^ 2 * a3 * b62
    - (9646710401827602432 : R) * h * v1 * u1 * a4 * a3 * w1
    - (5512405943901487104 : R) * h * v1 * a4 ^ 2 * a3 * s1
    - (1607785066971267072 : R) * h * u1 ^ 3 * a3 * w1
    - (5512405943901487104 : R) * h * u1 ^ 2 * a4 * a3 * s1

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock7_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock7_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock7_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock7_810,
    degreeZeroSourceJetHeadBlock7_810,
    degreeZeroSourceJetPlusBlock7_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `8` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock8_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1837468647967162368 : R) * h ^ 94 * a5 * a4 ^ 3 * b8
    + (672901116198912000 : R) * h ^ 88 * a7 ^ 4 * a3 * a0
    + (672901116198912000 : R) * h ^ 88 * a7 ^ 4 * a2 * a1
    - (5383208929591296000 : R) * h ^ 88 * a7 ^ 3 * a6 * a4 * a0
    - (5383208929591296000 : R) * h ^ 88 * a7 ^ 3 * a6 * a3 * a1
    - (2691604464795648000 : R) * h ^ 88 * a7 ^ 3 * a6 * a2 ^ 2
    - (2691604464795648000 : R) * h ^ 88 * a7 ^ 3 * a5 ^ 2 * a0
    - (5383208929591296000 : R) * h ^ 88 * a7 ^ 3 * a5 * a4 * a1
    - (5383208929591296000 : R) * h ^ 88 * a7 ^ 3 * a5 * a3 * a2
    - (2691604464795648000 : R) * h ^ 88 * a7 ^ 3 * a4 ^ 2 * a2
    - (2691604464795648000 : R) * h ^ 88 * a7 ^ 3 * a4 * a3 ^ 2
    - (20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a5 * a0
    - (20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a4 * a1
    - (20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 ^ 2 * a3 * a2
    - (20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 ^ 2 * a1
    - (40374066971934720000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a4 * a2
    - (20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 * a5 * a3 ^ 2
    - (20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a6 * a4 ^ 2 * a3
    - (6729011161989120000 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 3 * a2
    - (20187033485967360000 : R) * h ^ 88 * a7 ^ 2 * a5 ^ 2 * a4 * a3
    - (6729011161989120000 : R) * h ^ 88 * a7 ^ 2 * a5 * a4 ^ 3
    - (5383208929591296000 : R) * h ^ 88 * a7 * a6 ^ 4 * a0
    - (21532835718365184000 : R) * h ^ 88 * a7 * a6 ^ 3 * a5 * a1
    - (21532835718365184000 : R) * h ^ 88 * a7 * a6 ^ 3 * a4 * a2
    - (10766417859182592000 : R) * h ^ 88 * a7 * a6 ^ 3 * a3 ^ 2
    - (32299253577547776000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 ^ 2 * a2
    - (64598507155095552000 : R) * h ^ 88 * a7 * a6 ^ 2 * a5 * a4 * a3
    - (10766417859182592000 : R) * h ^ 88 * a7 * a6 ^ 2 * a4 ^ 3
    - (21532835718365184000 : R) * h ^ 88 * a7 * a6 * a5 ^ 3 * a3
    - (32299253577547776000 : R) * h ^ 88 * a7 * a6 * a5 ^ 2 * a4 ^ 2
    - (5383208929591296000 : R) * h ^ 88 * a7 * a5 ^ 4 * a4
    - (1480382455637606400 : R) * h ^ 88 * a6 ^ 5 * a1
    - (7401912278188032000 : R) * h ^ 88 * a6 ^ 4 * a5 * a2
    - (7401912278188032000 : R) * h ^ 88 * a6 ^ 4 * a4 * a3
    - (14803824556376064000 : R) * h ^ 88 * a6 ^ 3 * a5 ^ 2 * a3
    - (14803824556376064000 : R) * h ^ 88 * a6 ^ 3 * a5 * a4 ^ 2
    - (14803824556376064000 : R) * h ^ 88 * a6 ^ 2 * a5 ^ 3 * a4
    - (1480382455637606400 : R) * h ^ 88 * a6 * a5 ^ 5
    + (1665430262592307200 : R) * h ^ 87 * a7 ^ 4 * a4 * a0 * lambda
    + (1665430262592307200 : R) * h ^ 87 * a7 ^ 4 * a3 * a1 * lambda

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `8`. -/
def degreeZeroSourceJetHeadBlock8_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (6729011161989120000 : R) * t0 ^ 2 * u1 * a4 ^ 3
    - (10766417859182592000 : R) * t0 * v1 ^ 2 * a4 ^ 3
    - (32299253577547776000 : R) * t0 * v1 * u1 ^ 2 * a4 ^ 2
    - (5383208929591296000 : R) * t0 * u1 ^ 4 * a4
    - (14803824556376064000 : R) * v1 ^ 3 * u1 * a4 ^ 2
    - (14803824556376064000 : R) * v1 ^ 2 * u1 ^ 3 * a4
    - (1480382455637606400 : R) * v1 * u1 ^ 5
    - (1837468647967162368 : R) * u1 * a4 ^ 3 * s1

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `8`. -/
def degreeZeroSourceJetPlusBlock8_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (672901116198912000 : R) * h ^ 9 * t0 ^ 4 * a3 * a0
    + (672901116198912000 : R) * h ^ 9 * t0 ^ 4 * a2 * a1
    + (1665430262592307200 : R) * h ^ 8 * t0 ^ 4 * a4 * a0 * lambda
    + (1665430262592307200 : R) * h ^ 8 * t0 ^ 4 * a3 * a1 * lambda
    - (5383208929591296000 : R) * h ^ 7 * t0 ^ 3 * v1 * a4 * a0
    - (5383208929591296000 : R) * h ^ 7 * t0 ^ 3 * v1 * a3 * a1
    - (2691604464795648000 : R) * h ^ 7 * t0 ^ 3 * v1 * a2 ^ 2
    - (2691604464795648000 : R) * h ^ 7 * t0 ^ 3 * u1 ^ 2 * a0
    - (20187033485967360000 : R) * h ^ 7 * t0 ^ 2 * v1 ^ 2 * u1 * a0
    - (5383208929591296000 : R) * h ^ 7 * t0 * v1 ^ 4 * a0
    - (5383208929591296000 : R) * h ^ 5 * t0 ^ 3 * u1 * a4 * a1
    - (5383208929591296000 : R) * h ^ 5 * t0 ^ 3 * u1 * a3 * a2
    - (20187033485967360000 : R) * h ^ 5 * t0 ^ 2 * v1 ^ 2 * a4 * a1
    - (20187033485967360000 : R) * h ^ 5 * t0 ^ 2 * v1 ^ 2 * a3 * a2
    - (20187033485967360000 : R) * h ^ 5 * t0 ^ 2 * v1 * u1 ^ 2 * a1
    - (21532835718365184000 : R) * h ^ 5 * t0 * v1 ^ 3 * u1 * a1
    - (1480382455637606400 : R) * h ^ 5 * v1 ^ 5 * a1
    - (2691604464795648000 : R) * h ^ 3 * t0 ^ 3 * a4 ^ 2 * a2
    - (2691604464795648000 : R) * h ^ 3 * t0 ^ 3 * a4 * a3 ^ 2
    - (40374066971934720000 : R) * h ^ 3 * t0 ^ 2 * v1 * u1 * a4 * a2
    - (20187033485967360000 : R) * h ^ 3 * t0 ^ 2 * v1 * u1 * a3 ^ 2
    - (6729011161989120000 : R) * h ^ 3 * t0 ^ 2 * u1 ^ 3 * a2
    - (21532835718365184000 : R) * h ^ 3 * t0 * v1 ^ 3 * a4 * a2
    - (10766417859182592000 : R) * h ^ 3 * t0 * v1 ^ 3 * a3 ^ 2
    - (32299253577547776000 : R) * h ^ 3 * t0 * v1 ^ 2 * u1 ^ 2 * a2
    - (7401912278188032000 : R) * h ^ 3 * v1 ^ 4 * u1 * a2
    - (20187033485967360000 : R) * h * t0 ^ 2 * v1 * a4 ^ 2 * a3
    - (20187033485967360000 : R) * h * t0 ^ 2 * u1 ^ 2 * a4 * a3
    - (64598507155095552000 : R) * h * t0 * v1 ^ 2 * u1 * a4 * a3
    - (21532835718365184000 : R) * h * t0 * v1 * u1 ^ 3 * a3
    - (7401912278188032000 : R) * h * v1 ^ 4 * a4 * a3
    - (14803824556376064000 : R) * h * v1 ^ 3 * u1 ^ 2 * a3

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock8_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock8_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock8_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock8_810,
    degreeZeroSourceJetHeadBlock8_810,
    degreeZeroSourceJetPlusBlock8_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `9` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock9_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (832715131296153600 : R) * h ^ 87 * a7 ^ 4 * a2 ^ 2 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 ^ 3 * a6 * a5 * a0 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 ^ 3 * a6 * a4 * a1 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 ^ 3 * a6 * a3 * a2 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 3 * a5 ^ 2 * a1 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 ^ 3 * a5 * a4 * a2 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 3 * a5 * a3 ^ 2 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 3 * a4 ^ 2 * a3 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 3 * a0 * lambda
    + (9992581575553843200 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a5 * a1 * lambda
    + (9992581575553843200 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a4 * a2 * lambda
    + (4996290787776921600 : R) * h ^ 87 * a7 ^ 2 * a6 ^ 2 * a3 ^ 2 * lambda
    + (9992581575553843200 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 ^ 2 * a2 * lambda
    + (19985163151107686400 : R) * h ^ 87 * a7 ^ 2 * a6 * a5 * a4 * a3 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 2 * a6 * a4 ^ 3 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 3 * a3 * lambda
    + (4996290787776921600 : R) * h ^ 87 * a7 ^ 2 * a5 ^ 2 * a4 ^ 2 * lambda
    + (1665430262592307200 : R) * h ^ 87 * a7 * a6 ^ 4 * a1 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 * a6 ^ 3 * a5 * a2 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 * a6 ^ 3 * a4 * a3 * lambda
    + (9992581575553843200 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 ^ 2 * a3 * lambda
    + (9992581575553843200 : R) * h ^ 87 * a7 * a6 ^ 2 * a5 * a4 ^ 2 * lambda
    + (6661721050369228800 : R) * h ^ 87 * a7 * a6 * a5 ^ 3 * a4 * lambda
    + (333086052518461440 : R) * h ^ 87 * a7 * a5 ^ 5 * lambda
    + (333086052518461440 : R) * h ^ 87 * a6 ^ 5 * a2 * lambda
    + (1665430262592307200 : R) * h ^ 87 * a6 ^ 4 * a5 * a3 * lambda
    + (832715131296153600 : R) * h ^ 87 * a6 ^ 4 * a4 ^ 2 * lambda
    + (3330860525184614400 : R) * h ^ 87 * a6 ^ 3 * a5 ^ 2 * a4 * lambda
    + (832715131296153600 : R) * h ^ 87 * a6 ^ 2 * a5 ^ 4 * lambda
    + (179440297653043200 : R) * h ^ 86 * a7 ^ 4 * a4 * b1
    + (358880595306086400 : R) * h ^ 86 * a7 ^ 4 * a3 * b2
    + (538320892959129600 : R) * h ^ 86 * a7 ^ 4 * a2 * b3
    + (717761190612172800 : R) * h ^ 86 * a7 ^ 4 * a1 * b4
    + (897201488265216000 : R) * h ^ 86 * a7 ^ 4 * a0 * b5
    + (717761190612172800 : R) * h ^ 86 * a7 ^ 3 * a6 * a5 * b1
    + (1435522381224345600 : R) * h ^ 86 * a7 ^ 3 * a6 * a4 * b2
    + (2153283571836518400 : R) * h ^ 86 * a7 ^ 3 * a6 * a3 * b3
    + (2871044762448691200 : R) * h ^ 86 * a7 ^ 3 * a6 * a2 * b4
    + (3588805953060864000 : R) * h ^ 86 * a7 ^ 3 * a6 * a1 * b5
    + (4306567143673036800 : R) * h ^ 86 * a7 ^ 3 * a6 * a0 * b6

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `9`. -/
def degreeZeroSourceJetHeadBlock9_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `9`. -/
def degreeZeroSourceJetPlusBlock9_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (832715131296153600 : R) * h ^ 8 * t0 ^ 4 * a2 ^ 2 * lambda
    + (6661721050369228800 : R) * h ^ 8 * t0 ^ 3 * v1 * u1 * a0 * lambda
    + (3330860525184614400 : R) * h ^ 8 * t0 ^ 2 * v1 ^ 3 * a0 * lambda
    + (179440297653043200 : R) * h ^ 7 * t0 ^ 4 * a4 * b1
    + (358880595306086400 : R) * h ^ 7 * t0 ^ 4 * a3 * b2
    + (538320892959129600 : R) * h ^ 7 * t0 ^ 4 * a2 * b3
    + (717761190612172800 : R) * h ^ 7 * t0 ^ 4 * a1 * b4
    + (897201488265216000 : R) * h ^ 7 * t0 ^ 4 * a0 * b5
    + (717761190612172800 : R) * h ^ 7 * t0 ^ 3 * v1 * u1 * b1
    + (4306567143673036800 : R) * h ^ 7 * t0 ^ 3 * v1 * a0 * b62
    + (6661721050369228800 : R) * h ^ 6 * t0 ^ 3 * v1 * a4 * a1 * lambda
    + (6661721050369228800 : R) * h ^ 6 * t0 ^ 3 * v1 * a3 * a2 * lambda
    + (3330860525184614400 : R) * h ^ 6 * t0 ^ 3 * u1 ^ 2 * a1 * lambda
    + (9992581575553843200 : R) * h ^ 6 * t0 ^ 2 * v1 ^ 2 * u1 * a1 * lambda
    + (1665430262592307200 : R) * h ^ 6 * t0 * v1 ^ 4 * a1 * lambda
    + (1435522381224345600 : R) * h ^ 5 * t0 ^ 3 * v1 * a4 * b2
    + (2153283571836518400 : R) * h ^ 5 * t0 ^ 3 * v1 * a3 * b3
    + (2871044762448691200 : R) * h ^ 5 * t0 ^ 3 * v1 * a2 * b4
    + (3588805953060864000 : R) * h ^ 5 * t0 ^ 3 * v1 * a1 * b5
    + (6661721050369228800 : R) * h ^ 4 * t0 ^ 3 * u1 * a4 * a2 * lambda
    + (3330860525184614400 : R) * h ^ 4 * t0 ^ 3 * u1 * a3 ^ 2 * lambda
    + (9992581575553843200 : R) * h ^ 4 * t0 ^ 2 * v1 ^ 2 * a4 * a2 * lambda
    + (4996290787776921600 : R) * h ^ 4 * t0 ^ 2 * v1 ^ 2 * a3 ^ 2 * lambda
    + (9992581575553843200 : R) * h ^ 4 * t0 ^ 2 * v1 * u1 ^ 2 * a2 * lambda
    + (6661721050369228800 : R) * h ^ 4 * t0 * v1 ^ 3 * u1 * a2 * lambda
    + (333086052518461440 : R) * h ^ 4 * v1 ^ 5 * a2 * lambda
    + (3330860525184614400 : R) * h ^ 2 * t0 ^ 3 * a4 ^ 2 * a3 * lambda
    + (19985163151107686400 : R) * h ^ 2 * t0 ^ 2 * v1 * u1 * a4 * a3 * lambda
    + (3330860525184614400 : R) * h ^ 2 * t0 ^ 2 * u1 ^ 3 * a3 * lambda
    + (6661721050369228800 : R) * h ^ 2 * t0 * v1 ^ 3 * a4 * a3 * lambda
    + (9992581575553843200 : R) * h ^ 2 * t0 * v1 ^ 2 * u1 ^ 2 * a3 * lambda
    + (1665430262592307200 : R) * h ^ 2 * v1 ^ 4 * u1 * a3 * lambda
    + (3330860525184614400 : R) * t0 ^ 2 * v1 * a4 ^ 3 * lambda
    + (4996290787776921600 : R) * t0 ^ 2 * u1 ^ 2 * a4 ^ 2 * lambda
    + (9992581575553843200 : R) * t0 * v1 ^ 2 * u1 * a4 ^ 2 * lambda
    + (6661721050369228800 : R) * t0 * v1 * u1 ^ 3 * a4 * lambda
    + (333086052518461440 : R) * t0 * u1 ^ 5 * lambda
    + (832715131296153600 : R) * v1 ^ 4 * a4 ^ 2 * lambda
    + (3330860525184614400 : R) * v1 ^ 3 * u1 ^ 2 * a4 * lambda
    + (832715131296153600 : R) * v1 ^ 2 * u1 ^ 4 * lambda

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock9_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock9_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock9_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock9_810,
    degreeZeroSourceJetHeadBlock9_810,
    degreeZeroSourceJetPlusBlock9_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `10` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock10_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (717761190612172800 : R) * h ^ 86 * a7 ^ 3 * a5 ^ 2 * b2
    + (2153283571836518400 : R) * h ^ 86 * a7 ^ 3 * a5 * a4 * b3
    + (2871044762448691200 : R) * h ^ 86 * a7 ^ 3 * a5 * a3 * b4
    + (3588805953060864000 : R) * h ^ 86 * a7 ^ 3 * a5 * a2 * b5
    + (4306567143673036800 : R) * h ^ 86 * a7 ^ 3 * a5 * a1 * b6
    + (5024328334285209600 : R) * h ^ 86 * a7 ^ 3 * a5 * a0 * b7
    + (1435522381224345600 : R) * h ^ 86 * a7 ^ 3 * a4 ^ 2 * b4
    + (3588805953060864000 : R) * h ^ 86 * a7 ^ 3 * a4 * a3 * b5
    + (4306567143673036800 : R) * h ^ 86 * a7 ^ 3 * a4 * a2 * b6
    + (5024328334285209600 : R) * h ^ 86 * a7 ^ 3 * a4 * a1 * b7
    + (5742089524897382400 : R) * h ^ 86 * a7 ^ 3 * a4 * a0 * b8
    + (2153283571836518400 : R) * h ^ 86 * a7 ^ 3 * a3 ^ 2 * b6
    + (5024328334285209600 : R) * h ^ 86 * a7 ^ 3 * a3 * a2 * b7
    + (5742089524897382400 : R) * h ^ 86 * a7 ^ 3 * a3 * a1 * b8
    + (2871044762448691200 : R) * h ^ 86 * a7 ^ 3 * a2 ^ 2 * b8
    + (358880595306086400 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 3 * b1
    + (2153283571836518400 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a5 * b2
    + (3229925357754777600 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a4 * b3
    + (4306567143673036800 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a3 * b4
    + (5383208929591296000 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a2 * b5
    + (6459850715509555200 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a1 * b6
    + (7536492501427814400 : R) * h ^ 86 * a7 ^ 2 * a6 ^ 2 * a0 * b7
    + (3229925357754777600 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 ^ 2 * b3
    + (8613134287346073600 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a4 * b4
    + (10766417859182592000 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a3 * b5
    + (12919701431019110400 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a2 * b6
    + (15072985002855628800 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a1 * b7
    + (17226268574692147200 : R) * h ^ 86 * a7 ^ 2 * a6 * a5 * a0 * b8
    + (5383208929591296000 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 ^ 2 * b5
    + (12919701431019110400 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a3 * b6
    + (15072985002855628800 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a2 * b7
    + (17226268574692147200 : R) * h ^ 86 * a7 ^ 2 * a6 * a4 * a1 * b8
    + (7536492501427814400 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 ^ 2 * b7
    + (17226268574692147200 : R) * h ^ 86 * a7 ^ 2 * a6 * a3 * a2 * b8
    + (1435522381224345600 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 3 * b4
    + (5383208929591296000 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a4 * b5
    + (6459850715509555200 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a3 * b6
    + (7536492501427814400 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a2 * b7
    + (8613134287346073600 : R) * h ^ 86 * a7 ^ 2 * a5 ^ 2 * a1 * b8
    + (6459850715509555200 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 ^ 2 * b6

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `10`. -/
def degreeZeroSourceJetHeadBlock10_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (5383208929591296000 : R) * t0 ^ 2 * v1 * a4 ^ 2 * b5
    + (5383208929591296000 : R) * t0 ^ 2 * u1 ^ 2 * a4 * b5
    + (6459850715509555200 : R) * t0 ^ 2 * u1 * a4 ^ 2 * b62

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `10`. -/
def degreeZeroSourceJetPlusBlock10_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (5024328334285209600 : R) * h ^ 7 * t0 ^ 3 * u1 * a0 * w1
    + (5742089524897382400 : R) * h ^ 7 * t0 ^ 3 * a4 * a0 * s1
    + (5742089524897382400 : R) * h ^ 7 * t0 ^ 3 * a3 * a1 * s1
    + (2871044762448691200 : R) * h ^ 7 * t0 ^ 3 * a2 ^ 2 * s1
    + (358880595306086400 : R) * h ^ 7 * t0 ^ 2 * v1 ^ 3 * b1
    + (7536492501427814400 : R) * h ^ 7 * t0 ^ 2 * v1 ^ 2 * a0 * w1
    + (17226268574692147200 : R) * h ^ 7 * t0 ^ 2 * v1 * u1 * a0 * s1
    + (717761190612172800 : R) * h ^ 5 * t0 ^ 3 * u1 ^ 2 * b2
    + (4306567143673036800 : R) * h ^ 5 * t0 ^ 3 * u1 * a1 * b62
    + (5024328334285209600 : R) * h ^ 5 * t0 ^ 3 * a4 * a1 * w1
    + (5024328334285209600 : R) * h ^ 5 * t0 ^ 3 * a3 * a2 * w1
    + (2153283571836518400 : R) * h ^ 5 * t0 ^ 2 * v1 ^ 2 * u1 * b2
    + (6459850715509555200 : R) * h ^ 5 * t0 ^ 2 * v1 ^ 2 * a1 * b62
    + (15072985002855628800 : R) * h ^ 5 * t0 ^ 2 * v1 * u1 * a1 * w1
    + (17226268574692147200 : R) * h ^ 5 * t0 ^ 2 * v1 * a4 * a1 * s1
    + (17226268574692147200 : R) * h ^ 5 * t0 ^ 2 * v1 * a3 * a2 * s1
    + (8613134287346073600 : R) * h ^ 5 * t0 ^ 2 * u1 ^ 2 * a1 * s1
    + (2153283571836518400 : R) * h ^ 3 * t0 ^ 3 * u1 * a4 * b3
    + (2871044762448691200 : R) * h ^ 3 * t0 ^ 3 * u1 * a3 * b4
    + (3588805953060864000 : R) * h ^ 3 * t0 ^ 3 * u1 * a2 * b5
    + (4306567143673036800 : R) * h ^ 3 * t0 ^ 3 * a4 * a2 * b62
    + (2153283571836518400 : R) * h ^ 3 * t0 ^ 3 * a3 ^ 2 * b62
    + (3229925357754777600 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 2 * a4 * b3
    + (4306567143673036800 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 2 * a3 * b4
    + (5383208929591296000 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 2 * a2 * b5
    + (3229925357754777600 : R) * h ^ 3 * t0 ^ 2 * v1 * u1 ^ 2 * b3
    + (12919701431019110400 : R) * h ^ 3 * t0 ^ 2 * v1 * u1 * a2 * b62
    + (15072985002855628800 : R) * h ^ 3 * t0 ^ 2 * v1 * a4 * a2 * w1
    + (7536492501427814400 : R) * h ^ 3 * t0 ^ 2 * v1 * a3 ^ 2 * w1
    + (7536492501427814400 : R) * h ^ 3 * t0 ^ 2 * u1 ^ 2 * a2 * w1
    + (1435522381224345600 : R) * h * t0 ^ 3 * a4 ^ 2 * b4
    + (3588805953060864000 : R) * h * t0 ^ 3 * a4 * a3 * b5
    + (8613134287346073600 : R) * h * t0 ^ 2 * v1 * u1 * a4 * b4
    + (10766417859182592000 : R) * h * t0 ^ 2 * v1 * u1 * a3 * b5
    + (12919701431019110400 : R) * h * t0 ^ 2 * v1 * a4 * a3 * b62
    + (1435522381224345600 : R) * h * t0 ^ 2 * u1 ^ 3 * b4
    + (6459850715509555200 : R) * h * t0 ^ 2 * u1 ^ 2 * a3 * b62

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock10_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock10_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock10_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock10_810,
    degreeZeroSourceJetHeadBlock10_810,
    degreeZeroSourceJetPlusBlock10_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `11` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock11_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (15072985002855628800 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a3 * b7
    + (17226268574692147200 : R) * h ^ 86 * a7 ^ 2 * a5 * a4 * a2 * b8
    + (8613134287346073600 : R) * h ^ 86 * a7 ^ 2 * a5 * a3 ^ 2 * b8
    + (2512164167142604800 : R) * h ^ 86 * a7 ^ 2 * a4 ^ 3 * b7
    + (8613134287346073600 : R) * h ^ 86 * a7 ^ 2 * a4 ^ 2 * a3 * b8
    + (358880595306086400 : R) * h ^ 86 * a7 * a6 ^ 4 * b2
    + (2153283571836518400 : R) * h ^ 86 * a7 * a6 ^ 3 * a5 * b3
    + (2871044762448691200 : R) * h ^ 86 * a7 * a6 ^ 3 * a4 * b4
    + (3588805953060864000 : R) * h ^ 86 * a7 * a6 ^ 3 * a3 * b5
    + (4306567143673036800 : R) * h ^ 86 * a7 * a6 ^ 3 * a2 * b6
    + (5024328334285209600 : R) * h ^ 86 * a7 * a6 ^ 3 * a1 * b7
    + (5742089524897382400 : R) * h ^ 86 * a7 * a6 ^ 3 * a0 * b8
    + (4306567143673036800 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 ^ 2 * b4
    + (10766417859182592000 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a4 * b5
    + (12919701431019110400 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a3 * b6
    + (15072985002855628800 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a2 * b7
    + (17226268574692147200 : R) * h ^ 86 * a7 * a6 ^ 2 * a5 * a1 * b8
    + (6459850715509555200 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 ^ 2 * b6
    + (15072985002855628800 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a3 * b7
    + (17226268574692147200 : R) * h ^ 86 * a7 * a6 ^ 2 * a4 * a2 * b8
    + (8613134287346073600 : R) * h ^ 86 * a7 * a6 ^ 2 * a3 ^ 2 * b8
    + (3588805953060864000 : R) * h ^ 86 * a7 * a6 * a5 ^ 3 * b5
    + (12919701431019110400 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a4 * b6
    + (15072985002855628800 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a3 * b7
    + (17226268574692147200 : R) * h ^ 86 * a7 * a6 * a5 ^ 2 * a2 * b8
    + (15072985002855628800 : R) * h ^ 86 * a7 * a6 * a5 * a4 ^ 2 * b7
    + (34452537149384294400 : R) * h ^ 86 * a7 * a6 * a5 * a4 * a3 * b8
    + (5742089524897382400 : R) * h ^ 86 * a7 * a6 * a4 ^ 3 * b8
    + (1076641785918259200 : R) * h ^ 86 * a7 * a5 ^ 4 * b6
    + (5024328334285209600 : R) * h ^ 86 * a7 * a5 ^ 3 * a4 * b7
    + (5742089524897382400 : R) * h ^ 86 * a7 * a5 ^ 3 * a3 * b8
    + (8613134287346073600 : R) * h ^ 86 * a7 * a5 ^ 2 * a4 ^ 2 * b8
    + (107664178591825920 : R) * h ^ 86 * a6 ^ 5 * b3
    + (717761190612172800 : R) * h ^ 86 * a6 ^ 4 * a5 * b4
    + (897201488265216000 : R) * h ^ 86 * a6 ^ 4 * a4 * b5
    + (1076641785918259200 : R) * h ^ 86 * a6 ^ 4 * a3 * b6
    + (1256082083571302400 : R) * h ^ 86 * a6 ^ 4 * a2 * b7
    + (1435522381224345600 : R) * h ^ 86 * a6 ^ 4 * a1 * b8
    + (1794402976530432000 : R) * h ^ 86 * a6 ^ 3 * a5 ^ 2 * b5
    + (4306567143673036800 : R) * h ^ 86 * a6 ^ 3 * a5 * a4 * b6

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `11`. -/
def degreeZeroSourceJetHeadBlock11_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2512164167142604800 : R) * t0 ^ 2 * a4 ^ 3 * w1
    + (10766417859182592000 : R) * t0 * v1 ^ 2 * u1 * a4 * b5
    + (6459850715509555200 : R) * t0 * v1 ^ 2 * a4 ^ 2 * b62
    + (3588805953060864000 : R) * t0 * v1 * u1 ^ 3 * b5
    + (12919701431019110400 : R) * t0 * v1 * u1 ^ 2 * a4 * b62
    + (15072985002855628800 : R) * t0 * v1 * u1 * a4 ^ 2 * w1
    + (5742089524897382400 : R) * t0 * v1 * a4 ^ 3 * s1
    + (1076641785918259200 : R) * t0 * u1 ^ 4 * b62
    + (5024328334285209600 : R) * t0 * u1 ^ 3 * a4 * w1
    + (8613134287346073600 : R) * t0 * u1 ^ 2 * a4 ^ 2 * s1
    + (897201488265216000 : R) * v1 ^ 4 * a4 * b5
    + (1794402976530432000 : R) * v1 ^ 3 * u1 ^ 2 * b5
    + (4306567143673036800 : R) * v1 ^ 3 * u1 * a4 * b62

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `11`. -/
def degreeZeroSourceJetPlusBlock11_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (5742089524897382400 : R) * h ^ 7 * t0 * v1 ^ 3 * a0 * s1
    + (358880595306086400 : R) * h ^ 5 * t0 * v1 ^ 4 * b2
    + (5024328334285209600 : R) * h ^ 5 * t0 * v1 ^ 3 * a1 * w1
    + (17226268574692147200 : R) * h ^ 5 * t0 * v1 ^ 2 * u1 * a1 * s1
    + (1435522381224345600 : R) * h ^ 5 * v1 ^ 4 * a1 * s1
    + (17226268574692147200 : R) * h ^ 3 * t0 ^ 2 * u1 * a4 * a2 * s1
    + (8613134287346073600 : R) * h ^ 3 * t0 ^ 2 * u1 * a3 ^ 2 * s1
    + (2153283571836518400 : R) * h ^ 3 * t0 * v1 ^ 3 * u1 * b3
    + (4306567143673036800 : R) * h ^ 3 * t0 * v1 ^ 3 * a2 * b62
    + (15072985002855628800 : R) * h ^ 3 * t0 * v1 ^ 2 * u1 * a2 * w1
    + (17226268574692147200 : R) * h ^ 3 * t0 * v1 ^ 2 * a4 * a2 * s1
    + (8613134287346073600 : R) * h ^ 3 * t0 * v1 ^ 2 * a3 ^ 2 * s1
    + (17226268574692147200 : R) * h ^ 3 * t0 * v1 * u1 ^ 2 * a2 * s1
    + (107664178591825920 : R) * h ^ 3 * v1 ^ 5 * b3
    + (1256082083571302400 : R) * h ^ 3 * v1 ^ 4 * a2 * w1
    + (15072985002855628800 : R) * h * t0 ^ 2 * u1 * a4 * a3 * w1
    + (8613134287346073600 : R) * h * t0 ^ 2 * a4 ^ 2 * a3 * s1
    + (2871044762448691200 : R) * h * t0 * v1 ^ 3 * a4 * b4
    + (3588805953060864000 : R) * h * t0 * v1 ^ 3 * a3 * b5
    + (4306567143673036800 : R) * h * t0 * v1 ^ 2 * u1 ^ 2 * b4
    + (12919701431019110400 : R) * h * t0 * v1 ^ 2 * u1 * a3 * b62
    + (15072985002855628800 : R) * h * t0 * v1 ^ 2 * a4 * a3 * w1
    + (15072985002855628800 : R) * h * t0 * v1 * u1 ^ 2 * a3 * w1
    + (34452537149384294400 : R) * h * t0 * v1 * u1 * a4 * a3 * s1
    + (5742089524897382400 : R) * h * t0 * u1 ^ 3 * a3 * s1
    + (717761190612172800 : R) * h * v1 ^ 4 * u1 * b4
    + (1076641785918259200 : R) * h * v1 ^ 4 * a3 * b62

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock11_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock11_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock11_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock11_810,
    degreeZeroSourceJetHeadBlock11_810,
    degreeZeroSourceJetPlusBlock11_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `12` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock12_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (5024328334285209600 : R) * h ^ 86 * a6 ^ 3 * a5 * a3 * b7
    + (5742089524897382400 : R) * h ^ 86 * a6 ^ 3 * a5 * a2 * b8
    + (2512164167142604800 : R) * h ^ 86 * a6 ^ 3 * a4 ^ 2 * b7
    + (5742089524897382400 : R) * h ^ 86 * a6 ^ 3 * a4 * a3 * b8
    + (2153283571836518400 : R) * h ^ 86 * a6 ^ 2 * a5 ^ 3 * b6
    + (7536492501427814400 : R) * h ^ 86 * a6 ^ 2 * a5 ^ 2 * a4 * b7
    + (8613134287346073600 : R) * h ^ 86 * a6 ^ 2 * a5 ^ 2 * a3 * b8
    + (8613134287346073600 : R) * h ^ 86 * a6 ^ 2 * a5 * a4 ^ 2 * b8
    + (1256082083571302400 : R) * h ^ 86 * a6 * a5 ^ 4 * b7
    + (5742089524897382400 : R) * h ^ 86 * a6 * a5 ^ 3 * a4 * b8
    + (287104476244869120 : R) * h ^ 86 * a5 ^ 5 * b8
    - (740191227818803200 : R) * h ^ 80 * a7 ^ 5 * a4 * a0
    - (740191227818803200 : R) * h ^ 80 * a7 ^ 5 * a3 * a1
    - (370095613909401600 : R) * h ^ 80 * a7 ^ 5 * a2 ^ 2
    + (4626195173867520000 : R) * h ^ 80 * a7 ^ 4 * a6 * a5 * a0
    + (4626195173867520000 : R) * h ^ 80 * a7 ^ 4 * a6 * a4 * a1
    + (4626195173867520000 : R) * h ^ 80 * a7 ^ 4 * a6 * a3 * a2
    + (2313097586933760000 : R) * h ^ 80 * a7 ^ 4 * a5 ^ 2 * a1
    + (4626195173867520000 : R) * h ^ 80 * a7 ^ 4 * a5 * a4 * a2
    + (2313097586933760000 : R) * h ^ 80 * a7 ^ 4 * a5 * a3 ^ 2
    + (2313097586933760000 : R) * h ^ 80 * a7 ^ 4 * a4 ^ 2 * a3
    + (8635564324552704000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 3 * a0
    + (25906692973658112000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a5 * a1
    + (25906692973658112000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a4 * a2
    + (12953346486829056000 : R) * h ^ 80 * a7 ^ 3 * a6 ^ 2 * a3 ^ 2
    + (25906692973658112000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 ^ 2 * a2
    + (51813385947316224000 : R) * h ^ 80 * a7 ^ 3 * a6 * a5 * a4 * a3
    + (8635564324552704000 : R) * h ^ 80 * a7 ^ 3 * a6 * a4 ^ 3
    + (8635564324552704000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 3 * a3
    + (12953346486829056000 : R) * h ^ 80 * a7 ^ 3 * a5 ^ 2 * a4 ^ 2
    + (10640248899895296000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 4 * a1
    + (42560995599581184000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a5 * a2
    + (42560995599581184000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 3 * a4 * a3
    + (63841493399371776000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a3
    + (63841493399371776000 : R) * h ^ 80 * a7 ^ 2 * a6 ^ 2 * a5 * a4 ^ 2
    + (42560995599581184000 : R) * h ^ 80 * a7 ^ 2 * a6 * a5 ^ 3 * a4
    + (2128049779979059200 : R) * h ^ 80 * a7 ^ 2 * a5 ^ 5
    + (5921529822550425600 : R) * h ^ 80 * a7 * a6 ^ 5 * a2
    + (29607649112752128000 : R) * h ^ 80 * a7 * a6 ^ 4 * a5 * a3
    + (14803824556376064000 : R) * h ^ 80 * a7 * a6 ^ 4 * a4 ^ 2

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `12`. -/
def degreeZeroSourceJetHeadBlock12_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (8635564324552704000 : R) * t0 ^ 3 * v1 * a4 ^ 3
    + (12953346486829056000 : R) * t0 ^ 3 * u1 ^ 2 * a4 ^ 2
    + (63841493399371776000 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a4 ^ 2
    + (42560995599581184000 : R) * t0 ^ 2 * v1 * u1 ^ 3 * a4
    + (2128049779979059200 : R) * t0 ^ 2 * u1 ^ 5
    + (14803824556376064000 : R) * t0 * v1 ^ 4 * a4 ^ 2
    + (2512164167142604800 : R) * v1 ^ 3 * a4 ^ 2 * w1
    + (2153283571836518400 : R) * v1 ^ 2 * u1 ^ 3 * b62
    + (7536492501427814400 : R) * v1 ^ 2 * u1 ^ 2 * a4 * w1
    + (8613134287346073600 : R) * v1 ^ 2 * u1 * a4 ^ 2 * s1
    + (1256082083571302400 : R) * v1 * u1 ^ 4 * w1
    + (5742089524897382400 : R) * v1 * u1 ^ 3 * a4 * s1
    + (287104476244869120 : R) * u1 ^ 5 * s1

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `12`. -/
def degreeZeroSourceJetPlusBlock12_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (740191227818803200 : R) * h ^ 7 * t0 ^ 5 * a4 * a0
    - (740191227818803200 : R) * h ^ 7 * t0 ^ 5 * a3 * a1
    - (370095613909401600 : R) * h ^ 7 * t0 ^ 5 * a2 ^ 2
    + (4626195173867520000 : R) * h ^ 7 * t0 ^ 4 * v1 * u1 * a0
    + (8635564324552704000 : R) * h ^ 7 * t0 ^ 3 * v1 ^ 3 * a0
    + (4626195173867520000 : R) * h ^ 5 * t0 ^ 4 * v1 * a4 * a1
    + (4626195173867520000 : R) * h ^ 5 * t0 ^ 4 * v1 * a3 * a2
    + (2313097586933760000 : R) * h ^ 5 * t0 ^ 4 * u1 ^ 2 * a1
    + (25906692973658112000 : R) * h ^ 5 * t0 ^ 3 * v1 ^ 2 * u1 * a1
    + (10640248899895296000 : R) * h ^ 5 * t0 ^ 2 * v1 ^ 4 * a1
    + (4626195173867520000 : R) * h ^ 3 * t0 ^ 4 * u1 * a4 * a2
    + (2313097586933760000 : R) * h ^ 3 * t0 ^ 4 * u1 * a3 ^ 2
    + (25906692973658112000 : R) * h ^ 3 * t0 ^ 3 * v1 ^ 2 * a4 * a2
    + (12953346486829056000 : R) * h ^ 3 * t0 ^ 3 * v1 ^ 2 * a3 ^ 2
    + (25906692973658112000 : R) * h ^ 3 * t0 ^ 3 * v1 * u1 ^ 2 * a2
    + (42560995599581184000 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 3 * u1 * a2
    + (5921529822550425600 : R) * h ^ 3 * t0 * v1 ^ 5 * a2
    + (5742089524897382400 : R) * h ^ 3 * v1 ^ 3 * u1 * a2 * s1
    + (2313097586933760000 : R) * h * t0 ^ 4 * a4 ^ 2 * a3
    + (51813385947316224000 : R) * h * t0 ^ 3 * v1 * u1 * a4 * a3
    + (8635564324552704000 : R) * h * t0 ^ 3 * u1 ^ 3 * a3
    + (42560995599581184000 : R) * h * t0 ^ 2 * v1 ^ 3 * a4 * a3
    + (63841493399371776000 : R) * h * t0 ^ 2 * v1 ^ 2 * u1 ^ 2 * a3
    + (29607649112752128000 : R) * h * t0 * v1 ^ 4 * u1 * a3
    + (5024328334285209600 : R) * h * v1 ^ 3 * u1 * a3 * w1
    + (5742089524897382400 : R) * h * v1 ^ 3 * a4 * a3 * s1
    + (8613134287346073600 : R) * h * v1 ^ 2 * u1 ^ 2 * a3 * s1

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock12_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock12_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock12_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock12_810,
    degreeZeroSourceJetHeadBlock12_810,
    degreeZeroSourceJetPlusBlock12_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `13` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock13_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (59215298225504256000 : R) * h ^ 80 * a7 * a6 ^ 3 * a5 ^ 2 * a4
    + (14803824556376064000 : R) * h ^ 80 * a7 * a6 ^ 2 * a5 ^ 4
    + (1264493347523788800 : R) * h ^ 80 * a6 ^ 6 * a3
    + (7586960085142732800 : R) * h ^ 80 * a6 ^ 5 * a5 * a4
    + (6322466737618944000 : R) * h ^ 80 * a6 ^ 4 * a5 ^ 3
    - (1707066019157114880 : R) * h ^ 79 * a7 ^ 5 * a5 * a0 * lambda
    - (1707066019157114880 : R) * h ^ 79 * a7 ^ 5 * a4 * a1 * lambda
    - (1707066019157114880 : R) * h ^ 79 * a7 ^ 5 * a3 * a2 * lambda
    - (4267665047892787200 : R) * h ^ 79 * a7 ^ 4 * a6 ^ 2 * a0 * lambda
    - (8535330095785574400 : R) * h ^ 79 * a7 ^ 4 * a6 * a5 * a1 * lambda
    - (8535330095785574400 : R) * h ^ 79 * a7 ^ 4 * a6 * a4 * a2 * lambda
    - (4267665047892787200 : R) * h ^ 79 * a7 ^ 4 * a6 * a3 ^ 2 * lambda
    - (4267665047892787200 : R) * h ^ 79 * a7 ^ 4 * a5 ^ 2 * a2 * lambda
    - (8535330095785574400 : R) * h ^ 79 * a7 ^ 4 * a5 * a4 * a3 * lambda
    - (1422555015964262400 : R) * h ^ 79 * a7 ^ 4 * a4 ^ 3 * lambda
    - (5690220063857049600 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 3 * a1 * lambda
    - (17070660191571148800 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a5 * a2 * lambda
    - (17070660191571148800 : R) * h ^ 79 * a7 ^ 3 * a6 ^ 2 * a4 * a3 * lambda
    - (17070660191571148800 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 ^ 2 * a3 * lambda
    - (17070660191571148800 : R) * h ^ 79 * a7 ^ 3 * a6 * a5 * a4 ^ 2 * lambda
    - (5690220063857049600 : R) * h ^ 79 * a7 ^ 3 * a5 ^ 3 * a4 * lambda
    - (4267665047892787200 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 4 * a2 * lambda
    - (17070660191571148800 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a5 * a3 * lambda
    - (8535330095785574400 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 3 * a4 ^ 2 * lambda
    - (25605990287356723200 : R) * h ^ 79 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * a4 * lambda
    - (4267665047892787200 : R) * h ^ 79 * a7 ^ 2 * a6 * a5 ^ 4 * lambda
    - (1707066019157114880 : R) * h ^ 79 * a7 * a6 ^ 5 * a3 * lambda
    - (8535330095785574400 : R) * h ^ 79 * a7 * a6 ^ 4 * a5 * a4 * lambda
    - (5690220063857049600 : R) * h ^ 79 * a7 * a6 ^ 3 * a5 ^ 3 * lambda
    - (284511003192852480 : R) * h ^ 79 * a6 ^ 6 * a4 * lambda
    - (853533009578557440 : R) * h ^ 79 * a6 ^ 5 * a5 ^ 2 * lambda
    - (148038245563760640 : R) * h ^ 78 * a7 ^ 5 * a5 * b1
    - (296076491127521280 : R) * h ^ 78 * a7 ^ 5 * a4 * b2
    - (444114736691281920 : R) * h ^ 78 * a7 ^ 5 * a3 * b3
    - (592152982255042560 : R) * h ^ 78 * a7 ^ 5 * a2 * b4
    - (740191227818803200 : R) * h ^ 78 * a7 ^ 5 * a1 * b5
    - (888229473382563840 : R) * h ^ 78 * a7 ^ 5 * a0 * b6
    - (370095613909401600 : R) * h ^ 78 * a7 ^ 4 * a6 ^ 2 * b1
    - (1480382455637606400 : R) * h ^ 78 * a7 ^ 4 * a6 * a5 * b2
    - (2220573683456409600 : R) * h ^ 78 * a7 ^ 4 * a6 * a4 * b3

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `13`. -/
def degreeZeroSourceJetHeadBlock13_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (59215298225504256000 : R) * t0 * v1 ^ 3 * u1 ^ 2 * a4
    + (14803824556376064000 : R) * t0 * v1 ^ 2 * u1 ^ 4
    + (7586960085142732800 : R) * v1 ^ 5 * u1 * a4
    + (6322466737618944000 : R) * v1 ^ 4 * u1 ^ 3

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `13`. -/
def degreeZeroSourceJetPlusBlock13_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1707066019157114880 : R) * h ^ 8 * t0 ^ 5 * u1 * a0 * lambda
    - (4267665047892787200 : R) * h ^ 8 * t0 ^ 4 * v1 ^ 2 * a0 * lambda
    - (148038245563760640 : R) * h ^ 7 * t0 ^ 5 * u1 * b1
    - (888229473382563840 : R) * h ^ 7 * t0 ^ 5 * a0 * b62
    - (370095613909401600 : R) * h ^ 7 * t0 ^ 4 * v1 ^ 2 * b1
    - (1707066019157114880 : R) * h ^ 6 * t0 ^ 5 * a4 * a1 * lambda
    - (1707066019157114880 : R) * h ^ 6 * t0 ^ 5 * a3 * a2 * lambda
    - (8535330095785574400 : R) * h ^ 6 * t0 ^ 4 * v1 * u1 * a1 * lambda
    - (5690220063857049600 : R) * h ^ 6 * t0 ^ 3 * v1 ^ 3 * a1 * lambda
    - (296076491127521280 : R) * h ^ 5 * t0 ^ 5 * a4 * b2
    - (444114736691281920 : R) * h ^ 5 * t0 ^ 5 * a3 * b3
    - (592152982255042560 : R) * h ^ 5 * t0 ^ 5 * a2 * b4
    - (740191227818803200 : R) * h ^ 5 * t0 ^ 5 * a1 * b5
    - (1480382455637606400 : R) * h ^ 5 * t0 ^ 4 * v1 * u1 * b2
    - (8535330095785574400 : R) * h ^ 4 * t0 ^ 4 * v1 * a4 * a2 * lambda
    - (4267665047892787200 : R) * h ^ 4 * t0 ^ 4 * v1 * a3 ^ 2 * lambda
    - (4267665047892787200 : R) * h ^ 4 * t0 ^ 4 * u1 ^ 2 * a2 * lambda
    - (17070660191571148800 : R) * h ^ 4 * t0 ^ 3 * v1 ^ 2 * u1 * a2 * lambda
    - (4267665047892787200 : R) * h ^ 4 * t0 ^ 2 * v1 ^ 4 * a2 * lambda
    - (2220573683456409600 : R) * h ^ 3 * t0 ^ 4 * v1 * a4 * b3
    - (8535330095785574400 : R) * h ^ 2 * t0 ^ 4 * u1 * a4 * a3 * lambda
    - (17070660191571148800 : R) * h ^ 2 * t0 ^ 3 * v1 ^ 2 * a4 * a3 * lambda
    - (17070660191571148800 : R) * h ^ 2 * t0 ^ 3 * v1 * u1 ^ 2 * a3 * lambda
    - (17070660191571148800 : R) * h ^ 2 * t0 ^ 2 * v1 ^ 3 * u1 * a3 * lambda
    - (1707066019157114880 : R) * h ^ 2 * t0 * v1 ^ 5 * a3 * lambda
    + (1264493347523788800 : R) * h * v1 ^ 6 * a3
    - (1422555015964262400 : R) * t0 ^ 4 * a4 ^ 3 * lambda
    - (17070660191571148800 : R) * t0 ^ 3 * v1 * u1 * a4 ^ 2 * lambda
    - (5690220063857049600 : R) * t0 ^ 3 * u1 ^ 3 * a4 * lambda
    - (8535330095785574400 : R) * t0 ^ 2 * v1 ^ 3 * a4 ^ 2 * lambda
    - (25605990287356723200 : R) * t0 ^ 2 * v1 ^ 2 * u1 ^ 2 * a4 * lambda
    - (4267665047892787200 : R) * t0 ^ 2 * v1 * u1 ^ 4 * lambda
    - (8535330095785574400 : R) * t0 * v1 ^ 4 * u1 * a4 * lambda
    - (5690220063857049600 : R) * t0 * v1 ^ 3 * u1 ^ 3 * lambda
    - (284511003192852480 : R) * v1 ^ 6 * a4 * lambda
    - (853533009578557440 : R) * v1 ^ 5 * u1 ^ 2 * lambda

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock13_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock13_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock13_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock13_810,
    degreeZeroSourceJetHeadBlock13_810,
    degreeZeroSourceJetPlusBlock13_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `14` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock14_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2960764911275212800 : R) * h ^ 78 * a7 ^ 4 * a6 * a3 * b4
    - (3700956139094016000 : R) * h ^ 78 * a7 ^ 4 * a6 * a2 * b5
    - (4441147366912819200 : R) * h ^ 78 * a7 ^ 4 * a6 * a1 * b6
    - (5181338594731622400 : R) * h ^ 78 * a7 ^ 4 * a6 * a0 * b7
    - (1110286841728204800 : R) * h ^ 78 * a7 ^ 4 * a5 ^ 2 * b3
    - (2960764911275212800 : R) * h ^ 78 * a7 ^ 4 * a5 * a4 * b4
    - (3700956139094016000 : R) * h ^ 78 * a7 ^ 4 * a5 * a3 * b5
    - (4441147366912819200 : R) * h ^ 78 * a7 ^ 4 * a5 * a2 * b6
    - (5181338594731622400 : R) * h ^ 78 * a7 ^ 4 * a5 * a1 * b7
    - (5921529822550425600 : R) * h ^ 78 * a7 ^ 4 * a5 * a0 * b8
    - (1850478069547008000 : R) * h ^ 78 * a7 ^ 4 * a4 ^ 2 * b5
    - (4441147366912819200 : R) * h ^ 78 * a7 ^ 4 * a4 * a3 * b6
    - (5181338594731622400 : R) * h ^ 78 * a7 ^ 4 * a4 * a2 * b7
    - (5921529822550425600 : R) * h ^ 78 * a7 ^ 4 * a4 * a1 * b8
    - (2590669297365811200 : R) * h ^ 78 * a7 ^ 4 * a3 ^ 2 * b7
    - (5921529822550425600 : R) * h ^ 78 * a7 ^ 4 * a3 * a2 * b8
    - (986921637091737600 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 3 * b2
    - (4441147366912819200 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a5 * b3
    - (5921529822550425600 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a4 * b4
    - (7401912278188032000 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a3 * b5
    - (8882294733825638400 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a2 * b6
    - (10362677189463244800 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a1 * b7
    - (11843059645100851200 : R) * h ^ 78 * a7 ^ 3 * a6 ^ 2 * a0 * b8
    - (5921529822550425600 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 ^ 2 * b4
    - (14803824556376064000 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a4 * b5
    - (17764589467651276800 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a3 * b6
    - (20725354378926489600 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a2 * b7
    - (23686119290201702400 : R) * h ^ 78 * a7 ^ 3 * a6 * a5 * a1 * b8
    - (8882294733825638400 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 ^ 2 * b6
    - (20725354378926489600 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a3 * b7
    - (23686119290201702400 : R) * h ^ 78 * a7 ^ 3 * a6 * a4 * a2 * b8
    - (11843059645100851200 : R) * h ^ 78 * a7 ^ 3 * a6 * a3 ^ 2 * b8
    - (2467304092729344000 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 3 * b5
    - (8882294733825638400 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a4 * b6
    - (10362677189463244800 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a3 * b7
    - (11843059645100851200 : R) * h ^ 78 * a7 ^ 3 * a5 ^ 2 * a2 * b8
    - (10362677189463244800 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 ^ 2 * b7
    - (23686119290201702400 : R) * h ^ 78 * a7 ^ 3 * a5 * a4 * a3 * b8
    - (3947686548366950400 : R) * h ^ 78 * a7 ^ 3 * a4 ^ 3 * b8
    - (1110286841728204800 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 4 * b3

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `14`. -/
def degreeZeroSourceJetHeadBlock14_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1850478069547008000 : R) * t0 ^ 4 * a4 ^ 2 * b5
    - (14803824556376064000 : R) * t0 ^ 3 * v1 * u1 * a4 * b5
    - (8882294733825638400 : R) * t0 ^ 3 * v1 * a4 ^ 2 * b62
    - (2467304092729344000 : R) * t0 ^ 3 * u1 ^ 3 * b5
    - (8882294733825638400 : R) * t0 ^ 3 * u1 ^ 2 * a4 * b62
    - (10362677189463244800 : R) * t0 ^ 3 * u1 * a4 ^ 2 * w1
    - (3947686548366950400 : R) * t0 ^ 3 * a4 ^ 3 * s1

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `14`. -/
def degreeZeroSourceJetPlusBlock14_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5181338594731622400 : R) * h ^ 7 * t0 ^ 4 * v1 * a0 * w1
    - (5921529822550425600 : R) * h ^ 7 * t0 ^ 4 * u1 * a0 * s1
    - (11843059645100851200 : R) * h ^ 7 * t0 ^ 3 * v1 ^ 2 * a0 * s1
    - (4441147366912819200 : R) * h ^ 5 * t0 ^ 4 * v1 * a1 * b62
    - (5181338594731622400 : R) * h ^ 5 * t0 ^ 4 * u1 * a1 * w1
    - (5921529822550425600 : R) * h ^ 5 * t0 ^ 4 * a4 * a1 * s1
    - (5921529822550425600 : R) * h ^ 5 * t0 ^ 4 * a3 * a2 * s1
    - (986921637091737600 : R) * h ^ 5 * t0 ^ 3 * v1 ^ 3 * b2
    - (10362677189463244800 : R) * h ^ 5 * t0 ^ 3 * v1 ^ 2 * a1 * w1
    - (23686119290201702400 : R) * h ^ 5 * t0 ^ 3 * v1 * u1 * a1 * s1
    - (2960764911275212800 : R) * h ^ 3 * t0 ^ 4 * v1 * a3 * b4
    - (3700956139094016000 : R) * h ^ 3 * t0 ^ 4 * v1 * a2 * b5
    - (1110286841728204800 : R) * h ^ 3 * t0 ^ 4 * u1 ^ 2 * b3
    - (4441147366912819200 : R) * h ^ 3 * t0 ^ 4 * u1 * a2 * b62
    - (5181338594731622400 : R) * h ^ 3 * t0 ^ 4 * a4 * a2 * w1
    - (2590669297365811200 : R) * h ^ 3 * t0 ^ 4 * a3 ^ 2 * w1
    - (4441147366912819200 : R) * h ^ 3 * t0 ^ 3 * v1 ^ 2 * u1 * b3
    - (8882294733825638400 : R) * h ^ 3 * t0 ^ 3 * v1 ^ 2 * a2 * b62
    - (20725354378926489600 : R) * h ^ 3 * t0 ^ 3 * v1 * u1 * a2 * w1
    - (23686119290201702400 : R) * h ^ 3 * t0 ^ 3 * v1 * a4 * a2 * s1
    - (11843059645100851200 : R) * h ^ 3 * t0 ^ 3 * v1 * a3 ^ 2 * s1
    - (11843059645100851200 : R) * h ^ 3 * t0 ^ 3 * u1 ^ 2 * a2 * s1
    - (1110286841728204800 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 4 * b3
    - (2960764911275212800 : R) * h * t0 ^ 4 * u1 * a4 * b4
    - (3700956139094016000 : R) * h * t0 ^ 4 * u1 * a3 * b5
    - (4441147366912819200 : R) * h * t0 ^ 4 * a4 * a3 * b62
    - (5921529822550425600 : R) * h * t0 ^ 3 * v1 ^ 2 * a4 * b4
    - (7401912278188032000 : R) * h * t0 ^ 3 * v1 ^ 2 * a3 * b5
    - (5921529822550425600 : R) * h * t0 ^ 3 * v1 * u1 ^ 2 * b4
    - (17764589467651276800 : R) * h * t0 ^ 3 * v1 * u1 * a3 * b62
    - (20725354378926489600 : R) * h * t0 ^ 3 * v1 * a4 * a3 * w1
    - (10362677189463244800 : R) * h * t0 ^ 3 * u1 ^ 2 * a3 * w1
    - (23686119290201702400 : R) * h * t0 ^ 3 * u1 * a4 * a3 * s1

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock14_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock14_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock14_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock14_810,
    degreeZeroSourceJetHeadBlock14_810,
    degreeZeroSourceJetPlusBlock14_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `15` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock15_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5921529822550425600 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a5 * b4
    - (7401912278188032000 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a4 * b5
    - (8882294733825638400 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a3 * b6
    - (10362677189463244800 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a2 * b7
    - (11843059645100851200 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 3 * a1 * b8
    - (11102868417282048000 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 ^ 2 * b5
    - (26646884201476915200 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a4 * b6
    - (31088031568389734400 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a3 * b7
    - (35529178935302553600 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a5 * a2 * b8
    - (15544015784194867200 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 ^ 2 * b7
    - (35529178935302553600 : R) * h ^ 78 * a7 ^ 2 * a6 ^ 2 * a4 * a3 * b8
    - (8882294733825638400 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 3 * b6
    - (31088031568389734400 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a4 * b7
    - (35529178935302553600 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 ^ 2 * a3 * b8
    - (35529178935302553600 : R) * h ^ 78 * a7 ^ 2 * a6 * a5 * a4 ^ 2 * b8
    - (2590669297365811200 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 4 * b7
    - (11843059645100851200 : R) * h ^ 78 * a7 ^ 2 * a5 ^ 3 * a4 * b8
    - (592152982255042560 : R) * h ^ 78 * a7 * a6 ^ 5 * b4
    - (3700956139094016000 : R) * h ^ 78 * a7 * a6 ^ 4 * a5 * b5
    - (4441147366912819200 : R) * h ^ 78 * a7 * a6 ^ 4 * a4 * b6
    - (5181338594731622400 : R) * h ^ 78 * a7 * a6 ^ 4 * a3 * b7
    - (5921529822550425600 : R) * h ^ 78 * a7 * a6 ^ 4 * a2 * b8
    - (8882294733825638400 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 ^ 2 * b6
    - (20725354378926489600 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 * a4 * b7
    - (23686119290201702400 : R) * h ^ 78 * a7 * a6 ^ 3 * a5 * a3 * b8
    - (11843059645100851200 : R) * h ^ 78 * a7 * a6 ^ 3 * a4 ^ 2 * b8
    - (10362677189463244800 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 ^ 3 * b7
    - (35529178935302553600 : R) * h ^ 78 * a7 * a6 ^ 2 * a5 ^ 2 * a4 * b8
    - (5921529822550425600 : R) * h ^ 78 * a7 * a6 * a5 ^ 4 * b8
    - (123365204636467200 : R) * h ^ 78 * a6 ^ 6 * b5
    - (888229473382563840 : R) * h ^ 78 * a6 ^ 5 * a5 * b6
    - (1036267718946324480 : R) * h ^ 78 * a6 ^ 5 * a4 * b7
    - (1184305964510085120 : R) * h ^ 78 * a6 ^ 5 * a3 * b8
    - (2590669297365811200 : R) * h ^ 78 * a6 ^ 4 * a5 ^ 2 * b7
    - (5921529822550425600 : R) * h ^ 78 * a6 ^ 4 * a5 * a4 * b8
    - (3947686548366950400 : R) * h ^ 78 * a6 ^ 3 * a5 ^ 3 * b8
    + (790308342202368000 : R) * h ^ 72 * a7 ^ 6 * a5 * a0
    + (790308342202368000 : R) * h ^ 72 * a7 ^ 6 * a4 * a1
    + (790308342202368000 : R) * h ^ 72 * a7 ^ 6 * a3 * a2
    - (1896740021285683200 : R) * h ^ 72 * a7 ^ 5 * a6 ^ 2 * a0

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `15`. -/
def degreeZeroSourceJetHeadBlock15_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (7401912278188032000 : R) * t0 ^ 2 * v1 ^ 3 * a4 * b5
    - (11102868417282048000 : R) * t0 ^ 2 * v1 ^ 2 * u1 ^ 2 * b5
    - (26646884201476915200 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a4 * b62
    - (15544015784194867200 : R) * t0 ^ 2 * v1 ^ 2 * a4 ^ 2 * w1
    - (8882294733825638400 : R) * t0 ^ 2 * v1 * u1 ^ 3 * b62
    - (31088031568389734400 : R) * t0 ^ 2 * v1 * u1 ^ 2 * a4 * w1
    - (35529178935302553600 : R) * t0 ^ 2 * v1 * u1 * a4 ^ 2 * s1
    - (2590669297365811200 : R) * t0 ^ 2 * u1 ^ 4 * w1
    - (11843059645100851200 : R) * t0 ^ 2 * u1 ^ 3 * a4 * s1
    - (3700956139094016000 : R) * t0 * v1 ^ 4 * u1 * b5
    - (4441147366912819200 : R) * t0 * v1 ^ 4 * a4 * b62
    - (8882294733825638400 : R) * t0 * v1 ^ 3 * u1 ^ 2 * b62
    - (20725354378926489600 : R) * t0 * v1 ^ 3 * u1 * a4 * w1
    - (11843059645100851200 : R) * t0 * v1 ^ 3 * a4 ^ 2 * s1
    - (10362677189463244800 : R) * t0 * v1 ^ 2 * u1 ^ 3 * w1
    - (35529178935302553600 : R) * t0 * v1 ^ 2 * u1 ^ 2 * a4 * s1
    - (5921529822550425600 : R) * t0 * v1 * u1 ^ 4 * s1
    - (123365204636467200 : R) * v1 ^ 6 * b5
    - (888229473382563840 : R) * v1 ^ 5 * u1 * b62
    - (1036267718946324480 : R) * v1 ^ 5 * a4 * w1
    - (2590669297365811200 : R) * v1 ^ 4 * u1 ^ 2 * w1
    - (5921529822550425600 : R) * v1 ^ 4 * u1 * a4 * s1
    - (3947686548366950400 : R) * v1 ^ 3 * u1 ^ 3 * s1

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `15`. -/
def degreeZeroSourceJetPlusBlock15_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (790308342202368000 : R) * h ^ 7 * t0 ^ 6 * u1 * a0
    - (1896740021285683200 : R) * h ^ 7 * t0 ^ 5 * v1 ^ 2 * a0
    + (790308342202368000 : R) * h ^ 5 * t0 ^ 6 * a4 * a1
    + (790308342202368000 : R) * h ^ 5 * t0 ^ 6 * a3 * a2
    - (11843059645100851200 : R) * h ^ 5 * t0 ^ 2 * v1 ^ 3 * a1 * s1
    - (10362677189463244800 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 3 * a2 * w1
    - (35529178935302553600 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 2 * u1 * a2 * s1
    - (5921529822550425600 : R) * h ^ 3 * t0 * v1 ^ 4 * a2 * s1
    - (5921529822550425600 : R) * h * t0 ^ 2 * v1 ^ 3 * u1 * b4
    - (8882294733825638400 : R) * h * t0 ^ 2 * v1 ^ 3 * a3 * b62
    - (31088031568389734400 : R) * h * t0 ^ 2 * v1 ^ 2 * u1 * a3 * w1
    - (35529178935302553600 : R) * h * t0 ^ 2 * v1 ^ 2 * a4 * a3 * s1
    - (35529178935302553600 : R) * h * t0 ^ 2 * v1 * u1 ^ 2 * a3 * s1
    - (592152982255042560 : R) * h * t0 * v1 ^ 5 * b4
    - (5181338594731622400 : R) * h * t0 * v1 ^ 4 * a3 * w1
    - (23686119290201702400 : R) * h * t0 * v1 ^ 3 * u1 * a3 * s1
    - (1184305964510085120 : R) * h * v1 ^ 5 * a3 * s1

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock15_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock15_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock15_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock15_810,
    degreeZeroSourceJetHeadBlock15_810,
    degreeZeroSourceJetPlusBlock15_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `16` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock16_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (3793480042571366400 : R) * h ^ 72 * a7 ^ 5 * a6 * a5 * a1
    - (3793480042571366400 : R) * h ^ 72 * a7 ^ 5 * a6 * a4 * a2
    - (1896740021285683200 : R) * h ^ 72 * a7 ^ 5 * a6 * a3 ^ 2
    - (1896740021285683200 : R) * h ^ 72 * a7 ^ 5 * a5 ^ 2 * a2
    - (3793480042571366400 : R) * h ^ 72 * a7 ^ 5 * a5 * a4 * a3
    - (632246673761894400 : R) * h ^ 72 * a7 ^ 5 * a4 ^ 3
    - (10274008448630784000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 3 * a1
    - (30822025345892352000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a5 * a2
    - (30822025345892352000 : R) * h ^ 72 * a7 ^ 4 * a6 ^ 2 * a4 * a3
    - (30822025345892352000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 ^ 2 * a3
    - (30822025345892352000 : R) * h ^ 72 * a7 ^ 4 * a6 * a5 * a4 ^ 2
    - (10274008448630784000 : R) * h ^ 72 * a7 ^ 4 * a5 ^ 3 * a4
    - (17386783528452096000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 4 * a2
    - (69547134113808384000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a5 * a3
    - (34773567056904192000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 3 * a4 ^ 2
    - (104320701170712576000 : R) * h ^ 72 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * a4
    - (17386783528452096000 : R) * h ^ 72 * a7 ^ 3 * a6 * a5 ^ 4
    - (14699735164964044800 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 5 * a3
    - (73498675824820224000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 4 * a5 * a4
    - (48999117216546816000 : R) * h ^ 72 * a7 ^ 2 * a6 ^ 3 * a5 ^ 3
    - (6322466737618944000 : R) * h ^ 72 * a7 * a6 ^ 6 * a4
    - (18967400212856832000 : R) * h ^ 72 * a7 * a6 ^ 5 * a5 ^ 2
    - (1106431679083315200 : R) * h ^ 72 * a6 ^ 7 * a5
    + (1742629894556221440 : R) * h ^ 71 * a7 ^ 6 * a6 * a0 * lambda
    + (1742629894556221440 : R) * h ^ 71 * a7 ^ 6 * a5 * a1 * lambda
    + (1742629894556221440 : R) * h ^ 71 * a7 ^ 6 * a4 * a2 * lambda
    + (871314947278110720 : R) * h ^ 71 * a7 ^ 6 * a3 ^ 2 * lambda
    + (5227889683668664320 : R) * h ^ 71 * a7 ^ 5 * a6 ^ 2 * a1 * lambda
    + (10455779367337328640 : R) * h ^ 71 * a7 ^ 5 * a6 * a5 * a2 * lambda
    + (10455779367337328640 : R) * h ^ 71 * a7 ^ 5 * a6 * a4 * a3 * lambda
    + (5227889683668664320 : R) * h ^ 71 * a7 ^ 5 * a5 ^ 2 * a3 * lambda
    + (5227889683668664320 : R) * h ^ 71 * a7 ^ 5 * a5 * a4 ^ 2 * lambda
    + (8713149472781107200 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 3 * a2 * lambda
    + (26139448418343321600 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a5 * a3 * lambda
    + (13069724209171660800 : R) * h ^ 71 * a7 ^ 4 * a6 ^ 2 * a4 ^ 2 * lambda
    + (26139448418343321600 : R) * h ^ 71 * a7 ^ 4 * a6 * a5 ^ 2 * a4 * lambda
    + (2178287368195276800 : R) * h ^ 71 * a7 ^ 4 * a5 ^ 4 * lambda
    + (8713149472781107200 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 4 * a3 * lambda
    + (34852597891124428800 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 3 * a5 * a4 * lambda
    + (17426298945562214400 : R) * h ^ 71 * a7 ^ 3 * a6 ^ 2 * a5 ^ 3 * lambda

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `16`. -/
def degreeZeroSourceJetHeadBlock16_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (632246673761894400 : R) * t0 ^ 5 * a4 ^ 3
    - (30822025345892352000 : R) * t0 ^ 4 * v1 * u1 * a4 ^ 2
    - (10274008448630784000 : R) * t0 ^ 4 * u1 ^ 3 * a4
    - (34773567056904192000 : R) * t0 ^ 3 * v1 ^ 3 * a4 ^ 2
    - (104320701170712576000 : R) * t0 ^ 3 * v1 ^ 2 * u1 ^ 2 * a4
    - (17386783528452096000 : R) * t0 ^ 3 * v1 * u1 ^ 4
    - (73498675824820224000 : R) * t0 ^ 2 * v1 ^ 4 * u1 * a4
    - (48999117216546816000 : R) * t0 ^ 2 * v1 ^ 3 * u1 ^ 3
    - (6322466737618944000 : R) * t0 * v1 ^ 6 * a4
    - (18967400212856832000 : R) * t0 * v1 ^ 5 * u1 ^ 2
    - (1106431679083315200 : R) * v1 ^ 7 * u1

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `16`. -/
def degreeZeroSourceJetPlusBlock16_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1742629894556221440 : R) * h ^ 8 * t0 ^ 6 * v1 * a0 * lambda
    + (1742629894556221440 : R) * h ^ 6 * t0 ^ 6 * u1 * a1 * lambda
    + (5227889683668664320 : R) * h ^ 6 * t0 ^ 5 * v1 ^ 2 * a1 * lambda
    - (3793480042571366400 : R) * h ^ 5 * t0 ^ 5 * v1 * u1 * a1
    - (10274008448630784000 : R) * h ^ 5 * t0 ^ 4 * v1 ^ 3 * a1
    + (1742629894556221440 : R) * h ^ 4 * t0 ^ 6 * a4 * a2 * lambda
    + (871314947278110720 : R) * h ^ 4 * t0 ^ 6 * a3 ^ 2 * lambda
    + (10455779367337328640 : R) * h ^ 4 * t0 ^ 5 * v1 * u1 * a2 * lambda
    + (8713149472781107200 : R) * h ^ 4 * t0 ^ 4 * v1 ^ 3 * a2 * lambda
    - (3793480042571366400 : R) * h ^ 3 * t0 ^ 5 * v1 * a4 * a2
    - (1896740021285683200 : R) * h ^ 3 * t0 ^ 5 * v1 * a3 ^ 2
    - (1896740021285683200 : R) * h ^ 3 * t0 ^ 5 * u1 ^ 2 * a2
    - (30822025345892352000 : R) * h ^ 3 * t0 ^ 4 * v1 ^ 2 * u1 * a2
    - (17386783528452096000 : R) * h ^ 3 * t0 ^ 3 * v1 ^ 4 * a2
    + (10455779367337328640 : R) * h ^ 2 * t0 ^ 5 * v1 * a4 * a3 * lambda
    + (5227889683668664320 : R) * h ^ 2 * t0 ^ 5 * u1 ^ 2 * a3 * lambda
    + (26139448418343321600 : R) * h ^ 2 * t0 ^ 4 * v1 ^ 2 * u1 * a3 * lambda
    + (8713149472781107200 : R) * h ^ 2 * t0 ^ 3 * v1 ^ 4 * a3 * lambda
    - (3793480042571366400 : R) * h * t0 ^ 5 * u1 * a4 * a3
    - (30822025345892352000 : R) * h * t0 ^ 4 * v1 ^ 2 * a4 * a3
    - (30822025345892352000 : R) * h * t0 ^ 4 * v1 * u1 ^ 2 * a3
    - (69547134113808384000 : R) * h * t0 ^ 3 * v1 ^ 3 * u1 * a3
    - (14699735164964044800 : R) * h * t0 ^ 2 * v1 ^ 5 * a3
    + (5227889683668664320 : R) * t0 ^ 5 * u1 * a4 ^ 2 * lambda
    + (13069724209171660800 : R) * t0 ^ 4 * v1 ^ 2 * a4 ^ 2 * lambda
    + (26139448418343321600 : R) * t0 ^ 4 * v1 * u1 ^ 2 * a4 * lambda
    + (2178287368195276800 : R) * t0 ^ 4 * u1 ^ 4 * lambda
    + (34852597891124428800 : R) * t0 ^ 3 * v1 ^ 3 * u1 * a4 * lambda
    + (17426298945562214400 : R) * t0 ^ 3 * v1 ^ 2 * u1 ^ 3 * lambda

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock16_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock16_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock16_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock16_810,
    degreeZeroSourceJetHeadBlock16_810,
    degreeZeroSourceJetPlusBlock16_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `17` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock17_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (5227889683668664320 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 5 * a4 * lambda
    + (13069724209171660800 : R) * h ^ 71 * a7 ^ 2 * a6 ^ 4 * a5 ^ 2 * lambda
    + (1742629894556221440 : R) * h ^ 71 * a7 * a6 ^ 6 * a5 * lambda
    + (31118390974218240 : R) * h ^ 71 * a6 ^ 8 * lambda
    + (126449334752378880 : R) * h ^ 70 * a7 ^ 6 * a6 * b1
    + (252898669504757760 : R) * h ^ 70 * a7 ^ 6 * a5 * b2
    + (379348004257136640 : R) * h ^ 70 * a7 ^ 6 * a4 * b3
    + (505797339009515520 : R) * h ^ 70 * a7 ^ 6 * a3 * b4
    + (632246673761894400 : R) * h ^ 70 * a7 ^ 6 * a2 * b5
    + (758696008514273280 : R) * h ^ 70 * a7 ^ 6 * a1 * b6
    + (885145343266652160 : R) * h ^ 70 * a7 ^ 6 * a0 * b7
    + (758696008514273280 : R) * h ^ 70 * a7 ^ 5 * a6 ^ 2 * b2
    + (2276088025542819840 : R) * h ^ 70 * a7 ^ 5 * a6 * a5 * b3
    + (3034784034057093120 : R) * h ^ 70 * a7 ^ 5 * a6 * a4 * b4
    + (3793480042571366400 : R) * h ^ 70 * a7 ^ 5 * a6 * a3 * b5
    + (4552176051085639680 : R) * h ^ 70 * a7 ^ 5 * a6 * a2 * b6
    + (5310872059599912960 : R) * h ^ 70 * a7 ^ 5 * a6 * a1 * b7
    + (6069568068114186240 : R) * h ^ 70 * a7 ^ 5 * a6 * a0 * b8
    + (1517392017028546560 : R) * h ^ 70 * a7 ^ 5 * a5 ^ 2 * b4
    + (3793480042571366400 : R) * h ^ 70 * a7 ^ 5 * a5 * a4 * b5
    + (4552176051085639680 : R) * h ^ 70 * a7 ^ 5 * a5 * a3 * b6
    + (5310872059599912960 : R) * h ^ 70 * a7 ^ 5 * a5 * a2 * b7
    + (6069568068114186240 : R) * h ^ 70 * a7 ^ 5 * a5 * a1 * b8
    + (2276088025542819840 : R) * h ^ 70 * a7 ^ 5 * a4 ^ 2 * b6
    + (5310872059599912960 : R) * h ^ 70 * a7 ^ 5 * a4 * a3 * b7
    + (6069568068114186240 : R) * h ^ 70 * a7 ^ 5 * a4 * a2 * b8
    + (3034784034057093120 : R) * h ^ 70 * a7 ^ 5 * a3 ^ 2 * b8
    + (1896740021285683200 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 3 * b3
    + (7586960085142732800 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a5 * b4
    + (9483700106428416000 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a4 * b5
    + (11380440127714099200 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a3 * b6
    + (13277180148999782400 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a2 * b7
    + (15173920170285465600 : R) * h ^ 70 * a7 ^ 4 * a6 ^ 2 * a1 * b8
    + (9483700106428416000 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 ^ 2 * b5
    + (22760880255428198400 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a4 * b6
    + (26554360297999564800 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a3 * b7
    + (30347840340570931200 : R) * h ^ 70 * a7 ^ 4 * a6 * a5 * a2 * b8
    + (13277180148999782400 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 ^ 2 * b7
    + (30347840340570931200 : R) * h ^ 70 * a7 ^ 4 * a6 * a4 * a3 * b8
    + (3793480042571366400 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 3 * b6

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `17`. -/
def degreeZeroSourceJetHeadBlock17_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (3793480042571366400 : R) * t0 ^ 5 * u1 * a4 * b5
    + (2276088025542819840 : R) * t0 ^ 5 * a4 ^ 2 * b62
    + (9483700106428416000 : R) * t0 ^ 4 * v1 ^ 2 * a4 * b5
    + (9483700106428416000 : R) * t0 ^ 4 * v1 * u1 ^ 2 * b5
    + (22760880255428198400 : R) * t0 ^ 4 * v1 * u1 * a4 * b62
    + (13277180148999782400 : R) * t0 ^ 4 * v1 * a4 ^ 2 * w1
    + (3793480042571366400 : R) * t0 ^ 4 * u1 ^ 3 * b62

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `17`. -/
def degreeZeroSourceJetPlusBlock17_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (126449334752378880 : R) * h ^ 7 * t0 ^ 6 * v1 * b1
    + (885145343266652160 : R) * h ^ 7 * t0 ^ 6 * a0 * w1
    + (6069568068114186240 : R) * h ^ 7 * t0 ^ 5 * v1 * a0 * s1
    + (252898669504757760 : R) * h ^ 5 * t0 ^ 6 * u1 * b2
    + (758696008514273280 : R) * h ^ 5 * t0 ^ 6 * a1 * b62
    + (758696008514273280 : R) * h ^ 5 * t0 ^ 5 * v1 ^ 2 * b2
    + (5310872059599912960 : R) * h ^ 5 * t0 ^ 5 * v1 * a1 * w1
    + (6069568068114186240 : R) * h ^ 5 * t0 ^ 5 * u1 * a1 * s1
    + (15173920170285465600 : R) * h ^ 5 * t0 ^ 4 * v1 ^ 2 * a1 * s1
    + (379348004257136640 : R) * h ^ 3 * t0 ^ 6 * a4 * b3
    + (505797339009515520 : R) * h ^ 3 * t0 ^ 6 * a3 * b4
    + (632246673761894400 : R) * h ^ 3 * t0 ^ 6 * a2 * b5
    + (2276088025542819840 : R) * h ^ 3 * t0 ^ 5 * v1 * u1 * b3
    + (4552176051085639680 : R) * h ^ 3 * t0 ^ 5 * v1 * a2 * b62
    + (5310872059599912960 : R) * h ^ 3 * t0 ^ 5 * u1 * a2 * w1
    + (6069568068114186240 : R) * h ^ 3 * t0 ^ 5 * a4 * a2 * s1
    + (3034784034057093120 : R) * h ^ 3 * t0 ^ 5 * a3 ^ 2 * s1
    + (1896740021285683200 : R) * h ^ 3 * t0 ^ 4 * v1 ^ 3 * b3
    + (13277180148999782400 : R) * h ^ 3 * t0 ^ 4 * v1 ^ 2 * a2 * w1
    + (30347840340570931200 : R) * h ^ 3 * t0 ^ 4 * v1 * u1 * a2 * s1
    + (3034784034057093120 : R) * h * t0 ^ 5 * v1 * a4 * b4
    + (3793480042571366400 : R) * h * t0 ^ 5 * v1 * a3 * b5
    + (1517392017028546560 : R) * h * t0 ^ 5 * u1 ^ 2 * b4
    + (4552176051085639680 : R) * h * t0 ^ 5 * u1 * a3 * b62
    + (5310872059599912960 : R) * h * t0 ^ 5 * a4 * a3 * w1
    + (7586960085142732800 : R) * h * t0 ^ 4 * v1 ^ 2 * u1 * b4
    + (11380440127714099200 : R) * h * t0 ^ 4 * v1 ^ 2 * a3 * b62
    + (26554360297999564800 : R) * h * t0 ^ 4 * v1 * u1 * a3 * w1
    + (30347840340570931200 : R) * h * t0 ^ 4 * v1 * a4 * a3 * s1
    + (5227889683668664320 : R) * t0 ^ 2 * v1 ^ 5 * a4 * lambda
    + (13069724209171660800 : R) * t0 ^ 2 * v1 ^ 4 * u1 ^ 2 * lambda
    + (1742629894556221440 : R) * t0 * v1 ^ 6 * u1 * lambda
    + (31118390974218240 : R) * v1 ^ 8 * lambda

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock17_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock17_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock17_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock17_810,
    degreeZeroSourceJetHeadBlock17_810,
    degreeZeroSourceJetPlusBlock17_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `18` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock18_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (13277180148999782400 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a4 * b7
    + (15173920170285465600 : R) * h ^ 70 * a7 ^ 4 * a5 ^ 2 * a3 * b8
    + (15173920170285465600 : R) * h ^ 70 * a7 ^ 4 * a5 * a4 ^ 2 * b8
    + (2528986695047577600 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 4 * b4
    + (12644933475237888000 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a5 * b5
    + (15173920170285465600 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a4 * b6
    + (17702906865333043200 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a3 * b7
    + (20231893560380620800 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 3 * a2 * b8
    + (22760880255428198400 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 ^ 2 * b6
    + (53108720595999129600 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a4 * b7
    + (60695680681141862400 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a5 * a3 * b8
    + (30347840340570931200 : R) * h ^ 70 * a7 ^ 3 * a6 ^ 2 * a4 ^ 2 * b8
    + (17702906865333043200 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 3 * b7
    + (60695680681141862400 : R) * h ^ 70 * a7 ^ 3 * a6 * a5 ^ 2 * a4 * b8
    + (5057973390095155200 : R) * h ^ 70 * a7 ^ 3 * a5 ^ 4 * b8
    + (1896740021285683200 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 5 * b5
    + (11380440127714099200 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a5 * b6
    + (13277180148999782400 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a4 * b7
    + (15173920170285465600 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 4 * a3 * b8
    + (26554360297999564800 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 ^ 2 * b7
    + (60695680681141862400 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 3 * a5 * a4 * b8
    + (30347840340570931200 : R) * h ^ 70 * a7 ^ 2 * a6 ^ 2 * a5 ^ 3 * b8
    + (758696008514273280 : R) * h ^ 70 * a7 * a6 ^ 6 * b6
    + (5310872059599912960 : R) * h ^ 70 * a7 * a6 ^ 5 * a5 * b7
    + (6069568068114186240 : R) * h ^ 70 * a7 * a6 ^ 5 * a4 * b8
    + (15173920170285465600 : R) * h ^ 70 * a7 * a6 ^ 4 * a5 ^ 2 * b8
    + (126449334752378880 : R) * h ^ 70 * a6 ^ 7 * b7
    + (1011594678019031040 : R) * h ^ 70 * a6 ^ 6 * a5 * b8
    - (829823759312486400 : R) * h ^ 64 * a7 ^ 7 * a6 * a0
    - (829823759312486400 : R) * h ^ 64 * a7 ^ 7 * a5 * a1
    - (829823759312486400 : R) * h ^ 64 * a7 ^ 7 * a4 * a2
    - (414911879656243200 : R) * h ^ 64 * a7 ^ 7 * a3 ^ 2
    + (1452191578796851200 : R) * h ^ 64 * a7 ^ 6 * a6 ^ 2 * a1
    + (2904383157593702400 : R) * h ^ 64 * a7 ^ 6 * a6 * a5 * a2
    + (2904383157593702400 : R) * h ^ 64 * a7 ^ 6 * a6 * a4 * a3
    + (1452191578796851200 : R) * h ^ 64 * a7 ^ 6 * a5 ^ 2 * a3
    + (1452191578796851200 : R) * h ^ 64 * a7 ^ 6 * a5 * a4 ^ 2
    + (11617532630374809600 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 3 * a2
    + (34852597891124428800 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a5 * a3
    + (17426298945562214400 : R) * h ^ 64 * a7 ^ 5 * a6 ^ 2 * a4 ^ 2

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `18`. -/
def degreeZeroSourceJetHeadBlock18_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1452191578796851200 : R) * t0 ^ 6 * u1 * a4 ^ 2
    + (17426298945562214400 : R) * t0 ^ 5 * v1 ^ 2 * a4 ^ 2
    + (13277180148999782400 : R) * t0 ^ 4 * u1 ^ 2 * a4 * w1
    + (15173920170285465600 : R) * t0 ^ 4 * u1 * a4 ^ 2 * s1
    + (12644933475237888000 : R) * t0 ^ 3 * v1 ^ 3 * u1 * b5
    + (15173920170285465600 : R) * t0 ^ 3 * v1 ^ 3 * a4 * b62
    + (22760880255428198400 : R) * t0 ^ 3 * v1 ^ 2 * u1 ^ 2 * b62
    + (53108720595999129600 : R) * t0 ^ 3 * v1 ^ 2 * u1 * a4 * w1
    + (30347840340570931200 : R) * t0 ^ 3 * v1 ^ 2 * a4 ^ 2 * s1
    + (17702906865333043200 : R) * t0 ^ 3 * v1 * u1 ^ 3 * w1
    + (60695680681141862400 : R) * t0 ^ 3 * v1 * u1 ^ 2 * a4 * s1
    + (5057973390095155200 : R) * t0 ^ 3 * u1 ^ 4 * s1
    + (1896740021285683200 : R) * t0 ^ 2 * v1 ^ 5 * b5
    + (11380440127714099200 : R) * t0 ^ 2 * v1 ^ 4 * u1 * b62
    + (13277180148999782400 : R) * t0 ^ 2 * v1 ^ 4 * a4 * w1
    + (26554360297999564800 : R) * t0 ^ 2 * v1 ^ 3 * u1 ^ 2 * w1
    + (60695680681141862400 : R) * t0 ^ 2 * v1 ^ 3 * u1 * a4 * s1
    + (30347840340570931200 : R) * t0 ^ 2 * v1 ^ 2 * u1 ^ 3 * s1
    + (758696008514273280 : R) * t0 * v1 ^ 6 * b62
    + (5310872059599912960 : R) * t0 * v1 ^ 5 * u1 * w1
    + (6069568068114186240 : R) * t0 * v1 ^ 5 * a4 * s1
    + (15173920170285465600 : R) * t0 * v1 ^ 4 * u1 ^ 2 * s1
    + (126449334752378880 : R) * v1 ^ 7 * w1
    + (1011594678019031040 : R) * v1 ^ 6 * u1 * s1

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `18`. -/
def degreeZeroSourceJetPlusBlock18_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (829823759312486400 : R) * h ^ 7 * t0 ^ 7 * v1 * a0
    - (829823759312486400 : R) * h ^ 5 * t0 ^ 7 * u1 * a1
    + (1452191578796851200 : R) * h ^ 5 * t0 ^ 6 * v1 ^ 2 * a1
    - (829823759312486400 : R) * h ^ 3 * t0 ^ 7 * a4 * a2
    - (414911879656243200 : R) * h ^ 3 * t0 ^ 7 * a3 ^ 2
    + (2904383157593702400 : R) * h ^ 3 * t0 ^ 6 * v1 * u1 * a2
    + (11617532630374809600 : R) * h ^ 3 * t0 ^ 5 * v1 ^ 3 * a2
    + (20231893560380620800 : R) * h ^ 3 * t0 ^ 3 * v1 ^ 3 * a2 * s1
    + (2904383157593702400 : R) * h * t0 ^ 6 * v1 * a4 * a3
    + (1452191578796851200 : R) * h * t0 ^ 6 * u1 ^ 2 * a3
    + (34852597891124428800 : R) * h * t0 ^ 5 * v1 ^ 2 * u1 * a3
    + (15173920170285465600 : R) * h * t0 ^ 4 * u1 ^ 2 * a3 * s1
    + (2528986695047577600 : R) * h * t0 ^ 3 * v1 ^ 4 * b4
    + (17702906865333043200 : R) * h * t0 ^ 3 * v1 ^ 3 * a3 * w1
    + (60695680681141862400 : R) * h * t0 ^ 3 * v1 ^ 2 * u1 * a3 * s1
    + (15173920170285465600 : R) * h * t0 ^ 2 * v1 ^ 4 * a3 * s1

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock18_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock18_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock18_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock18_810,
    degreeZeroSourceJetHeadBlock18_810,
    degreeZeroSourceJetPlusBlock18_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `19` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock19_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (34852597891124428800 : R) * h ^ 64 * a7 ^ 5 * a6 * a5 ^ 2 * a4
    + (2904383157593702400 : R) * h ^ 64 * a7 ^ 5 * a5 ^ 4
    + (25413352628944896000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 4 * a3
    + (101653410515779584000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 3 * a5 * a4
    + (50826705257889792000 : R) * h ^ 64 * a7 ^ 4 * a6 ^ 2 * a5 ^ 3
    + (29043831575937024000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 5 * a4
    + (72609578939842560000 : R) * h ^ 64 * a7 ^ 3 * a6 ^ 4 * a5 ^ 2
    + (18878490524359065600 : R) * h ^ 64 * a7 ^ 2 * a6 ^ 6 * a5
    + (829823759312486400 : R) * h ^ 64 * a7 * a6 ^ 8
    - (221718535691304960 : R) * h ^ 63 * a7 ^ 8 * a0 * lambda
    - (1773748285530439680 : R) * h ^ 63 * a7 ^ 7 * a6 * a1 * lambda
    - (1773748285530439680 : R) * h ^ 63 * a7 ^ 7 * a5 * a2 * lambda
    - (1773748285530439680 : R) * h ^ 63 * a7 ^ 7 * a4 * a3 * lambda
    - (6208118999356538880 : R) * h ^ 63 * a7 ^ 6 * a6 ^ 2 * a2 * lambda
    - (12416237998713077760 : R) * h ^ 63 * a7 ^ 6 * a6 * a5 * a3 * lambda
    - (6208118999356538880 : R) * h ^ 63 * a7 ^ 6 * a6 * a4 ^ 2 * lambda
    - (6208118999356538880 : R) * h ^ 63 * a7 ^ 6 * a5 ^ 2 * a4 * lambda
    - (12416237998713077760 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 3 * a3 * lambda
    - (37248713996139233280 : R) * h ^ 63 * a7 ^ 5 * a6 ^ 2 * a5 * a4 * lambda
    - (12416237998713077760 : R) * h ^ 63 * a7 ^ 5 * a6 * a5 ^ 3 * lambda
    - (15520297498391347200 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 4 * a4 * lambda
    - (31040594996782694400 : R) * h ^ 63 * a7 ^ 4 * a6 ^ 3 * a5 ^ 2 * lambda
    - (12416237998713077760 : R) * h ^ 63 * a7 ^ 3 * a6 ^ 5 * a5 * lambda
    - (886874142765219840 : R) * h ^ 63 * a7 ^ 2 * a6 ^ 7 * lambda
    - (13830395988541440 : R) * h ^ 62 * a7 ^ 8 * b1
    - (221286335816663040 : R) * h ^ 62 * a7 ^ 7 * a6 * b2
    - (331929503724994560 : R) * h ^ 62 * a7 ^ 7 * a5 * b3
    - (442572671633326080 : R) * h ^ 62 * a7 ^ 7 * a4 * b4
    - (553215839541657600 : R) * h ^ 62 * a7 ^ 7 * a3 * b5
    - (663859007449989120 : R) * h ^ 62 * a7 ^ 7 * a2 * b6
    - (774502175358320640 : R) * h ^ 62 * a7 ^ 7 * a1 * b7
    - (885145343266652160 : R) * h ^ 62 * a7 ^ 7 * a0 * b8
    - (1161753263037480960 : R) * h ^ 62 * a7 ^ 6 * a6 ^ 2 * b3
    - (3098008701433282560 : R) * h ^ 62 * a7 ^ 6 * a6 * a5 * b4
    - (3872510876791603200 : R) * h ^ 62 * a7 ^ 6 * a6 * a4 * b5
    - (4647013052149923840 : R) * h ^ 62 * a7 ^ 6 * a6 * a3 * b6
    - (5421515227508244480 : R) * h ^ 62 * a7 ^ 6 * a6 * a2 * b7
    - (6196017402866565120 : R) * h ^ 62 * a7 ^ 6 * a6 * a1 * b8
    - (1936255438395801600 : R) * h ^ 62 * a7 ^ 6 * a5 ^ 2 * b5
    - (4647013052149923840 : R) * h ^ 62 * a7 ^ 6 * a5 * a4 * b6

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `19`. -/
def degreeZeroSourceJetHeadBlock19_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (3872510876791603200 : R) * t0 ^ 6 * v1 * a4 * b5
    - (1936255438395801600 : R) * t0 ^ 6 * u1 ^ 2 * b5
    - (4647013052149923840 : R) * t0 ^ 6 * u1 * a4 * b62
    + (34852597891124428800 : R) * t0 ^ 5 * v1 * u1 ^ 2 * a4
    + (2904383157593702400 : R) * t0 ^ 5 * u1 ^ 4
    + (101653410515779584000 : R) * t0 ^ 4 * v1 ^ 3 * u1 * a4
    + (50826705257889792000 : R) * t0 ^ 4 * v1 ^ 2 * u1 ^ 3
    + (29043831575937024000 : R) * t0 ^ 3 * v1 ^ 5 * a4
    + (72609578939842560000 : R) * t0 ^ 3 * v1 ^ 4 * u1 ^ 2
    + (18878490524359065600 : R) * t0 ^ 2 * v1 ^ 6 * u1
    + (829823759312486400 : R) * t0 * v1 ^ 8

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `19`. -/
def degreeZeroSourceJetPlusBlock19_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (221718535691304960 : R) * h ^ 8 * t0 ^ 8 * a0 * lambda
    - (13830395988541440 : R) * h ^ 7 * t0 ^ 8 * b1
    - (885145343266652160 : R) * h ^ 7 * t0 ^ 7 * a0 * s1
    - (1773748285530439680 : R) * h ^ 6 * t0 ^ 7 * v1 * a1 * lambda
    - (221286335816663040 : R) * h ^ 5 * t0 ^ 7 * v1 * b2
    - (774502175358320640 : R) * h ^ 5 * t0 ^ 7 * a1 * w1
    - (6196017402866565120 : R) * h ^ 5 * t0 ^ 6 * v1 * a1 * s1
    - (1773748285530439680 : R) * h ^ 4 * t0 ^ 7 * u1 * a2 * lambda
    - (6208118999356538880 : R) * h ^ 4 * t0 ^ 6 * v1 ^ 2 * a2 * lambda
    - (331929503724994560 : R) * h ^ 3 * t0 ^ 7 * u1 * b3
    - (663859007449989120 : R) * h ^ 3 * t0 ^ 7 * a2 * b62
    - (1161753263037480960 : R) * h ^ 3 * t0 ^ 6 * v1 ^ 2 * b3
    - (5421515227508244480 : R) * h ^ 3 * t0 ^ 6 * v1 * a2 * w1
    - (1773748285530439680 : R) * h ^ 2 * t0 ^ 7 * a4 * a3 * lambda
    - (12416237998713077760 : R) * h ^ 2 * t0 ^ 6 * v1 * u1 * a3 * lambda
    - (12416237998713077760 : R) * h ^ 2 * t0 ^ 5 * v1 ^ 3 * a3 * lambda
    - (442572671633326080 : R) * h * t0 ^ 7 * a4 * b4
    - (553215839541657600 : R) * h * t0 ^ 7 * a3 * b5
    - (3098008701433282560 : R) * h * t0 ^ 6 * v1 * u1 * b4
    - (4647013052149923840 : R) * h * t0 ^ 6 * v1 * a3 * b62
    + (25413352628944896000 : R) * h * t0 ^ 4 * v1 ^ 4 * a3
    - (6208118999356538880 : R) * t0 ^ 6 * v1 * a4 ^ 2 * lambda
    - (6208118999356538880 : R) * t0 ^ 6 * u1 ^ 2 * a4 * lambda
    - (37248713996139233280 : R) * t0 ^ 5 * v1 ^ 2 * u1 * a4 * lambda
    - (12416237998713077760 : R) * t0 ^ 5 * v1 * u1 ^ 3 * lambda
    - (15520297498391347200 : R) * t0 ^ 4 * v1 ^ 4 * a4 * lambda
    - (31040594996782694400 : R) * t0 ^ 4 * v1 ^ 3 * u1 ^ 2 * lambda
    - (12416237998713077760 : R) * t0 ^ 3 * v1 ^ 5 * u1 * lambda
    - (886874142765219840 : R) * t0 ^ 2 * v1 ^ 7 * lambda

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock19_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock19_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock19_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock19_810,
    degreeZeroSourceJetHeadBlock19_810,
    degreeZeroSourceJetPlusBlock19_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `20` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock20_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5421515227508244480 : R) * h ^ 62 * a7 ^ 6 * a5 * a3 * b7
    - (6196017402866565120 : R) * h ^ 62 * a7 ^ 6 * a5 * a2 * b8
    - (2710757613754122240 : R) * h ^ 62 * a7 ^ 6 * a4 ^ 2 * b7
    - (6196017402866565120 : R) * h ^ 62 * a7 ^ 6 * a4 * a3 * b8
    - (3098008701433282560 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 3 * b4
    - (11617532630374809600 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a5 * b5
    - (13941039156449771520 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a4 * b6
    - (16264545682524733440 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a3 * b7
    - (18588052208599695360 : R) * h ^ 62 * a7 ^ 5 * a6 ^ 2 * a2 * b8
    - (13941039156449771520 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 ^ 2 * b6
    - (32529091365049466880 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a4 * b7
    - (37176104417199390720 : R) * h ^ 62 * a7 ^ 5 * a6 * a5 * a3 * b8
    - (18588052208599695360 : R) * h ^ 62 * a7 ^ 5 * a6 * a4 ^ 2 * b8
    - (5421515227508244480 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 3 * b7
    - (18588052208599695360 : R) * h ^ 62 * a7 ^ 5 * a5 ^ 2 * a4 * b8
    - (4840638595989504000 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 4 * b5
    - (23235065260749619200 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a5 * b6
    - (27107576137541222400 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a4 * b7
    - (30980087014332825600 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 3 * a3 * b8
    - (40661364206311833600 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 ^ 2 * b7
    - (92940261042998476800 : R) * h ^ 62 * a7 ^ 4 * a6 ^ 2 * a5 * a4 * b8
    - (30980087014332825600 : R) * h ^ 62 * a7 ^ 4 * a6 * a5 ^ 3 * b8
    - (4647013052149923840 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 5 * b6
    - (27107576137541222400 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a5 * b7
    - (30980087014332825600 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 4 * a4 * b8
    - (61960174028665651200 : R) * h ^ 62 * a7 ^ 3 * a6 ^ 3 * a5 ^ 2 * b8
    - (2710757613754122240 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 6 * b7
    - (18588052208599695360 : R) * h ^ 62 * a7 ^ 2 * a6 ^ 5 * a5 * b8
    - (885145343266652160 : R) * h ^ 62 * a7 * a6 ^ 7 * b8
    + (218981269818572800 : R) * h ^ 56 * a7 ^ 9 * a0
    + (862238749910630400 : R) * h ^ 56 * a7 ^ 8 * a6 * a1
    + (862238749910630400 : R) * h ^ 56 * a7 ^ 8 * a5 * a2
    + (862238749910630400 : R) * h ^ 56 * a7 ^ 8 * a4 * a3
    - (985415714183577600 : R) * h ^ 56 * a7 ^ 7 * a6 ^ 2 * a2
    - (1970831428367155200 : R) * h ^ 56 * a7 ^ 7 * a6 * a5 * a3
    - (985415714183577600 : R) * h ^ 56 * a7 ^ 7 * a6 * a4 ^ 2
    - (985415714183577600 : R) * h ^ 56 * a7 ^ 7 * a5 ^ 2 * a4
    - (12646168332022579200 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 3 * a3
    - (37938504996067737600 : R) * h ^ 56 * a7 ^ 6 * a6 ^ 2 * a5 * a4
    - (12646168332022579200 : R) * h ^ 56 * a7 ^ 6 * a6 * a5 ^ 3

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `20`. -/
def degreeZeroSourceJetHeadBlock20_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (985415714183577600 : R) * t0 ^ 7 * v1 * a4 ^ 2
    - (985415714183577600 : R) * t0 ^ 7 * u1 ^ 2 * a4
    - (37938504996067737600 : R) * t0 ^ 6 * v1 ^ 2 * u1 * a4
    - (12646168332022579200 : R) * t0 ^ 6 * v1 * u1 ^ 3
    - (2710757613754122240 : R) * t0 ^ 6 * a4 ^ 2 * w1
    - (11617532630374809600 : R) * t0 ^ 5 * v1 ^ 2 * u1 * b5
    - (13941039156449771520 : R) * t0 ^ 5 * v1 ^ 2 * a4 * b62
    - (13941039156449771520 : R) * t0 ^ 5 * v1 * u1 ^ 2 * b62
    - (32529091365049466880 : R) * t0 ^ 5 * v1 * u1 * a4 * w1
    - (18588052208599695360 : R) * t0 ^ 5 * v1 * a4 ^ 2 * s1
    - (5421515227508244480 : R) * t0 ^ 5 * u1 ^ 3 * w1
    - (18588052208599695360 : R) * t0 ^ 5 * u1 ^ 2 * a4 * s1
    - (4840638595989504000 : R) * t0 ^ 4 * v1 ^ 4 * b5
    - (23235065260749619200 : R) * t0 ^ 4 * v1 ^ 3 * u1 * b62
    - (27107576137541222400 : R) * t0 ^ 4 * v1 ^ 3 * a4 * w1
    - (40661364206311833600 : R) * t0 ^ 4 * v1 ^ 2 * u1 ^ 2 * w1
    - (92940261042998476800 : R) * t0 ^ 4 * v1 ^ 2 * u1 * a4 * s1
    - (30980087014332825600 : R) * t0 ^ 4 * v1 * u1 ^ 3 * s1
    - (4647013052149923840 : R) * t0 ^ 3 * v1 ^ 5 * b62
    - (27107576137541222400 : R) * t0 ^ 3 * v1 ^ 4 * u1 * w1
    - (30980087014332825600 : R) * t0 ^ 3 * v1 ^ 4 * a4 * s1
    - (61960174028665651200 : R) * t0 ^ 3 * v1 ^ 3 * u1 ^ 2 * s1
    - (2710757613754122240 : R) * t0 ^ 2 * v1 ^ 6 * w1
    - (18588052208599695360 : R) * t0 ^ 2 * v1 ^ 5 * u1 * s1
    - (885145343266652160 : R) * t0 * v1 ^ 7 * s1

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `20`. -/
def degreeZeroSourceJetPlusBlock20_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (218981269818572800 : R) * h ^ 7 * t0 ^ 9 * a0
    + (862238749910630400 : R) * h ^ 5 * t0 ^ 8 * v1 * a1
    + (862238749910630400 : R) * h ^ 3 * t0 ^ 8 * u1 * a2
    - (985415714183577600 : R) * h ^ 3 * t0 ^ 7 * v1 ^ 2 * a2
    - (6196017402866565120 : R) * h ^ 3 * t0 ^ 6 * u1 * a2 * s1
    - (18588052208599695360 : R) * h ^ 3 * t0 ^ 5 * v1 ^ 2 * a2 * s1
    + (862238749910630400 : R) * h * t0 ^ 8 * a4 * a3
    - (1970831428367155200 : R) * h * t0 ^ 7 * v1 * u1 * a3
    - (12646168332022579200 : R) * h * t0 ^ 6 * v1 ^ 3 * a3
    - (5421515227508244480 : R) * h * t0 ^ 6 * u1 * a3 * w1
    - (6196017402866565120 : R) * h * t0 ^ 6 * a4 * a3 * s1
    - (3098008701433282560 : R) * h * t0 ^ 5 * v1 ^ 3 * b4
    - (16264545682524733440 : R) * h * t0 ^ 5 * v1 ^ 2 * a3 * w1
    - (37176104417199390720 : R) * h * t0 ^ 5 * v1 * u1 * a3 * s1
    - (30980087014332825600 : R) * h * t0 ^ 4 * v1 ^ 3 * a3 * s1

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock20_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock20_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock20_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock20_810,
    degreeZeroSourceJetHeadBlock20_810,
    degreeZeroSourceJetPlusBlock20_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `21` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock21_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (34489549996425216000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 4 * a4
    - (68979099992850432000 : R) * h ^ 56 * a7 ^ 5 * a6 ^ 3 * a5 ^ 2
    - (50009847494816563200 : R) * h ^ 56 * a7 ^ 4 * a6 ^ 5 * a5
    - (6240966189829324800 : R) * h ^ 56 * a7 ^ 3 * a6 ^ 7
    + (200162566943539200 : R) * h ^ 55 * a7 ^ 9 * a1 * lambda
    + (1801463102491852800 : R) * h ^ 55 * a7 ^ 8 * a6 * a2 * lambda
    + (1801463102491852800 : R) * h ^ 55 * a7 ^ 8 * a5 * a3 * lambda
    + (900731551245926400 : R) * h ^ 55 * a7 ^ 8 * a4 ^ 2 * lambda
    + (7205852409967411200 : R) * h ^ 55 * a7 ^ 7 * a6 ^ 2 * a3 * lambda
    + (14411704819934822400 : R) * h ^ 55 * a7 ^ 7 * a6 * a5 * a4 * lambda
    + (2401950803322470400 : R) * h ^ 55 * a7 ^ 7 * a5 ^ 3 * lambda
    + (16813655623257292800 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 3 * a4 * lambda
    + (25220483434885939200 : R) * h ^ 55 * a7 ^ 6 * a6 ^ 2 * a5 ^ 2 * lambda
    + (25220483434885939200 : R) * h ^ 55 * a7 ^ 5 * a6 ^ 4 * a5 * lambda
    + (4203413905814323200 : R) * h ^ 55 * a7 ^ 4 * a6 ^ 6 * lambda
    + (21898126981857280 : R) * h ^ 54 * a7 ^ 9 * b2
    + (295624714255073280 : R) * h ^ 54 * a7 ^ 8 * a6 * b3
    + (394166285673431040 : R) * h ^ 54 * a7 ^ 8 * a5 * b4
    + (492707857091788800 : R) * h ^ 54 * a7 ^ 8 * a4 * b5
    + (591249428510146560 : R) * h ^ 54 * a7 ^ 8 * a3 * b6
    + (689790999928504320 : R) * h ^ 54 * a7 ^ 8 * a2 * b7
    + (788332571346862080 : R) * h ^ 54 * a7 ^ 8 * a1 * b8
    + (1576665142693724160 : R) * h ^ 54 * a7 ^ 7 * a6 ^ 2 * b4
    + (3941662856734310400 : R) * h ^ 54 * a7 ^ 7 * a6 * a5 * b5
    + (4729995428081172480 : R) * h ^ 54 * a7 ^ 7 * a6 * a4 * b6
    + (5518327999428034560 : R) * h ^ 54 * a7 ^ 7 * a6 * a3 * b7
    + (6306660570774896640 : R) * h ^ 54 * a7 ^ 7 * a6 * a2 * b8
    + (2364997714040586240 : R) * h ^ 54 * a7 ^ 7 * a5 ^ 2 * b6
    + (5518327999428034560 : R) * h ^ 54 * a7 ^ 7 * a5 * a4 * b7
    + (6306660570774896640 : R) * h ^ 54 * a7 ^ 7 * a5 * a3 * b8
    + (3153330285387448320 : R) * h ^ 54 * a7 ^ 7 * a4 ^ 2 * b8
    + (4598606666190028800 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 3 * b5
    + (16554983998284103680 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a5 * b6
    + (19314147997998120960 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a4 * b7
    + (22073311997712138240 : R) * h ^ 54 * a7 ^ 6 * a6 ^ 2 * a3 * b8
    + (19314147997998120960 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 ^ 2 * b7
    + (44146623995424276480 : R) * h ^ 54 * a7 ^ 6 * a6 * a5 * a4 * b8
    + (7357770665904046080 : R) * h ^ 54 * a7 ^ 6 * a5 ^ 3 * b8
    + (8277491999142051840 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 4 * b6
    + (38628295995996241920 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a5 * b7

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `21`. -/
def degreeZeroSourceJetHeadBlock21_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (492707857091788800 : R) * t0 ^ 8 * a4 * b5
    + (3941662856734310400 : R) * t0 ^ 7 * v1 * u1 * b5
    + (4729995428081172480 : R) * t0 ^ 7 * v1 * a4 * b62
    + (2364997714040586240 : R) * t0 ^ 7 * u1 ^ 2 * b62
    + (5518327999428034560 : R) * t0 ^ 7 * u1 * a4 * w1
    + (3153330285387448320 : R) * t0 ^ 7 * a4 ^ 2 * s1
    + (4598606666190028800 : R) * t0 ^ 6 * v1 ^ 3 * b5
    + (16554983998284103680 : R) * t0 ^ 6 * v1 ^ 2 * u1 * b62
    + (19314147997998120960 : R) * t0 ^ 6 * v1 ^ 2 * a4 * w1
    + (19314147997998120960 : R) * t0 ^ 6 * v1 * u1 ^ 2 * w1
    + (44146623995424276480 : R) * t0 ^ 6 * v1 * u1 * a4 * s1
    + (7357770665904046080 : R) * t0 ^ 6 * u1 ^ 3 * s1
    - (34489549996425216000 : R) * t0 ^ 5 * v1 ^ 4 * a4
    + (8277491999142051840 : R) * t0 ^ 5 * v1 ^ 4 * b62
    - (68979099992850432000 : R) * t0 ^ 5 * v1 ^ 3 * u1 ^ 2
    + (38628295995996241920 : R) * t0 ^ 5 * v1 ^ 3 * u1 * w1
    - (50009847494816563200 : R) * t0 ^ 4 * v1 ^ 5 * u1
    - (6240966189829324800 : R) * t0 ^ 3 * v1 ^ 7

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `21`. -/
def degreeZeroSourceJetPlusBlock21_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (200162566943539200 : R) * h ^ 6 * t0 ^ 9 * a1 * lambda
    + (21898126981857280 : R) * h ^ 5 * t0 ^ 9 * b2
    + (788332571346862080 : R) * h ^ 5 * t0 ^ 8 * a1 * s1
    + (1801463102491852800 : R) * h ^ 4 * t0 ^ 8 * v1 * a2 * lambda
    + (295624714255073280 : R) * h ^ 3 * t0 ^ 8 * v1 * b3
    + (689790999928504320 : R) * h ^ 3 * t0 ^ 8 * a2 * w1
    + (6306660570774896640 : R) * h ^ 3 * t0 ^ 7 * v1 * a2 * s1
    + (1801463102491852800 : R) * h ^ 2 * t0 ^ 8 * u1 * a3 * lambda
    + (7205852409967411200 : R) * h ^ 2 * t0 ^ 7 * v1 ^ 2 * a3 * lambda
    + (394166285673431040 : R) * h * t0 ^ 8 * u1 * b4
    + (591249428510146560 : R) * h * t0 ^ 8 * a3 * b62
    + (1576665142693724160 : R) * h * t0 ^ 7 * v1 ^ 2 * b4
    + (5518327999428034560 : R) * h * t0 ^ 7 * v1 * a3 * w1
    + (6306660570774896640 : R) * h * t0 ^ 7 * u1 * a3 * s1
    + (22073311997712138240 : R) * h * t0 ^ 6 * v1 ^ 2 * a3 * s1
    + (900731551245926400 : R) * t0 ^ 8 * a4 ^ 2 * lambda
    + (14411704819934822400 : R) * t0 ^ 7 * v1 * u1 * a4 * lambda
    + (2401950803322470400 : R) * t0 ^ 7 * u1 ^ 3 * lambda
    + (16813655623257292800 : R) * t0 ^ 6 * v1 ^ 3 * a4 * lambda
    + (25220483434885939200 : R) * t0 ^ 6 * v1 ^ 2 * u1 ^ 2 * lambda
    + (25220483434885939200 : R) * t0 ^ 5 * v1 ^ 4 * u1 * lambda
    + (4203413905814323200 : R) * t0 ^ 4 * v1 ^ 6 * lambda

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock21_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock21_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock21_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock21_810,
    degreeZeroSourceJetHeadBlock21_810,
    degreeZeroSourceJetPlusBlock21_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `22` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock22_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (44146623995424276480 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 3 * a4 * b8
    + (66219935993136414720 : R) * h ^ 54 * a7 ^ 5 * a6 ^ 2 * a5 ^ 2 * b8
    + (9657073998999060480 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 5 * b7
    + (55183279994280345600 : R) * h ^ 54 * a7 ^ 4 * a6 ^ 4 * a5 * b8
    + (7357770665904046080 : R) * h ^ 54 * a7 ^ 3 * a6 ^ 6 * b8
    - (189042424335564800 : R) * h ^ 48 * a7 ^ 10 * a1
    - (889611408637952000 : R) * h ^ 48 * a7 ^ 9 * a6 * a2
    - (889611408637952000 : R) * h ^ 48 * a7 ^ 9 * a5 * a3
    - (444805704318976000 : R) * h ^ 48 * a7 ^ 9 * a4 ^ 2
    + (500406417358848000 : R) * h ^ 48 * a7 ^ 8 * a6 ^ 2 * a3
    + (1000812834717696000 : R) * h ^ 48 * a7 ^ 8 * a6 * a5 * a4
    + (166802139119616000 : R) * h ^ 48 * a7 ^ 8 * a5 ^ 3
    + (13344171129569280000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 3 * a4
    + (20016256694353920000 : R) * h ^ 48 * a7 ^ 7 * a6 ^ 2 * a5 ^ 2
    + (44369369005817856000 : R) * h ^ 48 * a7 ^ 6 * a6 ^ 4 * a5
    + (13077287706977894400 : R) * h ^ 48 * a7 ^ 5 * a6 ^ 6
    - (182648342335979520 : R) * h ^ 47 * a7 ^ 10 * a2 * lambda
    - (1826483423359795200 : R) * h ^ 47 * a7 ^ 9 * a6 * a3 * lambda
    - (1826483423359795200 : R) * h ^ 47 * a7 ^ 9 * a5 * a4 * lambda
    - (8219175405119078400 : R) * h ^ 47 * a7 ^ 8 * a6 ^ 2 * a4 * lambda
    - (8219175405119078400 : R) * h ^ 47 * a7 ^ 8 * a6 * a5 ^ 2 * lambda
    - (21917801080317542400 : R) * h ^ 47 * a7 ^ 7 * a6 ^ 3 * a5 * lambda
    - (7671230378111139840 : R) * h ^ 47 * a7 ^ 6 * a6 ^ 5 * lambda
    - (26688342259138560 : R) * h ^ 46 * a7 ^ 10 * b3
    - (355844563455180800 : R) * h ^ 46 * a7 ^ 9 * a6 * b4
    - (444805704318976000 : R) * h ^ 46 * a7 ^ 9 * a5 * b5
    - (533766845182771200 : R) * h ^ 46 * a7 ^ 9 * a4 * b6
    - (622727986046566400 : R) * h ^ 46 * a7 ^ 9 * a3 * b7
    - (711689126910361600 : R) * h ^ 46 * a7 ^ 9 * a2 * b8
    - (2001625669435392000 : R) * h ^ 46 * a7 ^ 8 * a6 ^ 2 * b5
    - (4803901606644940800 : R) * h ^ 46 * a7 ^ 8 * a6 * a5 * b6
    - (5604551874419097600 : R) * h ^ 46 * a7 ^ 8 * a6 * a4 * b7
    - (6405202142193254400 : R) * h ^ 46 * a7 ^ 8 * a6 * a3 * b8
    - (2802275937209548800 : R) * h ^ 46 * a7 ^ 8 * a5 ^ 2 * b7
    - (6405202142193254400 : R) * h ^ 46 * a7 ^ 8 * a5 * a4 * b8
    - (6405202142193254400 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 3 * b6
    - (22418207497676390400 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a5 * b7
    - (25620808568773017600 : R) * h ^ 46 * a7 ^ 7 * a6 ^ 2 * a4 * b8
    - (25620808568773017600 : R) * h ^ 46 * a7 ^ 7 * a6 * a5 ^ 2 * b8
    - (13077287706977894400 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 4 * b7

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `22`. -/
def degreeZeroSourceJetHeadBlock22_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (444805704318976000 : R) * t0 ^ 9 * u1 * b5
    - (444805704318976000 : R) * t0 ^ 9 * a4 ^ 2
    - (533766845182771200 : R) * t0 ^ 9 * a4 * b62
    - (2001625669435392000 : R) * t0 ^ 8 * v1 ^ 2 * b5
    + (1000812834717696000 : R) * t0 ^ 8 * v1 * u1 * a4
    - (4803901606644940800 : R) * t0 ^ 8 * v1 * u1 * b62
    - (5604551874419097600 : R) * t0 ^ 8 * v1 * a4 * w1
    + (166802139119616000 : R) * t0 ^ 8 * u1 ^ 3
    - (2802275937209548800 : R) * t0 ^ 8 * u1 ^ 2 * w1
    - (6405202142193254400 : R) * t0 ^ 8 * u1 * a4 * s1
    + (13344171129569280000 : R) * t0 ^ 7 * v1 ^ 3 * a4
    - (6405202142193254400 : R) * t0 ^ 7 * v1 ^ 3 * b62
    + (20016256694353920000 : R) * t0 ^ 7 * v1 ^ 2 * u1 ^ 2
    - (22418207497676390400 : R) * t0 ^ 7 * v1 ^ 2 * u1 * w1
    - (25620808568773017600 : R) * t0 ^ 7 * v1 ^ 2 * a4 * s1
    - (25620808568773017600 : R) * t0 ^ 7 * v1 * u1 ^ 2 * s1
    + (44369369005817856000 : R) * t0 ^ 6 * v1 ^ 4 * u1
    - (13077287706977894400 : R) * t0 ^ 6 * v1 ^ 4 * w1
    + (13077287706977894400 : R) * t0 ^ 5 * v1 ^ 6
    + (44146623995424276480 : R) * t0 ^ 5 * v1 ^ 3 * a4 * s1
    + (66219935993136414720 : R) * t0 ^ 5 * v1 ^ 2 * u1 ^ 2 * s1
    + (9657073998999060480 : R) * t0 ^ 4 * v1 ^ 5 * w1
    + (55183279994280345600 : R) * t0 ^ 4 * v1 ^ 4 * u1 * s1
    + (7357770665904046080 : R) * t0 ^ 3 * v1 ^ 6 * s1

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `22`. -/
def degreeZeroSourceJetPlusBlock22_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (189042424335564800 : R) * h ^ 5 * t0 ^ 10 * a1
    - (182648342335979520 : R) * h ^ 4 * t0 ^ 10 * a2 * lambda
    - (26688342259138560 : R) * h ^ 3 * t0 ^ 10 * b3
    - (889611408637952000 : R) * h ^ 3 * t0 ^ 9 * v1 * a2
    - (711689126910361600 : R) * h ^ 3 * t0 ^ 9 * a2 * s1
    - (1826483423359795200 : R) * h ^ 2 * t0 ^ 9 * v1 * a3 * lambda
    - (355844563455180800 : R) * h * t0 ^ 9 * v1 * b4
    - (889611408637952000 : R) * h * t0 ^ 9 * u1 * a3
    - (622727986046566400 : R) * h * t0 ^ 9 * a3 * w1
    + (500406417358848000 : R) * h * t0 ^ 8 * v1 ^ 2 * a3
    - (6405202142193254400 : R) * h * t0 ^ 8 * v1 * a3 * s1
    - (1826483423359795200 : R) * t0 ^ 9 * u1 * a4 * lambda
    - (8219175405119078400 : R) * t0 ^ 8 * v1 ^ 2 * a4 * lambda
    - (8219175405119078400 : R) * t0 ^ 8 * v1 * u1 ^ 2 * lambda
    - (21917801080317542400 : R) * t0 ^ 7 * v1 ^ 3 * u1 * lambda
    - (7671230378111139840 : R) * t0 ^ 6 * v1 ^ 5 * lambda

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock22_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock22_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock22_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock22_810,
    degreeZeroSourceJetHeadBlock22_810,
    degreeZeroSourceJetPlusBlock22_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `23` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock23_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (59781886660470374400 : R) * h ^ 46 * a7 ^ 6 * a6 ^ 3 * a5 * b8
    - (17934565998141112320 : R) * h ^ 46 * a7 ^ 5 * a6 ^ 5 * b8
    + (166043947578163200 : R) * h ^ 40 * a7 ^ 11 * a2
    + (913241711679897600 : R) * h ^ 40 * a7 ^ 10 * a6 * a3
    + (913241711679897600 : R) * h ^ 40 * a7 ^ 10 * a5 * a4
    - (13698625675198464000 : R) * h ^ 40 * a7 ^ 8 * a6 ^ 3 * a5
    - (10958900540158771200 : R) * h ^ 40 * a7 ^ 7 * a6 ^ 5
    + (168119496922890240 : R) * h ^ 39 * a7 ^ 11 * a3 * lambda
    + (1849314466151792640 : R) * h ^ 39 * a7 ^ 10 * a6 * a4 * lambda
    + (924657233075896320 : R) * h ^ 39 * a7 ^ 10 * a5 ^ 2 * lambda
    + (9246572330758963200 : R) * h ^ 39 * a7 ^ 9 * a6 ^ 2 * a5 * lambda
    + (6934929248069222400 : R) * h ^ 39 * a7 ^ 8 * a6 ^ 4 * lambda
    + (29518924013895680 : R) * h ^ 38 * a7 ^ 11 * b4
    + (405885205191065600 : R) * h ^ 38 * a7 ^ 10 * a6 * b5
    + (487062246229278720 : R) * h ^ 38 * a7 ^ 10 * a5 * b6
    + (568239287267491840 : R) * h ^ 38 * a7 ^ 10 * a4 * b7
    + (649416328305704960 : R) * h ^ 38 * a7 ^ 10 * a3 * b8
    + (2435311231146393600 : R) * h ^ 38 * a7 ^ 9 * a6 ^ 2 * b6
    + (5682392872674918400 : R) * h ^ 38 * a7 ^ 9 * a6 * a5 * b7
    + (6494163283057049600 : R) * h ^ 38 * a7 ^ 9 * a6 * a4 * b8
    + (3247081641528524800 : R) * h ^ 38 * a7 ^ 9 * a5 ^ 2 * b8
    + (8523589309012377600 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 3 * b7
    + (29223734773756723200 : R) * h ^ 38 * a7 ^ 8 * a6 ^ 2 * a5 * b8
    + (19482489849171148800 : R) * h ^ 38 * a7 ^ 7 * a6 ^ 4 * b8
    - (147882890811801600 : R) * h ^ 32 * a7 ^ 12 * a3
    - (933997205127168000 : R) * h ^ 32 * a7 ^ 11 * a6 * a4
    - (466998602563584000 : R) * h ^ 32 * a7 ^ 11 * a5 ^ 2
    - (513698462819942400 : R) * h ^ 32 * a7 ^ 10 * a6 ^ 2 * a5
    + (3424656418799616000 : R) * h ^ 32 * a7 ^ 9 * a6 ^ 4
    - (155860783605596160 : R) * h ^ 31 * a7 ^ 12 * a4 * lambda
    - (1870329403267153920 : R) * h ^ 31 * a7 ^ 11 * a6 * a5 * lambda
    - (3428937239323115520 : R) * h ^ 31 * a7 ^ 10 * a6 ^ 3 * lambda
    - (31133240170905600 : R) * h ^ 30 * a7 ^ 12 * b5
    - (448318658461040640 : R) * h ^ 30 * a7 ^ 11 * a6 * b6
    - (523038434871214080 : R) * h ^ 30 * a7 ^ 11 * a5 * b7
    - (597758211281387520 : R) * h ^ 30 * a7 ^ 11 * a4 * b8
    - (2876711391791677440 : R) * h ^ 30 * a7 ^ 10 * a6 ^ 2 * b7
    - (6575340324095262720 : R) * h ^ 30 * a7 ^ 10 * a6 * a5 * b8
    - (10958900540158771200 : R) * h ^ 30 * a7 ^ 9 * a6 ^ 3 * b8
    + (133214344962048000 : R) * h ^ 24 * a7 ^ 13 * a4

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `23`. -/
def degreeZeroSourceJetHeadBlock23_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (133214344962048000 : R) * t0 ^ 13 * a4
    - (31133240170905600 : R) * t0 ^ 12 * b5
    - (933997205127168000 : R) * t0 ^ 11 * v1 * a4
    - (448318658461040640 : R) * t0 ^ 11 * v1 * b62
    - (466998602563584000 : R) * t0 ^ 11 * u1 ^ 2
    - (523038434871214080 : R) * t0 ^ 11 * u1 * w1
    - (597758211281387520 : R) * t0 ^ 11 * a4 * s1
    - (513698462819942400 : R) * t0 ^ 10 * v1 ^ 2 * u1
    - (2876711391791677440 : R) * t0 ^ 10 * v1 ^ 2 * w1
    - (6575340324095262720 : R) * t0 ^ 10 * v1 * u1 * s1
    + (405885205191065600 : R) * t0 ^ 10 * v1 * b5
    + (913241711679897600 : R) * t0 ^ 10 * u1 * a4
    + (487062246229278720 : R) * t0 ^ 10 * u1 * b62
    + (568239287267491840 : R) * t0 ^ 10 * a4 * w1
    + (3424656418799616000 : R) * t0 ^ 9 * v1 ^ 4
    - (10958900540158771200 : R) * t0 ^ 9 * v1 ^ 3 * s1
    + (2435311231146393600 : R) * t0 ^ 9 * v1 ^ 2 * b62
    + (5682392872674918400 : R) * t0 ^ 9 * v1 * u1 * w1
    + (6494163283057049600 : R) * t0 ^ 9 * v1 * a4 * s1
    + (3247081641528524800 : R) * t0 ^ 9 * u1 ^ 2 * s1
    - (13698625675198464000 : R) * t0 ^ 8 * v1 ^ 3 * u1
    + (8523589309012377600 : R) * t0 ^ 8 * v1 ^ 3 * w1
    + (29223734773756723200 : R) * t0 ^ 8 * v1 ^ 2 * u1 * s1
    - (10958900540158771200 : R) * t0 ^ 7 * v1 ^ 5
    + (19482489849171148800 : R) * t0 ^ 7 * v1 ^ 4 * s1
    - (59781886660470374400 : R) * t0 ^ 6 * v1 ^ 3 * u1 * s1
    - (17934565998141112320 : R) * t0 ^ 5 * v1 ^ 5 * s1

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `23`. -/
def degreeZeroSourceJetPlusBlock23_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (166043947578163200 : R) * h ^ 3 * t0 ^ 11 * a2
    + (168119496922890240 : R) * h ^ 2 * t0 ^ 11 * a3 * lambda
    - (147882890811801600 : R) * h * t0 ^ 12 * a3
    + (29518924013895680 : R) * h * t0 ^ 11 * b4
    + (913241711679897600 : R) * h * t0 ^ 10 * v1 * a3
    + (649416328305704960 : R) * h * t0 ^ 10 * a3 * s1
    - (155860783605596160 : R) * t0 ^ 12 * a4 * lambda
    - (1870329403267153920 : R) * t0 ^ 11 * v1 * u1 * lambda
    - (3428937239323115520 : R) * t0 ^ 10 * v1 ^ 3 * lambda
    + (1849314466151792640 : R) * t0 ^ 10 * v1 * a4 * lambda
    + (924657233075896320 : R) * t0 ^ 10 * u1 ^ 2 * lambda
    + (9246572330758963200 : R) * t0 ^ 9 * v1 ^ 2 * u1 * lambda
    + (6934929248069222400 : R) * t0 ^ 8 * v1 ^ 4 * lambda

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock23_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock23_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock23_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock23_810,
    degreeZeroSourceJetHeadBlock23_810,
    degreeZeroSourceJetPlusBlock23_810, degreeZeroSourceBaseOrder810]
  ring
set_option maxHeartbeats 200000000 in
/-- Source block `24` of the `h^{119}`-cleared numerator. -/
def degreeZeroClearedSourceBlock24_810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    (952482566478643200 : R) * h ^ 24 * a7 ^ 12 * a6 * a5
    + (346357296901324800 : R) * h ^ 24 * a7 ^ 11 * a6 ^ 3
    + (145370153939834880 : R) * h ^ 23 * a7 ^ 13 * a5 * lambda
    + (944906000608926720 : R) * h ^ 23 * a7 ^ 12 * a6 ^ 2 * lambda
    + (31971442790891520 : R) * h ^ 22 * a7 ^ 13 * b6
    + (484900215661854720 : R) * h ^ 22 * a7 ^ 12 * a6 * b7
    + (554171675042119680 : R) * h ^ 22 * a7 ^ 12 * a5 * b8
    + (3325030050252718080 : R) * h ^ 22 * a7 ^ 11 * a6 ^ 2 * b8
    - (121141794949862400 : R) * h ^ 16 * a7 ^ 14 * a5
    - (484567179799449600 : R) * h ^ 16 * a7 ^ 13 * a6 ^ 2
    - (136284519318595200 : R) * h ^ 15 * a7 ^ 14 * a6 * lambda
    - (32304478653296640 : R) * h ^ 14 * a7 ^ 14 * b7
    - (516871658452746240 : R) * h ^ 14 * a7 ^ 13 * a6 * b8
    + (111046645370707200 : R) * h ^ 8 * a7 ^ 15 * a6
    + (8020911814063155 : R) * h ^ 7 * a7 ^ 16 * lambda
    + (32304478653296640 : R) * h ^ 6 * a7 ^ 15 * b8
    - (8387881635621600 : R) * a7 ^ 17

set_option maxHeartbeats 200000000 in
/-- Order-`102` head contributed by source block `24`. -/
def degreeZeroSourceJetHeadBlock24_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (8387881635621600 : R) * t0 ^ 17
    + (111046645370707200 : R) * t0 ^ 15 * v1
    + (32304478653296640 : R) * t0 ^ 15 * s1
    - (121141794949862400 : R) * t0 ^ 14 * u1
    - (32304478653296640 : R) * t0 ^ 14 * w1
    - (484567179799449600 : R) * t0 ^ 13 * v1 ^ 2
    - (516871658452746240 : R) * t0 ^ 13 * v1 * s1
    + (31971442790891520 : R) * t0 ^ 13 * b62
    + (952482566478643200 : R) * t0 ^ 12 * v1 * u1
    + (484900215661854720 : R) * t0 ^ 12 * v1 * w1
    + (554171675042119680 : R) * t0 ^ 12 * u1 * s1
    + (346357296901324800 : R) * t0 ^ 11 * v1 ^ 3
    + (3325030050252718080 : R) * t0 ^ 11 * v1 ^ 2 * s1

set_option maxHeartbeats 200000000 in
/-- Plus remainder contributed by source block `24`. -/
def degreeZeroSourceJetPlusBlock24_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (8020911814063155 : R) * t0 ^ 16 * lambda
    - (136284519318595200 : R) * t0 ^ 14 * v1 * lambda
    + (145370153939834880 : R) * t0 ^ 13 * u1 * lambda
    + (944906000608926720 : R) * t0 ^ 12 * v1 ^ 2 * lambda

set_option maxHeartbeats 200000000 in
private theorem degreeZeroClearedSourceBlock24_810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSourceBlock24_810 h (h ^ 6 * t0) (h ^ 4 * v1)
        (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        (degreeZeroSourceJetHeadBlock24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda +
          h * degreeZeroSourceJetPlusBlock24_810 h t0 v1 u1 a4 a3 a2
            a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [degreeZeroClearedSourceBlock24_810,
    degreeZeroSourceJetHeadBlock24_810,
    degreeZeroSourceJetPlusBlock24_810, degreeZeroSourceBaseOrder810]
  ring

/-- The `977`-term integer numerator after substituting
the octic depression into the compact primitive and clearing `2^{62}`.
Generic `h`-degree `119`; raw `H_MIN = 0`. -/
def degreeZeroClearedSource810 (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroClearedSourceBlock0_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock1_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock2_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock3_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock4_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock5_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock6_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock7_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock8_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock9_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock10_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock11_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock12_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock13_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock14_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock15_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock16_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock17_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock18_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock19_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock20_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock21_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock22_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock23_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
  degreeZeroClearedSourceBlock24_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda

/-- The first surviving head of the degree-zero source jet. -/
def degreeZeroSourceJetHead810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroSourceJetHeadBlock0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetHeadBlock24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-- Remaining factor after `Head + h · Plus` is removed from the
order-`102` quotient. -/
def degreeZeroSourceJetPlus810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroSourceJetPlusBlock0_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock1_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock2_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock3_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock4_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock5_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock6_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock7_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock8_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock9_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock10_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock11_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock12_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock13_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock14_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock15_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock16_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock17_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock18_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock19_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock20_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock21_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock22_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock23_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroSourceJetPlusBlock24_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-- The exact quotient after the factor `h^{102}` is removed from the
cleared degree-zero source numerator on the unsolved left jet. -/
def degreeZeroSourceJetQuotient810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroSourceJetHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3
      b2 b1 lambda +
    h * degreeZeroSourceJetPlus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
      b5 b4 b3 b2 b1 lambda

/-- First head split of the order-`102` quotient. -/
theorem degreeZeroSourceJetQuotient810_orderExpansion
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetQuotient810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      degreeZeroSourceJetHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5
          b4 b3 b2 b1 lambda +
        h * degreeZeroSourceJetPlus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda :=
  rfl

theorem degreeZeroSourceJetQuotient810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetQuotient810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      degreeZeroSourceJetHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5
        b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetQuotient810, zero_mul, add_zero]

set_option maxHeartbeats 800000000 in
/-- Exact order-`102` factorization of the cleared source numerator on
the unsolved left jet. -/
theorem degreeZeroClearedSource810_leftJet_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSource810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
        a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3
        b2 b1 lambda =
      h ^ degreeZeroSourceBaseOrder810 *
        degreeZeroSourceJetQuotient810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 lambda := by
  unfold degreeZeroClearedSource810
  have hb0 := degreeZeroClearedSourceBlock0_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb1 := degreeZeroClearedSourceBlock1_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb2 := degreeZeroClearedSourceBlock2_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb3 := degreeZeroClearedSourceBlock3_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb4 := degreeZeroClearedSourceBlock4_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb5 := degreeZeroClearedSourceBlock5_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb6 := degreeZeroClearedSourceBlock6_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb7 := degreeZeroClearedSourceBlock7_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb8 := degreeZeroClearedSourceBlock8_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb9 := degreeZeroClearedSourceBlock9_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb10 := degreeZeroClearedSourceBlock10_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb11 := degreeZeroClearedSourceBlock11_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb12 := degreeZeroClearedSourceBlock12_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb13 := degreeZeroClearedSourceBlock13_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb14 := degreeZeroClearedSourceBlock14_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb15 := degreeZeroClearedSourceBlock15_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb16 := degreeZeroClearedSourceBlock16_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb17 := degreeZeroClearedSourceBlock17_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb18 := degreeZeroClearedSourceBlock18_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb19 := degreeZeroClearedSourceBlock19_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb20 := degreeZeroClearedSourceBlock20_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb21 := degreeZeroClearedSourceBlock21_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb22 := degreeZeroClearedSourceBlock22_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb23 := degreeZeroClearedSourceBlock23_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hb24 := degreeZeroClearedSourceBlock24_810_leftJet_factored
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23, hb24]
  simp only [degreeZeroSourceJetQuotient810, degreeZeroSourceJetHead810,
    degreeZeroSourceJetPlus810]
  ring

#print axioms degreeZeroClearedSource810_leftJet_factored
#print axioms degreeZeroSourceJetQuotient810_orderExpansion
#print axioms degreeZeroSourceJetQuotient810_zero

end DegreeZeroClearedSource810

section DegreeZeroSourceJetMap810

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 800000000 in
theorem degreeZeroSourceJetHead810_map
    (f : R →+* S)
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    f (degreeZeroSourceJetHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5
        b4 b3 b2 b1 lambda) =
      degreeZeroSourceJetHead810 (f t0) (f v1) (f u1) (f a4) (f a3)
        (f a2) (f a1) (f a0) (f s1) (f w1) (f b62) (f b5) (f b4) (f b3)
        (f b2) (f b1) (f lambda) := by
  simp only [degreeZeroSourceJetHead810, degreeZeroSourceJetHeadBlock0_810, degreeZeroSourceJetHeadBlock1_810, degreeZeroSourceJetHeadBlock2_810, degreeZeroSourceJetHeadBlock3_810, degreeZeroSourceJetHeadBlock4_810, degreeZeroSourceJetHeadBlock5_810, degreeZeroSourceJetHeadBlock6_810, degreeZeroSourceJetHeadBlock7_810, degreeZeroSourceJetHeadBlock8_810, degreeZeroSourceJetHeadBlock9_810, degreeZeroSourceJetHeadBlock10_810, degreeZeroSourceJetHeadBlock11_810, degreeZeroSourceJetHeadBlock12_810, degreeZeroSourceJetHeadBlock13_810, degreeZeroSourceJetHeadBlock14_810, degreeZeroSourceJetHeadBlock15_810, degreeZeroSourceJetHeadBlock16_810, degreeZeroSourceJetHeadBlock17_810, degreeZeroSourceJetHeadBlock18_810, degreeZeroSourceJetHeadBlock19_810, degreeZeroSourceJetHeadBlock20_810, degreeZeroSourceJetHeadBlock21_810, degreeZeroSourceJetHeadBlock22_810, degreeZeroSourceJetHeadBlock23_810, degreeZeroSourceJetHeadBlock24_810, map_add,
    map_sub, map_neg, map_mul, map_pow, map_ofNat, map_zero]

set_option maxHeartbeats 800000000 in
theorem degreeZeroSourceJetPlus810_map
    (f : R →+* S)
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    f (degreeZeroSourceJetPlus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroSourceJetPlus810 (f h) (f t0) (f v1) (f u1) (f a4)
        (f a3) (f a2) (f a1) (f a0) (f s1) (f w1) (f b62) (f b5) (f b4)
        (f b3) (f b2) (f b1) (f lambda) := by
  simp only [degreeZeroSourceJetPlus810, degreeZeroSourceJetPlusBlock0_810, degreeZeroSourceJetPlusBlock1_810, degreeZeroSourceJetPlusBlock2_810, degreeZeroSourceJetPlusBlock3_810, degreeZeroSourceJetPlusBlock4_810, degreeZeroSourceJetPlusBlock5_810, degreeZeroSourceJetPlusBlock6_810, degreeZeroSourceJetPlusBlock7_810, degreeZeroSourceJetPlusBlock8_810, degreeZeroSourceJetPlusBlock9_810, degreeZeroSourceJetPlusBlock10_810, degreeZeroSourceJetPlusBlock11_810, degreeZeroSourceJetPlusBlock12_810, degreeZeroSourceJetPlusBlock13_810, degreeZeroSourceJetPlusBlock14_810, degreeZeroSourceJetPlusBlock15_810, degreeZeroSourceJetPlusBlock16_810, degreeZeroSourceJetPlusBlock17_810, degreeZeroSourceJetPlusBlock18_810, degreeZeroSourceJetPlusBlock19_810, degreeZeroSourceJetPlusBlock20_810, degreeZeroSourceJetPlusBlock21_810, degreeZeroSourceJetPlusBlock22_810, degreeZeroSourceJetPlusBlock23_810, degreeZeroSourceJetPlusBlock24_810, map_add,
    map_sub, map_neg, map_mul, map_pow, map_ofNat, map_zero]

theorem degreeZeroSourceJetQuotient810_map
    (f : R →+* S)
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    f (degreeZeroSourceJetQuotient810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda) =
      degreeZeroSourceJetQuotient810 (f h) (f t0) (f v1) (f u1) (f a4)
        (f a3) (f a2) (f a1) (f a0) (f s1) (f w1) (f b62) (f b5) (f b4)
        (f b3) (f b2) (f b1) (f lambda) := by
  simp only [degreeZeroSourceJetQuotient810, map_add, map_mul,
    degreeZeroSourceJetHead810_map, degreeZeroSourceJetPlus810_map]

set_option maxHeartbeats 800000000 in
theorem degreeZeroClearedSource810_map
    (f : R →+* S)
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    f (degreeZeroClearedSource810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroClearedSource810 (f h) (f a7) (f a6) (f a5) (f a4)
        (f a3) (f a2) (f a1) (f a0) (f b8) (f b7) (f b6) (f b5) (f b4)
        (f b3) (f b2) (f b1) (f lambda) := by
  simp only [degreeZeroClearedSource810, degreeZeroClearedSourceBlock0_810, degreeZeroClearedSourceBlock1_810, degreeZeroClearedSourceBlock2_810, degreeZeroClearedSourceBlock3_810, degreeZeroClearedSourceBlock4_810, degreeZeroClearedSourceBlock5_810, degreeZeroClearedSourceBlock6_810, degreeZeroClearedSourceBlock7_810, degreeZeroClearedSourceBlock8_810, degreeZeroClearedSourceBlock9_810, degreeZeroClearedSourceBlock10_810, degreeZeroClearedSourceBlock11_810, degreeZeroClearedSourceBlock12_810, degreeZeroClearedSourceBlock13_810, degreeZeroClearedSourceBlock14_810, degreeZeroClearedSourceBlock15_810, degreeZeroClearedSourceBlock16_810, degreeZeroClearedSourceBlock17_810, degreeZeroClearedSourceBlock18_810, degreeZeroClearedSourceBlock19_810, degreeZeroClearedSourceBlock20_810, degreeZeroClearedSourceBlock21_810, degreeZeroClearedSourceBlock22_810, degreeZeroClearedSourceBlock23_810, degreeZeroClearedSourceBlock24_810, map_add,
    map_sub, map_neg, map_mul, map_pow, map_ofNat, map_zero]

#print axioms degreeZeroSourceJetQuotient810_map
#print axioms degreeZeroSourceJetHead810_map

end DegreeZeroSourceJetMap810

section DegreeZeroSourceJetEval810

variable {k : Type*} [CommRing k]

theorem degreeZeroSourceJetQuotient810_eval
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroSourceJetQuotient810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroSourceJetQuotient810 (h.eval a) (t0.eval a) (v1.eval a)
        (u1.eval a) (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a)
        (a0.eval a) (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a)
        (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    degreeZeroSourceJetQuotient810_map (Polynomial.evalRingHom a) h t0
      v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

theorem degreeZeroSourceJetQuotient810_eval_root
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) (hroot : h.eval a = 0) :
    (degreeZeroSourceJetQuotient810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroSourceJetHead810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  rw [degreeZeroSourceJetQuotient810_eval, hroot,
    degreeZeroSourceJetQuotient810_zero]

theorem degreeZeroSourceJetHead810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroSourceJetHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5
        b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroSourceJetHead810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    degreeZeroSourceJetHead810_map (Polynomial.evalRingHom a) t0 v1 u1
      a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms degreeZeroSourceJetQuotient810_eval_root

end DegreeZeroSourceJetEval810

/-! ## Z4. Remaining order-`17` head obstruction on the left jet -/

section DegreeZeroSourceLeftJet810

variable {F : Type*} [Field F] [CharZero F]

/-- The grouped degree-zero primitive on the octic-decic depression of
the unsolved left jet.  The ninth-power scalar `λ` is substituted into
`b₉` exactly as in the source clearing. -/
def sourceRhoResidualLeftJet810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : F) : F :=
  sourceRhoResidual810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3
    a2 a1 a0
    (((5 : F) * (h ^ 6 * t0) * h ^ 2 - lambda * h ^ 9) / 4)
    (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1

end DegreeZeroSourceLeftJet810

section DegreeZeroSourceHead810

variable {k : Type*} [Field k] [CharZero k]

/-- The order-`102` head vanishes once the cleared source numerator has
the ordinary simple-pole derivative, with remaining pole order `17`.
The remaining-`17` clearing of the scaled left-jet primitive is the
displayed hypothesis; it is not discharged in this file. -/
theorem degreeZeroSourceJetHead810_zero_of_deriv_eq_simplePole
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0
            s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
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
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
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
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    degreeZeroSourceJetHead810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  let A0 : k[X] :=
    degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
      b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)
  let rho : RatFunc k :=
    (degreeZeroClearedIntegerScale810 : RatFunc k) *
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
        (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)
  have hhead :=
    localLinearPole_head_eval_zero_of_deriv_eq_simplePole810
      degreeZeroEffectiveTowerLength810 (by decide) a j h0 A0 rho
      hdegree hroot (by simpa [A0, rho] using hclear)
      (by simpa [rho] using hderiv)
  rw [← degreeZeroSourceJetQuotient810_eval_root h0 t0 v1 u1 a4 a3 a2
    a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda a hroot]
  exact hhead

#print axioms degreeZeroSourceJetHead810_zero_of_deriv_eq_simplePole

end DegreeZeroSourceHead810

end Max11DegreeRoutes
