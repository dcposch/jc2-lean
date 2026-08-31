import Sol610ScaleTwoAlignedTwelfthFaceScratch
import Fable610ScaleZeroEleventhDefectScratch

/-! # Weight-thirty algebraic block for the aligned `(6,10)` twelfth row

This scratch file isolates the chamber-free polynomial hidden in the
weight-sixty square-core formula.  The scale-zero formula with aligned
discriminator `lambda = 0` contains only even powers of its square root;
halving those powers gives the candidate weight-thirty defect below.

The remaining differential multiplier calculation is deliberately
factored through an explicit correction-module interface.  Its exact
prior-row boundary is `D,E,F,G,I,J,L,Omega,Lambda`; no face discriminator
or source correction is included.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000

/-- Homogeneous block 1 of the weight-thirty twelfth defect. -/
def alignedTwelfthDefectBlock1_610 {F : Type*} [CommRing F]
    (H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) : F[X] :=
    (8107385 : F[X]) * a5 ^ 12
    - (80514720 : F[X]) * a4 * a5 ^ 10 * H ^ 3
    - (12077208 : F[X]) * a5 ^ 10 * b8 * H ^ 1
    + (84192075 : F[X]) * a3 * a5 ^ 9 * H ^ 6
    + (12193335 : F[X]) * a5 ^ 9 * b7 * H ^ 4
    - (88609950 : F[X]) * a2 * a5 ^ 8 * H ^ 9
    + (261285750 : F[X]) * a4 ^ 2 * a5 ^ 8 * H ^ 6
    + (125417160 : F[X]) * a4 * a5 ^ 8 * b8 * H ^ 4
    - (12269070 : F[X]) * a5 ^ 8 * b6 * H ^ 7
    + (94062870 : F[X]) * a1 * a5 ^ 7 * H ^ 12
    - (463498200 : F[X]) * a3 * a4 * a5 ^ 7 * H ^ 9
    - (130870080 : F[X]) * a3 * a5 ^ 7 * b8 * H ^ 7
    - (114511320 : F[X]) * a4 * a5 ^ 7 * b7 * H ^ 7
    + (12269070 : F[X]) * a5 ^ 7 * b5 * H ^ 10
    - (101039400 : F[X]) * a0 * a5 ^ 6 * H ^ 15
    + (400789620 : F[X]) * a2 * a4 * a5 ^ 6 * H ^ 12
    + (137413584 : F[X]) * a2 * a5 ^ 6 * b8 * H ^ 10
    + (200394810 : F[X]) * a3 ^ 2 * a5 ^ 6 * H ^ 12
    + (120236886 : F[X]) * a3 * a5 ^ 6 * b7 * H ^ 10
    - (254469600 : F[X]) * a4 ^ 3 * a5 ^ 6 * H ^ 9
    - (458045280 : F[X]) * a4 ^ 2 * a5 ^ 6 * b8 * H ^ 7
    + (103060188 : F[X]) * a4 * a5 ^ 6 * b6 * H ^ 10
    - (12124728 : F[X]) * a5 ^ 6 * b4 * H ^ 13
    - (333430020 : F[X]) * a1 * a4 * a5 ^ 5 * H ^ 15
    - (145496736 : F[X]) * a1 * a5 ^ 5 * b8 * H ^ 13
    - (333430020 : F[X]) * a2 * a3 * a5 ^ 5 * H ^ 15
    - (127309644 : F[X]) * a2 * a5 ^ 5 * b7 * H ^ 13
    + (429417450 : F[X]) * a3 * a4 ^ 2 * a5 ^ 5 * H ^ 12
    + (824481504 : F[X]) * a3 * a4 * a5 ^ 5 * b8 * H ^ 10
    - (109122552 : F[X]) * a3 * a5 ^ 5 * b6 * H ^ 13
    + (360710658 : F[X]) * a4 ^ 2 * a5 ^ 5 * b7 * H ^ 10
    - (90935460 : F[X]) * a4 * a5 ^ 5 * b5 * H ^ 13
    + (11691702 : F[X]) * a5 ^ 5 * b3 * H ^ 16

/-- Homogeneous block 2 of the weight-thirty twelfth defect. -/
def alignedTwelfthDefectBlock2_610 {F : Type*} [CommRing F]
    (H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) : F[X] :=
    (259815600 : F[X]) * a0 * a4 * a5 ^ 4 * H ^ 18
    + (155889360 : F[X]) * a0 * a5 ^ 4 * b8 * H ^ 16
    + (259815600 : F[X]) * a1 * a3 * a5 ^ 4 * H ^ 18
    + (136403190 : F[X]) * a1 * a5 ^ 4 * b7 * H ^ 16
    + (129907800 : F[X]) * a2 ^ 2 * a5 ^ 4 * H ^ 18
    - (151559100 : F[X]) * a2 * a4 ^ 2 * a5 ^ 4 * H ^ 15
    - (727483680 : F[X]) * a2 * a4 * a5 ^ 4 * b8 * H ^ 13
    + (116917020 : F[X]) * a2 * a5 ^ 4 * b6 * H ^ 16
    - (151559100 : F[X]) * a3 ^ 2 * a4 * a5 ^ 4 * H ^ 15
    - (363741840 : F[X]) * a3 ^ 2 * a5 ^ 4 * b8 * H ^ 13
    - (636548220 : F[X]) * a3 * a4 * a5 ^ 4 * b7 * H ^ 13
    + (97430850 : F[X]) * a3 * a5 ^ 4 * b5 * H ^ 16
    - (143139150 : F[X]) * a4 ^ 4 * a5 ^ 4 * H ^ 12
    + (687067920 : F[X]) * a4 ^ 3 * a5 ^ 4 * b8 * H ^ 10
    - (272806380 : F[X]) * a4 ^ 2 * a5 ^ 4 * b6 * H ^ 13
    + (77944680 : F[X]) * a4 * a5 ^ 4 * b4 * H ^ 16
    - (10628820 : F[X]) * a5 ^ 4 * b2 * H ^ 19
    - (177147000 : F[X]) * a0 * a3 * a5 ^ 3 * H ^ 21
    - (148803480 : F[X]) * a0 * a5 ^ 3 * b7 * H ^ 19
    - (177147000 : F[X]) * a1 * a2 * a5 ^ 3 * H ^ 21
    - (64953900 : F[X]) * a1 * a4 ^ 2 * a5 ^ 3 * H ^ 18
    + (623557440 : F[X]) * a1 * a4 * a5 ^ 3 * b8 * H ^ 16
    - (127545840 : F[X]) * a1 * a5 ^ 3 * b6 * H ^ 19
    - (129907800 : F[X]) * a2 * a3 * a4 * a5 ^ 3 * H ^ 18
    + (623557440 : F[X]) * a2 * a3 * a5 ^ 3 * b8 * H ^ 16
    + (545612760 : F[X]) * a2 * a4 * a5 ^ 3 * b7 * H ^ 16
    - (106288200 : F[X]) * a2 * a5 ^ 3 * b5 * H ^ 19
    - (21651300 : F[X]) * a3 ^ 3 * a5 ^ 3 * H ^ 18
    + (272806380 : F[X]) * a3 ^ 2 * a5 ^ 3 * b7 * H ^ 16
    + (707275800 : F[X]) * a3 * a4 ^ 3 * a5 ^ 3 * H ^ 15
    - (1454967360 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * b8 * H ^ 13
    + (467668080 : F[X]) * a3 * a4 * a5 ^ 3 * b6 * H ^ 16
    - (85030560 : F[X]) * a3 * a5 ^ 3 * b4 * H ^ 19
    - (424365480 : F[X]) * a4 ^ 3 * a5 ^ 3 * b7 * H ^ 13
    + (194861700 : F[X]) * a4 ^ 2 * a5 ^ 3 * b5 * H ^ 16
    - (63772920 : F[X]) * a4 * a5 ^ 3 * b3 * H ^ 19
    + (7971615 : F[X]) * a5 ^ 3 * b1 * H ^ 22

/-- Homogeneous block 3 of the weight-thirty twelfth defect. -/
def alignedTwelfthDefectBlock3_610 {F : Type*} [CommRing F]
    (H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) : F[X] :=
    (79716150 : F[X]) * a0 * a2 * a5 ^ 2 * H ^ 24
    + (212576400 : F[X]) * a0 * a4 ^ 2 * a5 ^ 2 * H ^ 21
    - (510183360 : F[X]) * a0 * a4 * a5 ^ 2 * b8 * H ^ 19
    + (143489070 : F[X]) * a0 * a5 ^ 2 * b6 * H ^ 22
    + (39858075 : F[X]) * a1 ^ 2 * a5 ^ 2 * H ^ 24
    + (425152800 : F[X]) * a1 * a3 * a4 * a5 ^ 2 * H ^ 21
    - (510183360 : F[X]) * a1 * a3 * a5 ^ 2 * b8 * H ^ 19
    - (446410440 : F[X]) * a1 * a4 * a5 ^ 2 * b7 * H ^ 19
    + (119574225 : F[X]) * a1 * a5 ^ 2 * b5 * H ^ 22
    + (212576400 : F[X]) * a2 ^ 2 * a4 * a5 ^ 2 * H ^ 21
    - (255091680 : F[X]) * a2 ^ 2 * a5 ^ 2 * b8 * H ^ 19
    + (212576400 : F[X]) * a2 * a3 ^ 2 * a5 ^ 2 * H ^ 21
    - (446410440 : F[X]) * a2 * a3 * a5 ^ 2 * b7 * H ^ 19
    - (649539000 : F[X]) * a2 * a4 ^ 3 * a5 ^ 2 * H ^ 18
    + (935336160 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * b8 * H ^ 16
    - (382637520 : F[X]) * a2 * a4 * a5 ^ 2 * b6 * H ^ 19
    + (95659380 : F[X]) * a2 * a5 ^ 2 * b4 * H ^ 22
    - (974308500 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 ^ 2 * H ^ 18
    + (935336160 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * b8 * H ^ 16
    - (191318760 : F[X]) * a3 ^ 2 * a5 ^ 2 * b6 * H ^ 19
    + (818419140 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * b7 * H ^ 16
    - (318864600 : F[X]) * a3 * a4 * a5 ^ 2 * b5 * H ^ 19
    + (71744535 : F[X]) * a3 * a5 ^ 2 * b3 * H ^ 22
    + (242494560 : F[X]) * a4 ^ 5 * a5 ^ 2 * H ^ 15
    - (363741840 : F[X]) * a4 ^ 4 * a5 ^ 2 * b8 * H ^ 13
    + (233834040 : F[X]) * a4 ^ 3 * a5 ^ 2 * b6 * H ^ 16
    - (127545840 : F[X]) * a4 ^ 2 * a5 ^ 2 * b4 * H ^ 19
    + (47829690 : F[X]) * a4 * a5 ^ 2 * b2 * H ^ 22

/-- Homogeneous block 4 of the weight-thirty twelfth defect. -/
def alignedTwelfthDefectBlock4_610 {F : Type*} [CommRing F]
    (H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) : F[X] :=
    (47829690 : F[X]) * a0 * a1 * a5 * H ^ 27
    - (558013050 : F[X]) * a0 * a3 * a4 * a5 * H ^ 24
    + (382637520 : F[X]) * a0 * a3 * a5 * b8 * H ^ 22
    + (334807830 : F[X]) * a0 * a4 * a5 * b7 * H ^ 22
    - (143489070 : F[X]) * a0 * a5 * b5 * H ^ 25
    - (558013050 : F[X]) * a1 * a2 * a4 * a5 * H ^ 24
    + (382637520 : F[X]) * a1 * a2 * a5 * b8 * H ^ 22
    - (279006525 : F[X]) * a1 * a3 ^ 2 * a5 * H ^ 24
    + (334807830 : F[X]) * a1 * a3 * a5 * b7 * H ^ 22
    + (460582200 : F[X]) * a1 * a4 ^ 3 * a5 * H ^ 21
    - (510183360 : F[X]) * a1 * a4 ^ 2 * a5 * b8 * H ^ 19
    + (286978140 : F[X]) * a1 * a4 * a5 * b6 * H ^ 22
    - (114791256 : F[X]) * a1 * a5 * b4 * H ^ 25
    - (279006525 : F[X]) * a2 ^ 2 * a3 * a5 * H ^ 24
    + (167403915 : F[X]) * a2 ^ 2 * a5 * b7 * H ^ 22
    + (1381746600 : F[X]) * a2 * a3 * a4 ^ 2 * a5 * H ^ 21
    - (1020366720 : F[X]) * a2 * a3 * a4 * a5 * b8 * H ^ 19
    + (286978140 : F[X]) * a2 * a3 * a5 * b6 * H ^ 22
    - (446410440 : F[X]) * a2 * a4 ^ 2 * a5 * b7 * H ^ 19
    + (239148450 : F[X]) * a2 * a4 * a5 * b5 * H ^ 22
    - (86093442 : F[X]) * a2 * a5 * b3 * H ^ 25
    + (460582200 : F[X]) * a3 ^ 3 * a4 * a5 * H ^ 21
    - (170061120 : F[X]) * a3 ^ 3 * a5 * b8 * H ^ 19
    - (446410440 : F[X]) * a3 ^ 2 * a4 * a5 * b7 * H ^ 19
    + (119574225 : F[X]) * a3 ^ 2 * a5 * b5 * H ^ 22
    - (617062050 : F[X]) * a3 * a4 ^ 4 * a5 * H ^ 18
    + (623557440 : F[X]) * a3 * a4 ^ 3 * a5 * b8 * H ^ 16
    - (382637520 : F[X]) * a3 * a4 ^ 2 * a5 * b6 * H ^ 19
    + (191318760 : F[X]) * a3 * a4 * a5 * b4 * H ^ 22
    - (57395628 : F[X]) * a3 * a5 * b2 * H ^ 25
    + (136403190 : F[X]) * a4 ^ 4 * a5 * b7 * H ^ 16
    - (106288200 : F[X]) * a4 ^ 3 * a5 * b5 * H ^ 19
    + (71744535 : F[X]) * a4 ^ 2 * a5 * b3 * H ^ 22
    - (28697814 : F[X]) * a4 * a5 * b1 * H ^ 25
    - (143489070 : F[X]) * a0 ^ 2 * H ^ 30
    + (478296900 : F[X]) * a0 * a2 * a4 * H ^ 27
    - (229582512 : F[X]) * a0 * a2 * b8 * H ^ 25
    + (239148450 : F[X]) * a0 * a3 ^ 2 * H ^ 27
    - (200884698 : F[X]) * a0 * a3 * b7 * H ^ 25
    - (212576400 : F[X]) * a0 * a4 ^ 3 * H ^ 24

/-- Homogeneous block 5 of the weight-thirty twelfth defect. -/
def alignedTwelfthDefectBlock5_610 {F : Type*} [CommRing F]
    (H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) : F[X] :=
    (191318760 : F[X]) * a0 * a4 ^ 2 * b8 * H ^ 22
    - (172186884 : F[X]) * a0 * a4 * b6 * H ^ 25
    + (172186884 : F[X]) * a0 * b4 * H ^ 28
    + (239148450 : F[X]) * a1 ^ 2 * a4 * H ^ 27
    - (114791256 : F[X]) * a1 ^ 2 * b8 * H ^ 25
    + (478296900 : F[X]) * a1 * a2 * a3 * H ^ 27
    - (200884698 : F[X]) * a1 * a2 * b7 * H ^ 25
    - (637729200 : F[X]) * a1 * a3 * a4 ^ 2 * H ^ 24
    + (382637520 : F[X]) * a1 * a3 * a4 * b8 * H ^ 22
    - (172186884 : F[X]) * a1 * a3 * b6 * H ^ 25
    + (167403915 : F[X]) * a1 * a4 ^ 2 * b7 * H ^ 22
    - (143489070 : F[X]) * a1 * a4 * b5 * H ^ 25
    + (129140163 : F[X]) * a1 * b3 * H ^ 28
    + (79716150 : F[X]) * a2 ^ 3 * H ^ 27
    - (318864600 : F[X]) * a2 ^ 2 * a4 ^ 2 * H ^ 24
    + (191318760 : F[X]) * a2 ^ 2 * a4 * b8 * H ^ 22
    - (86093442 : F[X]) * a2 ^ 2 * b6 * H ^ 25
    - (637729200 : F[X]) * a2 * a3 ^ 2 * a4 * H ^ 24
    + (191318760 : F[X]) * a2 * a3 ^ 2 * b8 * H ^ 22
    + (334807830 : F[X]) * a2 * a3 * a4 * b7 * H ^ 22
    - (143489070 : F[X]) * a2 * a3 * b5 * H ^ 25
    + (194861700 : F[X]) * a2 * a4 ^ 4 * H ^ 21
    - (170061120 : F[X]) * a2 * a4 ^ 3 * b8 * H ^ 19
    + (143489070 : F[X]) * a2 * a4 ^ 2 * b6 * H ^ 22
    - (114791256 : F[X]) * a2 * a4 * b4 * H ^ 25
    + (86093442 : F[X]) * a2 * b2 * H ^ 28
    - (53144100 : F[X]) * a3 ^ 4 * H ^ 24
    + (55801305 : F[X]) * a3 ^ 3 * b7 * H ^ 22
    + (389723400 : F[X]) * a3 ^ 2 * a4 ^ 3 * H ^ 21
    - (255091680 : F[X]) * a3 ^ 2 * a4 ^ 2 * b8 * H ^ 19
    + (143489070 : F[X]) * a3 ^ 2 * a4 * b6 * H ^ 22
    - (57395628 : F[X]) * a3 ^ 2 * b4 * H ^ 25
    - (148803480 : F[X]) * a3 * a4 ^ 3 * b7 * H ^ 19
    + (119574225 : F[X]) * a3 * a4 ^ 2 * b5 * H ^ 22
    - (86093442 : F[X]) * a3 * a4 * b3 * H ^ 25
    + (43046721 : F[X]) * a3 * b1 * H ^ 28
    - (30311820 : F[X]) * a4 ^ 6 * H ^ 18
    + (31177872 : F[X]) * a4 ^ 5 * b8 * H ^ 16
    - (31886460 : F[X]) * a4 ^ 4 * b6 * H ^ 19
    + (31886460 : F[X]) * a4 ^ 3 * b4 * H ^ 22
    - (28697814 : F[X]) * a4 ^ 2 * b2 * H ^ 25

/-- The chamber-free weight-thirty candidate obtained from the aligned
lambda-zero specialization of localClearedTwelfthDefect610 by the literal
substitution h^(2n) = H^n.  In doubled weights, H has weight two and
a_i,b_i have weight i, so every displayed monomial has weight sixty. -/
def alignedTwelfthDefect610 {F : Type*} [CommRing F]
    (H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) : F[X] :=
  alignedTwelfthDefectBlock1_610 H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
  alignedTwelfthDefectBlock2_610 H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
  alignedTwelfthDefectBlock3_610 H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
  alignedTwelfthDefectBlock4_610 H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
  alignedTwelfthDefectBlock5_610 H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1

set_option maxHeartbeats 160000000 in
set_option maxRecDepth 100000 in
/-- Exact square-root check for the chamber-free descent.  This is a
179-monomial identity, independently checked over `QQ` before the kernel
proof: the source expression has no odd square-root power. -/
theorem alignedTwelfthDefect610_squareRootSpecialization
    {F : Type*} [Field F] [CharZero F]
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) :
    localClearedTwelfthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 b1 0 =
      alignedTwelfthDefect610 (h ^ 2) a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
        b3 b2 b1 := by
  rw [localClearedTwelfthDefect610_of_lambda_zero]
  simp only [alignedTwelfthDefect610, alignedTwelfthDefectBlock1_610,
    alignedTwelfthDefectBlock2_610, alignedTwelfthDefectBlock3_610,
    alignedTwelfthDefectBlock4_610, alignedTwelfthDefectBlock5_610]
  ring

/-! ## Exact differential multiplier boundary -/

/-- Even integral row of integer `H`-weight `n`. -/
def alignedEvenWeightedRow610 {K : Type*} [CommRing K]
    (n : Nat) (H Z : K[X]) : K[X] :=
  H * Z.derivative - (n : K[X]) * Z * H.derivative

/-- Odd integral row of half-integral `H`-weight `n/2`. -/
def alignedOddWeightedRow610 {K : Type*} [CommRing K]
    (n : Nat) (H Z : K[X]) : K[X] :=
  (2 : K[X]) * H * Z.derivative - (n : K[X]) * Z * H.derivative

/-- Exact multiplier-certificate interface for the degree-`3` row.

The nine correction slots are precisely the already-consumed defects
`D,E,F,G,I,J,L,Omega,Lambda`, of weights
`15/2,10,25/2,15,35/2,20,45/2,25,55/2`.  Thus this structure records the
smallest missing CAS output: one leading multiplier and these nine
cofactors.  It contains no new axiom and does not assert that a certificate
exists. -/
structure AlignedTwelfthDefectMultiplier610 {K : Type*} [CommRing K]
    (H Theta raw D E F G I J L Omega Lambda : K[X]) where
  leading : K[X]
  cofactorD : K[X]
  cofactorE : K[X]
  cofactorF : K[X]
  cofactorG : K[X]
  cofactorI : K[X]
  cofactorJ : K[X]
  cofactorL : K[X]
  cofactorOmega : K[X]
  cofactorLambda : K[X]
  identity :
    leading * raw =
      alignedEvenWeightedRow610 30 H Theta +
      cofactorD * alignedOddWeightedRow610 15 H D +
      cofactorE * alignedEvenWeightedRow610 10 H E +
      cofactorF * alignedOddWeightedRow610 25 H F +
      cofactorG * alignedEvenWeightedRow610 15 H G +
      cofactorI * alignedOddWeightedRow610 35 H I +
      cofactorJ * alignedEvenWeightedRow610 20 H J +
      cofactorL * alignedOddWeightedRow610 45 H L +
      cofactorOmega * alignedEvenWeightedRow610 25 H Omega +
      cofactorLambda * alignedOddWeightedRow610 55 H Lambda

/-- Once the literal degree-`3` row and the nine prior weighted rows vanish,
an exact multiplier certificate reduces the candidate to its weight-thirty
weighted derivative. -/
theorem alignedTwelfthDefect610_weightedRow_of_multiplier
    {K : Type*} [CommRing K]
    {H Theta raw D E F G I J L Omega Lambda : K[X]}
    (hraw : raw = 0)
    (hD : alignedOddWeightedRow610 15 H D = 0)
    (hE : alignedEvenWeightedRow610 10 H E = 0)
    (hF : alignedOddWeightedRow610 25 H F = 0)
    (hG : alignedEvenWeightedRow610 15 H G = 0)
    (hI : alignedOddWeightedRow610 35 H I = 0)
    (hJ : alignedEvenWeightedRow610 20 H J = 0)
    (hL : alignedOddWeightedRow610 45 H L = 0)
    (hOmega : alignedEvenWeightedRow610 25 H Omega = 0)
    (hLambda : alignedOddWeightedRow610 55 H Lambda = 0)
    (hcertificate :
      AlignedTwelfthDefectMultiplier610 H Theta raw D E F G I J L Omega
        Lambda) :
    alignedEvenWeightedRow610 30 H Theta = 0 := by
  let leading : K[X] := hcertificate.leading
  let cD : K[X] := hcertificate.cofactorD
  let cE : K[X] := hcertificate.cofactorE
  let cF : K[X] := hcertificate.cofactorF
  let cG : K[X] := hcertificate.cofactorG
  let cI : K[X] := hcertificate.cofactorI
  let cJ : K[X] := hcertificate.cofactorJ
  let cL : K[X] := hcertificate.cofactorL
  let cOmega : K[X] := hcertificate.cofactorOmega
  let cLambda : K[X] := hcertificate.cofactorLambda
  have hid :
      leading * raw =
        alignedEvenWeightedRow610 30 H Theta +
        cD * alignedOddWeightedRow610 15 H D +
        cE * alignedEvenWeightedRow610 10 H E +
        cF * alignedOddWeightedRow610 25 H F +
        cG * alignedEvenWeightedRow610 15 H G +
        cI * alignedOddWeightedRow610 35 H I +
        cJ * alignedEvenWeightedRow610 20 H J +
        cL * alignedOddWeightedRow610 45 H L +
        cOmega * alignedEvenWeightedRow610 25 H Omega +
        cLambda * alignedOddWeightedRow610 55 H Lambda := by
    exact hcertificate.identity
  rw [hraw, hD, hE, hF, hG, hI, hJ, hL, hOmega, hLambda] at hid
  simp only [mul_zero, add_zero] at hid
  exact hid.symm

/-- Source-facing attachment of the conditional multiplier reduction to the
same literal degree-`3` row.  Earlier chamber/root packets are not unpacked:
callers supply their already-proved nine weighted-row equalities and retain
all witnesses unchanged. -/
theorem normalized610ScaleTwo_alignedTwelfthDefect_of_multiplier
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    {D E F G I J L Omega Lambda : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hD : alignedOddWeightedRow610 15 H D = 0)
    (hE : alignedEvenWeightedRow610 10 H E = 0)
    (hF : alignedOddWeightedRow610 25 H F = 0)
    (hG : alignedEvenWeightedRow610 15 H G = 0)
    (hI : alignedOddWeightedRow610 35 H I = 0)
    (hJ : alignedEvenWeightedRow610 20 H J = 0)
    (hL : alignedOddWeightedRow610 45 H L = 0)
    (hOmega : alignedEvenWeightedRow610 25 H Omega = 0)
    (hLambda : alignedOddWeightedRow610 55 H Lambda = 0)
    (hcertificate :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      AlignedTwelfthDefectMultiplier610 H
        (alignedTwelfthDefect610 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1))
        (alignedTwelfthJacobianRow610 p q) D E F G I J L Omega Lambda) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    alignedEvenWeightedRow610 30 H
      (alignedTwelfthDefect610 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
        (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
        (q.coeff 1)) = 0 := by
  dsimp only at hcertificate ⊢
  obtain ⟨_j, _hj, _hjac, hraw⟩ :=
    normalized610ScaleTwo_alignedTwelfthFace_literalPacket hsource haligned
  exact alignedTwelfthDefect610_weightedRow_of_multiplier hraw hD hE hF hG
    hI hJ hL hOmega hLambda hcertificate

/-- Generic chamber-free integration of the weight-thirty row. -/
theorem thirtiethPowerRelation_of_weightThirtyRow_610
    {K : Type*} [Field K] [CharZero K] {H Theta : K[X]}
    (hH : H ≠ 0)
    (hrow : alignedEvenWeightedRow610 30 H Theta = 0) :
    ∃ c : K, Theta = Polynomial.C c * H ^ 30 := by
  have hC30 : Polynomial.C (30 : K) = (30 : K[X]) :=
    Polynomial.C_eq_natCast 30
  have hW : Polynomial.wronskian Theta (H ^ 30) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      Theta * (Polynomial.C (30 : K) * H ^ (30 - 1) * H.derivative) -
          Theta.derivative * H ^ 30 =
          H ^ 29 *
            (Polynomial.C (30 : K) * Theta * H.derivative -
              H * Theta.derivative) := by ring
      _ = 0 := by
        rw [hC30]
        have hfac :
            (30 : K[X]) * Theta * H.derivative - H * Theta.derivative = 0 := by
          simp only [alignedEvenWeightedRow610] at hrow
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 30 hH) hW

#print axioms alignedTwelfthDefect610_squareRootSpecialization
#print axioms alignedTwelfthDefect610_weightedRow_of_multiplier
#print axioms normalized610ScaleTwo_alignedTwelfthDefect_of_multiplier
#print axioms thirtiethPowerRelation_of_weightThirtyRow_610

end Max11DegreeRoutes
