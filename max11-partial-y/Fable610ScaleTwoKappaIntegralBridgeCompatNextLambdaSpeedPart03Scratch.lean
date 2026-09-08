import Fable610ScaleTwoKappaIntegralBridgeCompatNextLambdaSpeedPart02Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaDepression610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 80000000 in
/-- Clearing the first integral `λ` of the degree-`3` row against `h⁶⁰`
on the ninth-power face. -/
theorem bridgeLambdaDefect_eq_cleared610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (258280326 : F) * h ^ 60 *
        bridgeLambdaResidual610
          (depressedL610 h (sexticDepressionR610 h a5) b9)
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
          (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
          (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
          (depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1)
          (depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
          (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7)
          (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6)
          (depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5)
          (depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (terminalDepressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) =
    (8107385 : F) * a5 ^ 12
    - (3979989 : F) * a5 ^ 11 * h ^ 5 * lambda
    - (80514720 : F) * a4 * a5 ^ 10 * h ^ 6
    - (12077208 : F) * a5 ^ 10 * b8 * h ^ 2
    + (84192075 : F) * a3 * a5 ^ 9 * h ^ 12
    + (45289530 : F) * a4 * a5 ^ 9 * h ^ 11 * lambda
    + (12193335 : F) * a5 ^ 9 * b7 * h ^ 8
    - (88609950 : F) * a2 * a5 ^ 8 * h ^ 18
    - (47031435 : F) * a3 * a5 ^ 8 * h ^ 17 * lambda
    + (261285750 : F) * a4 ^ 2 * a5 ^ 8 * h ^ 12
    + (125417160 : F) * a4 * a5 ^ 8 * b8 * h ^ 8
    - (12269070 : F) * a5 ^ 8 * b6 * h ^ 14
    + (94062870 : F) * a1 * a5 ^ 7 * h ^ 24
    + (49076280 : F) * a2 * a5 ^ 7 * h ^ 23 * lambda
    - (463498200 : F) * a3 * a4 * a5 ^ 7 * h ^ 18
    - (130870080 : F) * a3 * a5 ^ 7 * b8 * h ^ 14
    - (188125740 : F) * a4 ^ 2 * a5 ^ 7 * h ^ 17 * lambda
    - (114511320 : F) * a4 * a5 ^ 7 * b7 * h ^ 14
    + (12269070 : F) * a5 ^ 7 * b5 * h ^ 20
    - (101039400 : F) * a0 * a5 ^ 6 * h ^ 30
    - (51530094 : F) * a1 * a5 ^ 6 * h ^ 29 * lambda
    + (400789620 : F) * a2 * a4 * a5 ^ 6 * h ^ 24
    + (137413584 : F) * a2 * a5 ^ 6 * b8 * h ^ 20
    + (200394810 : F) * a3 ^ 2 * a5 ^ 6 * h ^ 24
    + (343533960 : F) * a3 * a4 * a5 ^ 6 * h ^ 23 * lambda
    + (120236886 : F) * a3 * a5 ^ 6 * b7 * h ^ 20
    - (254469600 : F) * a4 ^ 3 * a5 ^ 6 * h ^ 18
    - (458045280 : F) * a4 ^ 2 * a5 ^ 6 * b8 * h ^ 14
    + (103060188 : F) * a4 * a5 ^ 6 * b6 * h ^ 20
    - (12124728 : F) * a5 ^ 6 * b4 * h ^ 26
    + (54561276 : F) * a0 * a5 ^ 5 * h ^ 35 * lambda
    - (333430020 : F) * a1 * a4 * a5 ^ 5 * h ^ 30
    - (145496736 : F) * a1 * a5 ^ 5 * b8 * h ^ 26
    - (333430020 : F) * a2 * a3 * a5 ^ 5 * h ^ 30
    - (309180564 : F) * a2 * a4 * a5 ^ 5 * h ^ 29 * lambda
    - (127309644 : F) * a2 * a5 ^ 5 * b7 * h ^ 26
    - (154590282 : F) * a3 ^ 2 * a5 ^ 5 * h ^ 29 * lambda
    + (429417450 : F) * a3 * a4 ^ 2 * a5 ^ 5 * h ^ 24
    + (824481504 : F) * a3 * a4 * a5 ^ 5 * b8 * h ^ 20
    - (109122552 : F) * a3 * a5 ^ 5 * b6 * h ^ 26
    + (343533960 : F) * a4 ^ 3 * a5 ^ 5 * h ^ 23 * lambda
    + (360710658 : F) * a4 ^ 2 * a5 ^ 5 * b7 * h ^ 20
    - (90935460 : F) * a4 * a5 ^ 5 * b5 * h ^ 26
    + (11691702 : F) * a5 ^ 5 * b3 * h ^ 32
    + (259815600 : F) * a0 * a4 * a5 ^ 4 * h ^ 36
    + (155889360 : F) * a0 * a5 ^ 4 * b8 * h ^ 32
    + (259815600 : F) * a1 * a3 * a5 ^ 4 * h ^ 36
    + (272806380 : F) * a1 * a4 * a5 ^ 4 * h ^ 35 * lambda
    + (136403190 : F) * a1 * a5 ^ 4 * b7 * h ^ 32
    + (129907800 : F) * a2 ^ 2 * a5 ^ 4 * h ^ 36
    + (272806380 : F) * a2 * a3 * a5 ^ 4 * h ^ 35 * lambda
    - (151559100 : F) * a2 * a4 ^ 2 * a5 ^ 4 * h ^ 30
    - (727483680 : F) * a2 * a4 * a5 ^ 4 * b8 * h ^ 26
    + (116917020 : F) * a2 * a5 ^ 4 * b6 * h ^ 32
    - (151559100 : F) * a3 ^ 2 * a4 * a5 ^ 4 * h ^ 30
    - (363741840 : F) * a3 ^ 2 * a5 ^ 4 * b8 * h ^ 26
    - (772951410 : F) * a3 * a4 ^ 2 * a5 ^ 4 * h ^ 29 * lambda
    - (636548220 : F) * a3 * a4 * a5 ^ 4 * b7 * h ^ 26
    + (97430850 : F) * a3 * a5 ^ 4 * b5 * h ^ 32
    - (143139150 : F) * a4 ^ 4 * a5 ^ 4 * h ^ 24
    + (687067920 : F) * a4 ^ 3 * a5 ^ 4 * b8 * h ^ 20
    - (272806380 : F) * a4 ^ 2 * a5 ^ 4 * b6 * h ^ 26
    + (77944680 : F) * a4 * a5 ^ 4 * b4 * h ^ 32
    - (10628820 : F) * a5 ^ 4 * b2 * h ^ 38
    - (177147000 : F) * a0 * a3 * a5 ^ 3 * h ^ 42
    - (233834040 : F) * a0 * a4 * a5 ^ 3 * h ^ 41 * lambda
    - (148803480 : F) * a0 * a5 ^ 3 * b7 * h ^ 38
    - (177147000 : F) * a1 * a2 * a5 ^ 3 * h ^ 42
    - (233834040 : F) * a1 * a3 * a5 ^ 3 * h ^ 41 * lambda
    - (64953900 : F) * a1 * a4 ^ 2 * a5 ^ 3 * h ^ 36
    + (623557440 : F) * a1 * a4 * a5 ^ 3 * b8 * h ^ 32
    - (127545840 : F) * a1 * a5 ^ 3 * b6 * h ^ 38
    - (116917020 : F) * a2 ^ 2 * a5 ^ 3 * h ^ 41 * lambda
    - (129907800 : F) * a2 * a3 * a4 * a5 ^ 3 * h ^ 36
    + (623557440 : F) * a2 * a3 * a5 ^ 3 * b8 * h ^ 32
    + (545612760 : F) * a2 * a4 ^ 2 * a5 ^ 3 * h ^ 35 * lambda
    + (545612760 : F) * a2 * a4 * a5 ^ 3 * b7 * h ^ 32
    - (106288200 : F) * a2 * a5 ^ 3 * b5 * h ^ 38
    - (21651300 : F) * a3 ^ 3 * a5 ^ 3 * h ^ 36
    + (545612760 : F) * a3 ^ 2 * a4 * a5 ^ 3 * h ^ 35 * lambda
    + (272806380 : F) * a3 ^ 2 * a5 ^ 3 * b7 * h ^ 32
    + (707275800 : F) * a3 * a4 ^ 3 * a5 ^ 3 * h ^ 30
    - (1454967360 : F) * a3 * a4 ^ 2 * a5 ^ 3 * b8 * h ^ 26
    + (467668080 : F) * a3 * a4 * a5 ^ 3 * b6 * h ^ 32
    - (85030560 : F) * a3 * a5 ^ 3 * b4 * h ^ 38
    - (257650470 : F) * a4 ^ 4 * a5 ^ 3 * h ^ 29 * lambda
    - (424365480 : F) * a4 ^ 3 * a5 ^ 3 * b7 * h ^ 26
    + (194861700 : F) * a4 ^ 2 * a5 ^ 3 * b5 * h ^ 32
    - (63772920 : F) * a4 * a5 ^ 3 * b3 * h ^ 38
    + (7971615 : F) * a5 ^ 3 * b1 * h ^ 44
    + (79716150 : F) * a0 * a2 * a5 ^ 2 * h ^ 48
    + (191318760 : F) * a0 * a3 * a5 ^ 2 * h ^ 47 * lambda
    + (212576400 : F) * a0 * a4 ^ 2 * a5 ^ 2 * h ^ 42
    - (510183360 : F) * a0 * a4 * a5 ^ 2 * b8 * h ^ 38
    + (143489070 : F) * a0 * a5 ^ 2 * b6 * h ^ 44
    + (39858075 : F) * a1 ^ 2 * a5 ^ 2 * h ^ 48
    + (191318760 : F) * a1 * a2 * a5 ^ 2 * h ^ 47 * lambda
    + (425152800 : F) * a1 * a3 * a4 * a5 ^ 2 * h ^ 42
    - (510183360 : F) * a1 * a3 * a5 ^ 2 * b8 * h ^ 38
    - (350751060 : F) * a1 * a4 ^ 2 * a5 ^ 2 * h ^ 41 * lambda
    - (446410440 : F) * a1 * a4 * a5 ^ 2 * b7 * h ^ 38
    + (119574225 : F) * a1 * a5 ^ 2 * b5 * h ^ 44
    + (212576400 : F) * a2 ^ 2 * a4 * a5 ^ 2 * h ^ 42
    - (255091680 : F) * a2 ^ 2 * a5 ^ 2 * b8 * h ^ 38
    + (212576400 : F) * a2 * a3 ^ 2 * a5 ^ 2 * h ^ 42
    - (701502120 : F) * a2 * a3 * a4 * a5 ^ 2 * h ^ 41 * lambda
    - (446410440 : F) * a2 * a3 * a5 ^ 2 * b7 * h ^ 38
    - (649539000 : F) * a2 * a4 ^ 3 * a5 ^ 2 * h ^ 36
    + (935336160 : F) * a2 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 32
    - (382637520 : F) * a2 * a4 * a5 ^ 2 * b6 * h ^ 38
    + (95659380 : F) * a2 * a5 ^ 2 * b4 * h ^ 44
    - (116917020 : F) * a3 ^ 3 * a5 ^ 2 * h ^ 41 * lambda
    - (974308500 : F) * a3 ^ 2 * a4 ^ 2 * a5 ^ 2 * h ^ 36
    + (935336160 : F) * a3 ^ 2 * a4 * a5 ^ 2 * b8 * h ^ 32
    - (191318760 : F) * a3 ^ 2 * a5 ^ 2 * b6 * h ^ 38
    + (545612760 : F) * a3 * a4 ^ 3 * a5 ^ 2 * h ^ 35 * lambda
    + (818419140 : F) * a3 * a4 ^ 2 * a5 ^ 2 * b7 * h ^ 32
    - (318864600 : F) * a3 * a4 * a5 ^ 2 * b5 * h ^ 38
    + (71744535 : F) * a3 * a5 ^ 2 * b3 * h ^ 44
    + (242494560 : F) * a4 ^ 5 * a5 ^ 2 * h ^ 30
    - (363741840 : F) * a4 ^ 4 * a5 ^ 2 * b8 * h ^ 26
    + (233834040 : F) * a4 ^ 3 * a5 ^ 2 * b6 * h ^ 32
    - (127545840 : F) * a4 ^ 2 * a5 ^ 2 * b4 * h ^ 38
    + (47829690 : F) * a4 * a5 ^ 2 * b2 * h ^ 44
    + (47829690 : F) * a0 * a1 * a5 * h ^ 54
    - (143489070 : F) * a0 * a2 * a5 * h ^ 53 * lambda
    - (558013050 : F) * a0 * a3 * a4 * a5 * h ^ 48
    + (382637520 : F) * a0 * a3 * a5 * b8 * h ^ 44
    + (191318760 : F) * a0 * a4 ^ 2 * a5 * h ^ 47 * lambda
    + (334807830 : F) * a0 * a4 * a5 * b7 * h ^ 44
    - (143489070 : F) * a0 * a5 * b5 * h ^ 50
    - (71744535 : F) * a1 ^ 2 * a5 * h ^ 53 * lambda
    - (558013050 : F) * a1 * a2 * a4 * a5 * h ^ 48
    + (382637520 : F) * a1 * a2 * a5 * b8 * h ^ 44
    - (279006525 : F) * a1 * a3 ^ 2 * a5 * h ^ 48
    + (382637520 : F) * a1 * a3 * a4 * a5 * h ^ 47 * lambda
    + (334807830 : F) * a1 * a3 * a5 * b7 * h ^ 44
    + (460582200 : F) * a1 * a4 ^ 3 * a5 * h ^ 42
    - (510183360 : F) * a1 * a4 ^ 2 * a5 * b8 * h ^ 38
    + (286978140 : F) * a1 * a4 * a5 * b6 * h ^ 44
    - (114791256 : F) * a1 * a5 * b4 * h ^ 50
    - (279006525 : F) * a2 ^ 2 * a3 * a5 * h ^ 48
    + (191318760 : F) * a2 ^ 2 * a4 * a5 * h ^ 47 * lambda
    + (167403915 : F) * a2 ^ 2 * a5 * b7 * h ^ 44
    + (191318760 : F) * a2 * a3 ^ 2 * a5 * h ^ 47 * lambda
    + (1381746600 : F) * a2 * a3 * a4 ^ 2 * a5 * h ^ 42
    - (1020366720 : F) * a2 * a3 * a4 * a5 * b8 * h ^ 38
    + (286978140 : F) * a2 * a3 * a5 * b6 * h ^ 44
    - (233834040 : F) * a2 * a4 ^ 3 * a5 * h ^ 41 * lambda
    - (446410440 : F) * a2 * a4 ^ 2 * a5 * b7 * h ^ 38
    + (239148450 : F) * a2 * a4 * a5 * b5 * h ^ 44
    - (86093442 : F) * a2 * a5 * b3 * h ^ 50
    + (460582200 : F) * a3 ^ 3 * a4 * a5 * h ^ 42
    - (170061120 : F) * a3 ^ 3 * a5 * b8 * h ^ 38
    - (350751060 : F) * a3 ^ 2 * a4 ^ 2 * a5 * h ^ 41 * lambda
    - (446410440 : F) * a3 ^ 2 * a4 * a5 * b7 * h ^ 38
    + (119574225 : F) * a3 ^ 2 * a5 * b5 * h ^ 44
    - (617062050 : F) * a3 * a4 ^ 4 * a5 * h ^ 36
    + (623557440 : F) * a3 * a4 ^ 3 * a5 * b8 * h ^ 32
    - (382637520 : F) * a3 * a4 ^ 2 * a5 * b6 * h ^ 38
    + (191318760 : F) * a3 * a4 * a5 * b4 * h ^ 44
    - (57395628 : F) * a3 * a5 * b2 * h ^ 50
    + (54561276 : F) * a4 ^ 5 * a5 * h ^ 35 * lambda
    + (136403190 : F) * a4 ^ 4 * a5 * b7 * h ^ 32
    - (106288200 : F) * a4 ^ 3 * a5 * b5 * h ^ 38
    + (71744535 : F) * a4 ^ 2 * a5 * b3 * h ^ 44
    - (28697814 : F) * a4 * a5 * b1 * h ^ 50
    - (143489070 : F) * a0 ^ 2 * h ^ 60
    + (86093442 : F) * a0 * a1 * h ^ 59 * lambda
    + (478296900 : F) * a0 * a2 * a4 * h ^ 54
    - (229582512 : F) * a0 * a2 * b8 * h ^ 50
    + (239148450 : F) * a0 * a3 ^ 2 * h ^ 54
    - (143489070 : F) * a0 * a3 * a4 * h ^ 53 * lambda
    - (200884698 : F) * a0 * a3 * b7 * h ^ 50
    - (212576400 : F) * a0 * a4 ^ 3 * h ^ 48
    + (191318760 : F) * a0 * a4 ^ 2 * b8 * h ^ 44
    - (172186884 : F) * a0 * a4 * b6 * h ^ 50
    + (172186884 : F) * a0 * b4 * h ^ 56
    + (239148450 : F) * a1 ^ 2 * a4 * h ^ 54
    - (114791256 : F) * a1 ^ 2 * b8 * h ^ 50
    + (478296900 : F) * a1 * a2 * a3 * h ^ 54
    - (143489070 : F) * a1 * a2 * a4 * h ^ 53 * lambda
    - (200884698 : F) * a1 * a2 * b7 * h ^ 50
    - (71744535 : F) * a1 * a3 ^ 2 * h ^ 53 * lambda
    - (637729200 : F) * a1 * a3 * a4 ^ 2 * h ^ 48
    + (382637520 : F) * a1 * a3 * a4 * b8 * h ^ 44
    - (172186884 : F) * a1 * a3 * b6 * h ^ 50
    + (63772920 : F) * a1 * a4 ^ 3 * h ^ 47 * lambda
    + (167403915 : F) * a1 * a4 ^ 2 * b7 * h ^ 44
    - (143489070 : F) * a1 * a4 * b5 * h ^ 50
    + (129140163 : F) * a1 * b3 * h ^ 56
    + (79716150 : F) * a2 ^ 3 * h ^ 54
    - (71744535 : F) * a2 ^ 2 * a3 * h ^ 53 * lambda
    - (318864600 : F) * a2 ^ 2 * a4 ^ 2 * h ^ 48
    + (191318760 : F) * a2 ^ 2 * a4 * b8 * h ^ 44
    - (86093442 : F) * a2 ^ 2 * b6 * h ^ 50
    - (637729200 : F) * a2 * a3 ^ 2 * a4 * h ^ 48
    + (191318760 : F) * a2 * a3 ^ 2 * b8 * h ^ 44
    + (191318760 : F) * a2 * a3 * a4 ^ 2 * h ^ 47 * lambda
    + (334807830 : F) * a2 * a3 * a4 * b7 * h ^ 44
    - (143489070 : F) * a2 * a3 * b5 * h ^ 50
    + (194861700 : F) * a2 * a4 ^ 4 * h ^ 42
    - (170061120 : F) * a2 * a4 ^ 3 * b8 * h ^ 38
    + (143489070 : F) * a2 * a4 ^ 2 * b6 * h ^ 44
    - (114791256 : F) * a2 * a4 * b4 * h ^ 50
    + (86093442 : F) * a2 * b2 * h ^ 56
    - (53144100 : F) * a3 ^ 4 * h ^ 48
    + (63772920 : F) * a3 ^ 3 * a4 * h ^ 47 * lambda
    + (55801305 : F) * a3 ^ 3 * b7 * h ^ 44
    + (389723400 : F) * a3 ^ 2 * a4 ^ 3 * h ^ 42
    - (255091680 : F) * a3 ^ 2 * a4 ^ 2 * b8 * h ^ 38
    + (143489070 : F) * a3 ^ 2 * a4 * b6 * h ^ 44
    - (57395628 : F) * a3 ^ 2 * b4 * h ^ 50
    - (58458510 : F) * a3 * a4 ^ 4 * h ^ 41 * lambda
    - (148803480 : F) * a3 * a4 ^ 3 * b7 * h ^ 38
    + (119574225 : F) * a3 * a4 ^ 2 * b5 * h ^ 44
    - (86093442 : F) * a3 * a4 * b3 * h ^ 50
    + (43046721 : F) * a3 * b1 * h ^ 56
    - (30311820 : F) * a4 ^ 6 * h ^ 36
    + (31177872 : F) * a4 ^ 5 * b8 * h ^ 32
    - (31886460 : F) * a4 ^ 4 * b6 * h ^ 38
    + (31886460 : F) * a4 ^ 3 * b4 * h ^ 44
    - (28697814 : F) * a4 ^ 2 * b2 * h ^ 50 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h5 : (5 : F) ≠ 0 := by norm_num
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h12 : (12 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h18 : (18 : F) ≠ 0 := by norm_num
  have h27 : (27 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h36 : (36 : F) ≠ 0 := by norm_num
  have h54 : (54 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h72 : (72 : F) ≠ 0 := by norm_num
  have h81 : (81 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h216 : (216 : F) ≠ 0 := by norm_num
  have h243 : (243 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h324 : (324 : F) ≠ 0 := by norm_num
  have h432 : (432 : F) ≠ 0 := by norm_num
  have h648 : (648 : F) ≠ 0 := by norm_num
  have h729 : (729 : F) ≠ 0 := by norm_num
  have h1296 : (1296 : F) ≠ 0 := by norm_num
  have h7776 : (7776 : F) ≠ 0 := by norm_num
  have h11664 : (11664 : F) ≠ 0 := by norm_num
  have h31104 : (31104 : F) ≠ 0 := by norm_num
  have h46656 : (46656 : F) ≠ 0 := by norm_num
  have h93312 : (93312 : F) ≠ 0 := by norm_num
  have h186624 : (186624 : F) ≠ 0 := by norm_num
  have h5038848 : (5038848 : F) ≠ 0 := by norm_num
  have h6561 : (6561 : F) ≠ 0 := by norm_num
  have h258280326 : (258280326 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hh25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hh30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh40 : h ^ 40 ≠ 0 := pow_ne_zero 40 hh
  have hh45 : h ^ 45 ≠ 0 := pow_ne_zero 45 hh
  have hh50 : h ^ 50 ≠ 0 := pow_ne_zero 50 hh
  have hh55 : h ^ 55 ≠ 0 := pow_ne_zero 55 hh
  have hh60 : h ^ 60 ≠ 0 := pow_ne_zero 60 hh
  have hL :
      depressedL610 h (sexticDepressionR610 h a5) b9 = -lambda / 3 :=
    depressedL610_eq_of_ninthPower h a5 b9 lambda hh hN
  have hA :
      depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
        (12 * a4 * h ^ 6 - 5 * a5 ^ 2) / (12 * h ^ 10) :=
    depressedA610_eq_cleared h a5 a4 hh
  have hB :
      depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 =
        (54 * a3 * h ^ 12 - 36 * a4 * a5 * h ^ 6 + 10 * a5 ^ 3) /
          (54 * h ^ 15) :=
    depressedB610_eq_cleared h a5 a4 a3 hh
  have hC :
      depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 =
        (144 * a2 * h ^ 18 - 72 * a3 * a5 * h ^ 12 +
            24 * a4 * a5 ^ 2 * h ^ 6 - 5 * a5 ^ 4) /
          (144 * h ^ 20) :=
    depressedC610_eq_cleared h a5 a4 a3 a2 hh
  have hD0 :
      depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 =
        (324 * a1 * h ^ 24 - 108 * a2 * a5 * h ^ 18 +
            27 * a3 * a5 ^ 2 * h ^ 12 - 6 * a4 * a5 ^ 3 * h ^ 6 +
            a5 ^ 5) /
          (324 * h ^ 25) :=
    depressedD610_eq_cleared h a5 a4 a3 a2 a1 hh
  have hE0 :
      depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 a0 =
        (46656 * a0 * h ^ 30 - 7776 * a1 * a5 * h ^ 24 +
            1296 * a2 * a5 ^ 2 * h ^ 18 - 216 * a3 * a5 ^ 3 * h ^ 12 +
            36 * a4 * a5 ^ 4 * h ^ 6 - 5 * a5 ^ 6) /
          (46656 * h ^ 30) :=
    depressedE610_eq_cleared h a5 a4 a3 a2 a1 a0 hh
  have hS :
      depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 =
        (28 * a5 ^ 5 - 7 * lambda * a5 ^ 4 * h ^ 5 -
            56 * a5 ^ 3 * b8 * h ^ 2 + 126 * a5 ^ 2 * b7 * h ^ 8 -
            216 * a5 * b6 * h ^ 14 + 216 * b5 * h ^ 20) /
          (216 * h ^ 25) :=
    depressedS610_eq_cleared h a5 b9 b8 b7 b6 b5 lambda hh hN
  have hT :
      depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 =
        (-175 * a5 ^ 6 + 42 * lambda * a5 ^ 5 * h ^ 5 +
            420 * a5 ^ 4 * b8 * h ^ 2 - 1260 * a5 ^ 3 * b7 * h ^ 8 +
            3240 * a5 ^ 2 * b6 * h ^ 14 - 6480 * a5 * b5 * h ^ 20 +
            7776 * b4 * h ^ 26) /
          (7776 * h ^ 30) :=
    depressedT610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 lambda hh hN
  have hU :
      depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 =
        (30 * a5 ^ 7 - 7 * lambda * a5 ^ 6 * h ^ 5 -
            84 * a5 ^ 5 * b8 * h ^ 2 + 315 * a5 ^ 4 * b7 * h ^ 8 -
            1080 * a5 ^ 3 * b6 * h ^ 14 + 3240 * a5 ^ 2 * b5 * h ^ 20 -
            7776 * a5 * b4 * h ^ 26 + 11664 * b3 * h ^ 32) /
          (11664 * h ^ 35) :=
    depressedU610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  have hV :
      depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 b2 =
        (-35 * a5 ^ 8 + 8 * lambda * a5 ^ 7 * h ^ 5 +
            112 * a5 ^ 6 * b8 * h ^ 2 - 504 * a5 ^ 5 * b7 * h ^ 8 +
            2160 * a5 ^ 4 * b6 * h ^ 14 - 8640 * a5 ^ 3 * b5 * h ^ 20 +
            31104 * a5 ^ 2 * b4 * h ^ 26 - 93312 * a5 * b3 * h ^ 32 +
            186624 * b2 * h ^ 38) /
          (186624 * h ^ 40) :=
    depressedV610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh hN
  have hW :
      terminalDepressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 b2 b1 =
        (40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
            144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
            3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
            93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
            1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44) /
          (5038848 * h ^ 45) :=
    terminalDepressedW610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda hh hN
  have hP :
      depressedP610 h (sexticDepressionR610 h a5) b9 b8 =
        (-5 * a5 ^ 2 + 2 * lambda * a5 * h ^ 5 + 4 * b8 * h ^ 2) /
          (4 * h ^ 10) :=
    depressedP610_eq_cleared_ninthPower h a5 b9 b8 lambda hh hN
  have hQ :
      depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7 =
        (10 * a5 ^ 3 - 3 * lambda * a5 ^ 2 * h ^ 5 -
            12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8) /
          (9 * h ^ 15) :=
    depressedQ610_eq_cleared h a5 b9 b8 b7 lambda hh hN
  have hR :
      depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 =
        (-210 * a5 ^ 4 + 56 * lambda * a5 ^ 3 * h ^ 5 +
            336 * a5 ^ 2 * b8 * h ^ 2 - 504 * a5 * b7 * h ^ 8 +
            432 * b6 * h ^ 14) /
          (432 * h ^ 20) :=
    depressedR610_eq_cleared h a5 b9 b8 b7 b6 lambda hh hN
  rw [hL, hA, hB, hC, hD0, hE0, hP, hQ, hR, hS, hT, hU, hV, hW,
    speedBridgeLambdaResidual610Scaled60_eq h hh]
  simp only [speedBridgeLambdaResidual610Scaled60]
  ring

end BridgeLambdaDepression610

end Max11DegreeRoutes
