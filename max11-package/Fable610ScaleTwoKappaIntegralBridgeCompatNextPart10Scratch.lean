import LowScale46SourceBridge

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaJet610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 64000000 in
/-- Tail of the merged-jet cleared `λ` defect above order `h⁵⁵`. -/
def bridgeLambdaDeepTail610
    (hh w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 lam : R) : R := by
  refine ?_ + (54561276 : R) * hh ^ 5 * lam * w1 ^ 5 * p0
  refine ?_ - (3979989 : R) * hh ^ 5 * lam * w1 ^ 11
  refine ?_ - (143489070 : R) * hh ^ 5 * p0 ^ 2
  refine ?_ - (101039400 : R) * hh ^ 5 * w1 ^ 6 * p0
  refine ?_ + (8107385 : R) * hh ^ 5 * w1 ^ 12
  refine ?_ + (86093442 : R) * hh ^ 4 * lam * p1 * p0
  refine ?_ + (191318760 : R) * hh ^ 4 * lam * w1 ^ 2 * p32 * p0
  refine ?_ - (233834040 : R) * hh ^ 4 * lam * w1 ^ 3 * a41 * p0
  refine ?_ - (51530094 : R) * hh ^ 4 * lam * w1 ^ 6 * p1
  refine ?_ - (47031435 : R) * hh ^ 4 * lam * w1 ^ 8 * p32
  refine ?_ + (45289530 : R) * hh ^ 4 * lam * w1 ^ 9 * a41
  refine ?_ + (47829690 : R) * hh ^ 4 * w1 * p1 * p0
  refine ?_ + (7971615 : R) * hh ^ 4 * w1 ^ 3 * q1
  refine ?_ - (148803480 : R) * hh ^ 4 * w1 ^ 3 * u2 * p0
  refine ?_ - (177147000 : R) * hh ^ 4 * w1 ^ 3 * p32 * p0
  refine ?_ + (155889360 : R) * hh ^ 4 * w1 ^ 4 * s1 * p0
  refine ?_ + (259815600 : R) * hh ^ 4 * w1 ^ 4 * a41 * p0
  refine ?_ + (94062870 : R) * hh ^ 4 * w1 ^ 7 * p1
  refine ?_ + (12193335 : R) * hh ^ 4 * w1 ^ 9 * u2
  refine ?_ + (84192075 : R) * hh ^ 4 * w1 ^ 9 * p32
  refine ?_ - (12077208 : R) * hh ^ 4 * w1 ^ 10 * s1
  refine ?_ - (80514720 : R) * hh ^ 4 * w1 ^ 10 * a41
  refine ?_ - (143489070 : R) * hh ^ 3 * lam * a41 * p32 * p0
  refine ?_ - (71744535 : R) * hh ^ 3 * lam * w1 * p1 ^ 2
  refine ?_ - (143489070 : R) * hh ^ 3 * lam * w1 * p2 * p0
  refine ?_ + (191318760 : R) * hh ^ 3 * lam * w1 * a41 ^ 2 * p0
  refine ?_ - (233834040 : R) * hh ^ 3 * lam * w1 ^ 3 * p32 * p1
  refine ?_ + (272806380 : R) * hh ^ 3 * lam * w1 ^ 4 * a41 * p1
  refine ?_ - (154590282 : R) * hh ^ 3 * lam * w1 ^ 5 * p32 ^ 2
  refine ?_ + (343533960 : R) * hh ^ 3 * lam * w1 ^ 6 * a41 * p32
  refine ?_ + (49076280 : R) * hh ^ 3 * lam * w1 ^ 7 * p2
  refine ?_ - (188125740 : R) * hh ^ 3 * lam * w1 ^ 7 * a41 ^ 2
  refine ?_ + (43046721 : R) * hh ^ 3 * p32 * q1
  refine ?_ - (200884698 : R) * hh ^ 3 * p32 * u2 * p0
  refine ?_ + (239148450 : R) * hh ^ 3 * p32 ^ 2 * p0
  refine ?_ - (143489070 : R) * hh ^ 3 * w1 * q53 * p0
  refine ?_ + (382637520 : R) * hh ^ 3 * w1 * p32 * s1 * p0
  refine ?_ - (28697814 : R) * hh ^ 3 * w1 * a41 * q1
  refine ?_ + (334807830 : R) * hh ^ 3 * w1 * a41 * u2 * p0
  refine ?_ - (558013050 : R) * hh ^ 3 * w1 * a41 * p32 * p0
  refine ?_ + (39858075 : R) * hh ^ 3 * w1 ^ 2 * p1 ^ 2
  refine ?_ + (79716150 : R) * hh ^ 3 * w1 ^ 2 * p2 * p0
  refine ?_ + (143489070 : R) * hh ^ 3 * w1 ^ 2 * b62 * p0
  refine ?_ - (510183360 : R) * hh ^ 3 * w1 ^ 2 * a41 * s1 * p0
  refine ?_ + (212576400 : R) * hh ^ 3 * w1 ^ 2 * a41 ^ 2 * p0
  refine ?_ - (10628820 : R) * hh ^ 3 * w1 ^ 4 * q2
  refine ?_ + (136403190 : R) * hh ^ 3 * w1 ^ 4 * u2 * p1
  refine ?_ + (259815600 : R) * hh ^ 3 * w1 ^ 4 * p32 * p1
  refine ?_ - (145496736 : R) * hh ^ 3 * w1 ^ 5 * s1 * p1
  refine ?_ - (333430020 : R) * hh ^ 3 * w1 ^ 5 * a41 * p1
  refine ?_ + (120236886 : R) * hh ^ 3 * w1 ^ 6 * p32 * u2
  refine ?_ + (200394810 : R) * hh ^ 3 * w1 ^ 6 * p32 ^ 2
  refine ?_ + (12269070 : R) * hh ^ 3 * w1 ^ 7 * q53
  refine ?_ - (130870080 : R) * hh ^ 3 * w1 ^ 7 * p32 * s1
  refine ?_ - (114511320 : R) * hh ^ 3 * w1 ^ 7 * a41 * u2
  refine ?_ - (463498200 : R) * hh ^ 3 * w1 ^ 7 * a41 * p32
  refine ?_ - (88609950 : R) * hh ^ 3 * w1 ^ 8 * p2
  refine ?_ - (12269070 : R) * hh ^ 3 * w1 ^ 8 * b62
  refine ?_ + (125417160 : R) * hh ^ 3 * w1 ^ 8 * a41 * s1
  refine ?_ + (261285750 : R) * hh ^ 3 * w1 ^ 8 * a41 ^ 2
  refine ?_ - (71744535 : R) * hh ^ 2 * lam * p32 ^ 2 * p1
  refine ?_ + (382637520 : R) * hh ^ 2 * lam * w1 * a41 * p32 * p1
  refine ?_ + (191318760 : R) * hh ^ 2 * lam * w1 ^ 2 * p2 * p1
  refine ?_ - (116917020 : R) * hh ^ 2 * lam * w1 ^ 2 * p32 ^ 3
  refine ?_ - (350751060 : R) * hh ^ 2 * lam * w1 ^ 2 * a41 ^ 2 * p1
  refine ?_ + (545612760 : R) * hh ^ 2 * lam * w1 ^ 3 * a41 * p32 ^ 2
  refine ?_ + (272806380 : R) * hh ^ 2 * lam * w1 ^ 4 * p32 * p2
  refine ?_ - (772951410 : R) * hh ^ 2 * lam * w1 ^ 4 * a41 ^ 2 * p32
  refine ?_ - (309180564 : R) * hh ^ 2 * lam * w1 ^ 5 * a41 * p2
  refine ?_ + (343533960 : R) * hh ^ 2 * lam * w1 ^ 5 * a41 ^ 3
  refine ?_ + (172186884 : R) * hh ^ 2 * p0 * q41
  refine ?_ - (114791256 : R) * hh ^ 2 * s1 * p1 ^ 2
  refine ?_ - (229582512 : R) * hh ^ 2 * s1 * p2 * p0
  refine ?_ + (239148450 : R) * hh ^ 2 * a41 * p1 ^ 2
  refine ?_ + (478296900 : R) * hh ^ 2 * a41 * p2 * p0
  refine ?_ - (172186884 : R) * hh ^ 2 * a41 * b62 * p0
  refine ?_ + (191318760 : R) * hh ^ 2 * a41 ^ 2 * s1 * p0
  refine ?_ - (212576400 : R) * hh ^ 2 * a41 ^ 3 * p0
  refine ?_ - (57395628 : R) * hh ^ 2 * w1 * p32 * q2
  refine ?_ + (334807830 : R) * hh ^ 2 * w1 * p32 * u2 * p1
  refine ?_ - (279006525 : R) * hh ^ 2 * w1 * p32 ^ 2 * p1
  refine ?_ + (119574225 : R) * hh ^ 2 * w1 ^ 2 * q53 * p1
  refine ?_ - (510183360 : R) * hh ^ 2 * w1 ^ 2 * p32 * s1 * p1
  refine ?_ + (47829690 : R) * hh ^ 2 * w1 ^ 2 * a41 * q2
  refine ?_ - (446410440 : R) * hh ^ 2 * w1 ^ 2 * a41 * u2 * p1
  refine ?_ + (425152800 : R) * hh ^ 2 * w1 ^ 2 * a41 * p32 * p1
  refine ?_ - (177147000 : R) * hh ^ 2 * w1 ^ 3 * p2 * p1
  refine ?_ - (127545840 : R) * hh ^ 2 * w1 ^ 3 * b62 * p1
  refine ?_ + (272806380 : R) * hh ^ 2 * w1 ^ 3 * p32 ^ 2 * u2
  refine ?_ - (21651300 : R) * hh ^ 2 * w1 ^ 3 * p32 ^ 3
  refine ?_ + (623557440 : R) * hh ^ 2 * w1 ^ 3 * a41 * s1 * p1
  refine ?_ - (64953900 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 2 * p1
  refine ?_ + (97430850 : R) * hh ^ 2 * w1 ^ 4 * p32 * q53
  refine ?_ - (363741840 : R) * hh ^ 2 * w1 ^ 4 * p32 ^ 2 * s1
  refine ?_ - (636548220 : R) * hh ^ 2 * w1 ^ 4 * a41 * p32 * u2
  refine ?_ - (151559100 : R) * hh ^ 2 * w1 ^ 4 * a41 * p32 ^ 2
  refine ?_ + (11691702 : R) * hh ^ 2 * w1 ^ 5 * q3
  refine ?_ - (127309644 : R) * hh ^ 2 * w1 ^ 5 * u2 * p2
  refine ?_ - (333430020 : R) * hh ^ 2 * w1 ^ 5 * p32 * p2
  refine ?_ - (109122552 : R) * hh ^ 2 * w1 ^ 5 * p32 * b62
  refine ?_ - (90935460 : R) * hh ^ 2 * w1 ^ 5 * a41 * q53
  refine ?_ + (824481504 : R) * hh ^ 2 * w1 ^ 5 * a41 * p32 * s1
  refine ?_ + (360710658 : R) * hh ^ 2 * w1 ^ 5 * a41 ^ 2 * u2
  refine ?_ + (429417450 : R) * hh ^ 2 * w1 ^ 5 * a41 ^ 2 * p32
  refine ?_ - (12124728 : R) * hh ^ 2 * w1 ^ 6 * q41
  refine ?_ + (137413584 : R) * hh ^ 2 * w1 ^ 6 * s1 * p2
  refine ?_ + (400789620 : R) * hh ^ 2 * w1 ^ 6 * a41 * p2
  refine ?_ + (103060188 : R) * hh ^ 2 * w1 ^ 6 * a41 * b62
  refine ?_ - (458045280 : R) * hh ^ 2 * w1 ^ 6 * a41 ^ 2 * s1
  refine ?_ - (254469600 : R) * hh ^ 2 * w1 ^ 6 * a41 ^ 3
  refine ?_ - (143489070 : R) * hh * lam * a41 * p2 * p1
  refine ?_ + (63772920 : R) * hh * lam * a41 * p32 ^ 3
  refine ?_ + (63772920 : R) * hh * lam * a41 ^ 3 * p1
  refine ?_ + (191318760 : R) * hh * lam * w1 * p32 ^ 2 * p2
  refine ?_ - (350751060 : R) * hh * lam * w1 * a41 ^ 2 * p32 ^ 2
  refine ?_ - (701502120 : R) * hh * lam * w1 ^ 2 * a41 * p32 * p2
  refine ?_ + (545612760 : R) * hh * lam * w1 ^ 2 * a41 ^ 3 * p32
  refine ?_ - (116917020 : R) * hh * lam * w1 ^ 3 * p2 ^ 2
  refine ?_ + (545612760 : R) * hh * lam * w1 ^ 3 * a41 ^ 2 * p2
  refine ?_ - (257650470 : R) * hh * lam * w1 ^ 3 * a41 ^ 4
  refine ?_ + (129140163 : R) * hh * p1 * q3
  refine ?_ + (86093442 : R) * hh * p2 * q2
  refine ?_ - (200884698 : R) * hh * u2 * p2 * p1
  refine ?_ + (478296900 : R) * hh * p32 * p2 * p1
  refine ?_ - (172186884 : R) * hh * p32 * b62 * p1
  refine ?_ + (55801305 : R) * hh * p32 ^ 3 * u2
  refine ?_ - (53144100 : R) * hh * p32 ^ 4
  refine ?_ - (143489070 : R) * hh * a41 * q53 * p1
  refine ?_ + (382637520 : R) * hh * a41 * p32 * s1 * p1
  refine ?_ - (28697814 : R) * hh * a41 ^ 2 * q2
  refine ?_ + (167403915 : R) * hh * a41 ^ 2 * u2 * p1
  refine ?_ - (637729200 : R) * hh * a41 ^ 2 * p32 * p1
  refine ?_ - (114791256 : R) * hh * w1 * p1 * q41
  refine ?_ + (382637520 : R) * hh * w1 * s1 * p2 * p1
  refine ?_ + (119574225 : R) * hh * w1 * p32 ^ 2 * q53
  refine ?_ - (170061120 : R) * hh * w1 * p32 ^ 3 * s1
  refine ?_ - (558013050 : R) * hh * w1 * a41 * p2 * p1
  refine ?_ + (286978140 : R) * hh * w1 * a41 * b62 * p1
  refine ?_ - (446410440 : R) * hh * w1 * a41 * p32 ^ 2 * u2
  refine ?_ + (460582200 : R) * hh * w1 * a41 * p32 ^ 3
  refine ?_ - (510183360 : R) * hh * w1 * a41 ^ 2 * s1 * p1
  refine ?_ + (460582200 : R) * hh * w1 * a41 ^ 3 * p1
  refine ?_ + (71744535 : R) * hh * w1 ^ 2 * p32 * q3
  refine ?_ - (446410440 : R) * hh * w1 ^ 2 * p32 * u2 * p2
  refine ?_ + (212576400 : R) * hh * w1 ^ 2 * p32 ^ 2 * p2
  refine ?_ - (191318760 : R) * hh * w1 ^ 2 * p32 ^ 2 * b62
  refine ?_ - (318864600 : R) * hh * w1 ^ 2 * a41 * p32 * q53
  refine ?_ + (935336160 : R) * hh * w1 ^ 2 * a41 * p32 ^ 2 * s1
  refine ?_ + (818419140 : R) * hh * w1 ^ 2 * a41 ^ 2 * p32 * u2
  refine ?_ - (974308500 : R) * hh * w1 ^ 2 * a41 ^ 2 * p32 ^ 2
  refine ?_ - (106288200 : R) * hh * w1 ^ 3 * q53 * p2
  refine ?_ - (85030560 : R) * hh * w1 ^ 3 * p32 * q41
  refine ?_ + (623557440 : R) * hh * w1 ^ 3 * p32 * s1 * p2
  refine ?_ - (63772920 : R) * hh * w1 ^ 3 * a41 * q3
  refine ?_ + (545612760 : R) * hh * w1 ^ 3 * a41 * u2 * p2
  refine ?_ - (129907800 : R) * hh * w1 ^ 3 * a41 * p32 * p2
  refine ?_ + (467668080 : R) * hh * w1 ^ 3 * a41 * p32 * b62
  refine ?_ + (194861700 : R) * hh * w1 ^ 3 * a41 ^ 2 * q53
  refine ?_ - (1454967360 : R) * hh * w1 ^ 3 * a41 ^ 2 * p32 * s1
  refine ?_ - (424365480 : R) * hh * w1 ^ 3 * a41 ^ 3 * u2
  refine ?_ + (707275800 : R) * hh * w1 ^ 3 * a41 ^ 3 * p32
  refine ?_ + (129907800 : R) * hh * w1 ^ 4 * p2 ^ 2
  refine ?_ + (116917020 : R) * hh * w1 ^ 4 * b62 * p2
  refine ?_ + (77944680 : R) * hh * w1 ^ 4 * a41 * q41
  refine ?_ - (727483680 : R) * hh * w1 ^ 4 * a41 * s1 * p2
  refine ?_ - (151559100 : R) * hh * w1 ^ 4 * a41 ^ 2 * p2
  refine ?_ - (272806380 : R) * hh * w1 ^ 4 * a41 ^ 2 * b62
  refine ?_ + (687067920 : R) * hh * w1 ^ 4 * a41 ^ 3 * s1
  refine ?_ - (143139150 : R) * hh * w1 ^ 4 * a41 ^ 4
  refine ?_ - (71744535 : R) * lam * p32 * p2 ^ 2
  refine ?_ + (191318760 : R) * lam * a41 ^ 2 * p32 * p2
  refine ?_ - (58458510 : R) * lam * a41 ^ 4 * p32
  refine ?_ + (191318760 : R) * lam * w1 * a41 * p2 ^ 2
  refine ?_ - (233834040 : R) * lam * w1 * a41 ^ 3 * p2
  refine ?_ + (54561276 : R) * lam * w1 * a41 ^ 5
  refine ?_ - (143489070 : R) * p32 * q53 * p2
  refine ?_ - (57395628 : R) * p32 ^ 2 * q41
  refine ?_ + (191318760 : R) * p32 ^ 2 * s1 * p2
  refine ?_ - (86093442 : R) * a41 * p32 * q3
  refine ?_ + (334807830 : R) * a41 * p32 * u2 * p2
  refine ?_ - (637729200 : R) * a41 * p32 ^ 2 * p2
  refine ?_ + (143489070 : R) * a41 * p32 ^ 2 * b62
  refine ?_ + (119574225 : R) * a41 ^ 2 * p32 * q53
  refine ?_ - (255091680 : R) * a41 ^ 2 * p32 ^ 2 * s1
  refine ?_ - (148803480 : R) * a41 ^ 3 * p32 * u2
  refine ?_ + (389723400 : R) * a41 ^ 3 * p32 ^ 2
  refine ?_ - (86093442 : R) * w1 * p2 * q3
  refine ?_ + (167403915 : R) * w1 * u2 * p2 ^ 2
  refine ?_ - (279006525 : R) * w1 * p32 * p2 ^ 2
  refine ?_ + (286978140 : R) * w1 * p32 * b62 * p2
  refine ?_ + (239148450 : R) * w1 * a41 * q53 * p2
  refine ?_ + (191318760 : R) * w1 * a41 * p32 * q41
  refine ?_ - (1020366720 : R) * w1 * a41 * p32 * s1 * p2
  refine ?_ + (71744535 : R) * w1 * a41 ^ 2 * q3
  refine ?_ - (446410440 : R) * w1 * a41 ^ 2 * u2 * p2
  refine ?_ + (1381746600 : R) * w1 * a41 ^ 2 * p32 * p2
  refine ?_ - (382637520 : R) * w1 * a41 ^ 2 * p32 * b62
  refine ?_ - (106288200 : R) * w1 * a41 ^ 3 * q53
  refine ?_ + (623557440 : R) * w1 * a41 ^ 3 * p32 * s1
  refine ?_ + (136403190 : R) * w1 * a41 ^ 4 * u2
  refine ?_ - (617062050 : R) * w1 * a41 ^ 4 * p32
  exact (242494560 : R) * w1 ^ 2 * a41 ^ 5
    - (363741840 : R) * w1 ^ 2 * a41 ^ 4 * s1
    + (233834040 : R) * w1 ^ 2 * a41 ^ 3 * b62
    - (649539000 : R) * w1 ^ 2 * a41 ^ 3 * p2
    + (935336160 : R) * w1 ^ 2 * a41 ^ 2 * s1 * p2
    - (127545840 : R) * w1 ^ 2 * a41 ^ 2 * q41
    - (382637520 : R) * w1 ^ 2 * a41 * b62 * p2
    + (212576400 : R) * w1 ^ 2 * a41 * p2 ^ 2
    - (255091680 : R) * w1 ^ 2 * s1 * p2 ^ 2
    + (95659380 : R) * w1 ^ 2 * p2 * q41

end BridgeLambdaJet610

end Max11DegreeRoutes
