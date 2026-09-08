import Fable610ScaleTwoKappaIntegralBridgeCompatKappaSpeedPart02Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepression610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 80000000 in
/-- Clearing the first integral `κ` of the degree-`4` row against `h⁵⁵`
on the ninth-power face. -/
theorem bridgeKappaDefect_eq_cleared610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (3761479876608 : F) * h ^ 55 *
        bridgeKappaResidual610
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
    - (231612681800 : F) * a5 ^ 11
    + (114648277491 : F) * a5 ^ 10 * h ^ 5 * lambda
    + (2018963377200 : F) * a4 * a5 ^ 9 * h ^ 6
    + (346108007520 : F) * a5 ^ 9 * b8 * h ^ 2
    - (1168114525380 : F) * a4 * a5 ^ 8 * h ^ 11 * lambda
    - (2071125045000 : F) * a3 * a5 ^ 8 * h ^ 12
    - (347949007560 : F) * a5 ^ 8 * b7 * h ^ 8
    - (5302080115200 : F) * a4 ^ 2 * a5 ^ 7 * h ^ 12
    - (3181248069120 : F) * a4 * a5 ^ 7 * b8 * h ^ 8
    + (1192968025920 : F) * a3 * a5 ^ 7 * h ^ 17 * lambda
    + (2133763948800 : F) * a2 * a5 ^ 7 * h ^ 18
    + (349161373440 : F) * a5 ^ 7 * b6 * h ^ 14
    + (4175388090720 : F) * a4 ^ 2 * a5 ^ 6 * h ^ 17 * lambda
    + (8826023606400 : F) * a3 * a4 * a5 ^ 6 * h ^ 18
    + (2851484549760 : F) * a4 * a5 ^ 6 * b7 * h ^ 14
    + (3258839485440 : F) * a3 * a5 ^ 6 * b8 * h ^ 14
    - (1222064807040 : F) * a2 * a5 ^ 6 * h ^ 23 * lambda
    - (2211355365120 : F) * a1 * a5 ^ 6 * h ^ 24
    - (349161373440 : F) * a5 ^ 6 * b5 * h ^ 20
    + (2715699571200 : F) * a4 ^ 3 * a5 ^ 5 * h ^ 18
    + (9776518456320 : F) * a4 ^ 2 * a5 ^ 5 * b8 * h ^ 14
    - (7332388842240 : F) * a3 * a4 * a5 ^ 5 * h ^ 23 * lambda
    - (6983227468800 : F) * a2 * a4 * a5 ^ 5 * h ^ 24
    - (2513961888768 : F) * a4 * a5 ^ 5 * b6 * h ^ 20
    - (3491613734400 : F) * a3 ^ 2 * a5 ^ 5 * h ^ 24
    - (2932955536896 : F) * a3 * a5 ^ 5 * b7 * h ^ 20
    - (3351949185024 : F) * a2 * a5 ^ 5 * b8 * h ^ 20
    + (1256980944384 : F) * a1 * a5 ^ 5 * h ^ 29 * lambda
    + (2311689093120 : F) * a0 * a5 ^ 5 * h ^ 30
    + (346753363968 : F) * a5 ^ 5 * b4 * h ^ 26
    - (6110324035200 : F) * a4 ^ 3 * a5 ^ 4 * h ^ 23 * lambda
    - (1745806867200 : F) * a3 * a4 ^ 2 * a5 ^ 4 * h ^ 24
    - (7332388842240 : F) * a4 ^ 2 * a5 ^ 4 * b7 * h ^ 20
    - (16759745925120 : F) * a3 * a4 * a5 ^ 4 * b8 * h ^ 20
    + (6284904721920 : F) * a2 * a4 * a5 ^ 4 * h ^ 29 * lambda
    + (5056819891200 : F) * a1 * a4 * a5 ^ 4 * h ^ 30
    + (2167208524800 : F) * a4 * a5 ^ 4 * b5 * h ^ 26
    + (3142452360960 : F) * a3 ^ 2 * a5 ^ 4 * h ^ 29 * lambda
    + (5056819891200 : F) * a2 * a3 * a5 ^ 4 * h ^ 30
    + (2600650229760 : F) * a3 * a5 ^ 4 * b6 * h ^ 26
    + (3034091934720 : F) * a2 * a5 ^ 4 * b7 * h ^ 26
    + (3467533639680 : F) * a1 * a5 ^ 4 * b8 * h ^ 26
    - (1300325114880 : F) * a0 * a5 ^ 4 * h ^ 35 * lambda
    - (339215247360 : F) * a5 ^ 4 * b3 * h ^ 32
    + (4655484979200 : F) * a4 ^ 4 * a5 ^ 3 * h ^ 24
    - (11173163950080 : F) * a4 ^ 3 * a5 ^ 3 * b8 * h ^ 20
    + (12569809443840 : F) * a3 * a4 ^ 2 * a5 ^ 3 * h ^ 29 * lambda
    - (2889611366400 : F) * a2 * a4 ^ 2 * a5 ^ 3 * h ^ 30
    + (5201300459520 : F) * a4 ^ 2 * a5 ^ 3 * b6 * h ^ 26
    - (2889611366400 : F) * a3 ^ 2 * a4 * a5 ^ 3 * h ^ 30
    + (12136367738880 : F) * a3 * a4 * a5 ^ 3 * b7 * h ^ 26
    + (13870134558720 : F) * a2 * a4 * a5 ^ 3 * b8 * h ^ 26
    - (5201300459520 : F) * a1 * a4 * a5 ^ 3 * h ^ 35 * lambda
    - (3015246643200 : F) * a0 * a4 * a5 ^ 3 * h ^ 36
    - (1809147985920 : F) * a4 * a5 ^ 3 * b4 * h ^ 32
    + (6935067279360 : F) * a3 ^ 2 * a5 ^ 3 * b8 * h ^ 26
    - (5201300459520 : F) * a2 * a3 * a5 ^ 3 * h ^ 35 * lambda
    - (3015246643200 : F) * a1 * a3 * a5 ^ 3 * h ^ 36
    - (2261434982400 : F) * a3 * a5 ^ 3 * b5 * h ^ 32
    - (1507623321600 : F) * a2 ^ 2 * a5 ^ 3 * h ^ 36
    - (2713721978880 : F) * a2 * a5 ^ 3 * b6 * h ^ 32
    - (3166008975360 : F) * a1 * a5 ^ 3 * b7 * h ^ 32
    - (3618295971840 : F) * a0 * a5 ^ 3 * b8 * h ^ 32
    + (319261409280 : F) * a5 ^ 3 * b2 * h ^ 38
    + (3142452360960 : F) * a4 ^ 4 * a5 ^ 2 * h ^ 29 * lambda
    - (15892862515200 : F) * a3 * a4 ^ 3 * a5 ^ 2 * h ^ 30
    + (6068183869440 : F) * a4 ^ 3 * a5 ^ 2 * b7 * h ^ 26
    + (20805201838080 : F) * a3 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 26
    - (7801950689280 : F) * a2 * a4 ^ 2 * a5 ^ 2 * h ^ 35 * lambda
    + (5653587456000 : F) * a1 * a4 ^ 2 * a5 ^ 2 * h ^ 36
    - (3392152473600 : F) * a4 ^ 2 * a5 ^ 2 * b5 * h ^ 32
    - (7801950689280 : F) * a3 ^ 2 * a4 * a5 ^ 2 * h ^ 35 * lambda
    + (11307174912000 : F) * a2 * a3 * a4 * a5 ^ 2 * h ^ 36
    - (8141165936640 : F) * a3 * a4 * a5 ^ 2 * b6 * h ^ 32
    - (9498026926080 : F) * a2 * a4 * a5 ^ 2 * b7 * h ^ 32
    - (10854887915520 : F) * a1 * a4 * a5 ^ 2 * b8 * h ^ 32
    + (4070582968320 : F) * a0 * a4 * a5 ^ 2 * h ^ 41 * lambda
    + (1436676341760 : F) * a4 * a5 ^ 2 * b3 * h ^ 38
    + (1884529152000 : F) * a3 ^ 3 * a5 ^ 2 * h ^ 36
    - (4749013463040 : F) * a3 ^ 2 * a5 ^ 2 * b7 * h ^ 32
    - (10854887915520 : F) * a2 * a3 * a5 ^ 2 * b8 * h ^ 32
    + (4070582968320 : F) * a1 * a3 * a5 ^ 2 * h ^ 41 * lambda
    + (798153523200 : F) * a0 * a3 * a5 ^ 2 * h ^ 42
    + (1915568455680 : F) * a3 * a5 ^ 2 * b4 * h ^ 38
    + (2035291484160 : F) * a2 ^ 2 * a5 ^ 2 * h ^ 41 * lambda
    + (798153523200 : F) * a1 * a2 * a5 ^ 2 * h ^ 42
    + (2394460569600 : F) * a2 * a5 ^ 2 * b5 * h ^ 38
    + (2873352683520 : F) * a1 * a5 ^ 2 * b6 * h ^ 38
    + (3352244797440 : F) * a0 * a5 ^ 2 * b7 * h ^ 38
    - (261213880320 : F) * a5 ^ 2 * b1 * h ^ 44
    - (2889611366400 : F) * a4 ^ 5 * a5 * h ^ 30
    + (3467533639680 : F) * a4 ^ 4 * a5 * b8 * h ^ 26
    - (5201300459520 : F) * a3 * a4 ^ 3 * a5 * h ^ 35 * lambda
    + (10553363251200 : F) * a2 * a4 ^ 3 * a5 * h ^ 36
    - (2713721978880 : F) * a4 ^ 3 * a5 * b6 * h ^ 32
    + (15830044876800 : F) * a3 ^ 2 * a4 ^ 2 * a5 * h ^ 36
    - (9498026926080 : F) * a3 * a4 ^ 2 * a5 * b7 * h ^ 32
    - (10854887915520 : F) * a2 * a4 ^ 2 * a5 * b8 * h ^ 32
    + (4070582968320 : F) * a1 * a4 ^ 2 * a5 * h ^ 41 * lambda
    - (6385228185600 : F) * a0 * a4 ^ 2 * a5 * h ^ 42
    + (1915568455680 : F) * a4 ^ 2 * a5 * b4 * h ^ 38
    - (10854887915520 : F) * a3 ^ 2 * a4 * a5 * b8 * h ^ 32
    + (8141165936640 : F) * a2 * a3 * a4 * a5 * h ^ 41 * lambda
    - (12770456371200 : F) * a1 * a3 * a4 * a5 * h ^ 42
    + (4788921139200 : F) * a3 * a4 * a5 * b5 * h ^ 38
    - (6385228185600 : F) * a2 ^ 2 * a4 * a5 * h ^ 42
    + (5746705367040 : F) * a2 * a4 * a5 * b6 * h ^ 38
    + (6704489594880 : F) * a1 * a4 * a5 * b7 * h ^ 38
    + (7662273822720 : F) * a0 * a4 * a5 * b8 * h ^ 38
    - (1044855521280 : F) * a4 * a5 * b2 * h ^ 44
    + (1356860989440 : F) * a3 ^ 3 * a5 * h ^ 41 * lambda
    - (6385228185600 : F) * a2 * a3 ^ 2 * a5 * h ^ 42
    + (2873352683520 : F) * a3 ^ 2 * a5 * b6 * h ^ 38
    + (6704489594880 : F) * a2 * a3 * a5 * b7 * h ^ 38
    + (7662273822720 : F) * a1 * a3 * a5 * b8 * h ^ 38
    - (2873352683520 : F) * a0 * a3 * a5 * h ^ 47 * lambda
    - (1567283281920 : F) * a3 * a5 * b3 * h ^ 44
    + (3831136911360 : F) * a2 ^ 2 * a5 * b8 * h ^ 38
    - (2873352683520 : F) * a1 * a2 * a5 * h ^ 47 * lambda
    + (1741425868800 : F) * a0 * a2 * a5 * h ^ 48
    - (2089711042560 : F) * a2 * a5 * b4 * h ^ 44
    + (870712934400 : F) * a1 ^ 2 * a5 * h ^ 48
    - (2612138803200 : F) * a1 * a5 * b5 * h ^ 44
    - (3134566563840 : F) * a0 * a5 * b6 * h ^ 44
    - (260065022976 : F) * a4 ^ 5 * h ^ 35 * lambda
    + (4334417049600 : F) * a3 * a4 ^ 4 * h ^ 36
    - (791502243840 : F) * a4 ^ 4 * b7 * h ^ 32
    - (3618295971840 : F) * a3 * a4 ^ 3 * b8 * h ^ 32
    + (1356860989440 : F) * a2 * a4 ^ 3 * h ^ 41 * lambda
    - (4522869964800 : F) * a1 * a4 ^ 3 * h ^ 42
    + (798153523200 : F) * a4 ^ 3 * b5 * h ^ 38
    + (2035291484160 : F) * a3 ^ 2 * a4 ^ 2 * h ^ 41 * lambda
    - (13568609894400 : F) * a2 * a3 * a4 ^ 2 * h ^ 42
    + (2873352683520 : F) * a3 * a4 ^ 2 * b6 * h ^ 38
    + (3352244797440 : F) * a2 * a4 ^ 2 * b7 * h ^ 38
    + (3831136911360 : F) * a1 * a4 ^ 2 * b8 * h ^ 38
    - (1436676341760 : F) * a0 * a4 ^ 2 * h ^ 47 * lambda
    - (783641640960 : F) * a4 ^ 2 * b3 * h ^ 44
    - (4522869964800 : F) * a3 ^ 3 * a4 * h ^ 42
    + (3352244797440 : F) * a3 ^ 2 * a4 * b7 * h ^ 38
    + (7662273822720 : F) * a2 * a3 * a4 * b8 * h ^ 38
    - (2873352683520 : F) * a1 * a3 * a4 * h ^ 47 * lambda
    + (9577842278400 : F) * a0 * a3 * a4 * h ^ 48
    - (2089711042560 : F) * a3 * a4 * b4 * h ^ 44
    - (1436676341760 : F) * a2 ^ 2 * a4 * h ^ 47 * lambda
    + (9577842278400 : F) * a1 * a2 * a4 * h ^ 48
    - (2612138803200 : F) * a2 * a4 * b5 * h ^ 44
    - (3134566563840 : F) * a1 * a4 * b6 * h ^ 44
    - (3656994324480 : F) * a0 * a4 * b7 * h ^ 44
    + (626913312768 : F) * a4 * b1 * h ^ 50
    + (1277045637120 : F) * a3 ^ 3 * b8 * h ^ 38
    - (1436676341760 : F) * a2 * a3 ^ 2 * h ^ 47 * lambda
    + (4788921139200 : F) * a1 * a3 ^ 2 * h ^ 48
    - (1306069401600 : F) * a3 ^ 2 * b5 * h ^ 44
    + (4788921139200 : F) * a2 ^ 2 * a3 * h ^ 48
    - (3134566563840 : F) * a2 * a3 * b6 * h ^ 44
    - (3656994324480 : F) * a1 * a3 * b7 * h ^ 44
    - (4179422085120 : F) * a0 * a3 * b8 * h ^ 44
    + (1253826625536 : F) * a3 * b2 * h ^ 50
    - (1828497162240 : F) * a2 ^ 2 * b7 * h ^ 44
    - (4179422085120 : F) * a1 * a2 * b8 * h ^ 44
    + (1567283281920 : F) * a0 * a2 * h ^ 53 * lambda
    + (1880739938304 : F) * a2 * b3 * h ^ 50
    + (783641640960 : F) * a1 ^ 2 * h ^ 53 * lambda
    - (5224277606400 : F) * a0 * a1 * h ^ 54
    + (2507653251072 : F) * a1 * b4 * h ^ 50
    + (3134566563840 : F) * a0 * b5 * h ^ 50 := by
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
  have h3761479876608 : (3761479876608 : F) ≠ 0 := by norm_num
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
    speedBridgeKappaResidual610Scaled55_eq h hh]
  simp only [speedBridgeKappaResidual610Scaled55]
  ring

end BridgeKappaDepression610

end Max11DegreeRoutes
