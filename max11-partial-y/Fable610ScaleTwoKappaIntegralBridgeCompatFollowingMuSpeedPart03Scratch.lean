import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingMuSpeedPart02Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuDepression610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- Clearing the first integral `μ` of the degree-`2` row against `h⁶⁵`
on the ninth-power face. -/
theorem bridgeMuDefect_eq_cleared610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (12582912 : F) * h ^ 65 *
        bridgeMuResidual610
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
    - (180880 : F) * a5 ^ 13
    + (88179 : F) * a5 ^ 12 * lambda * h ^ 5
    + (2015520 : F) * a5 ^ 11 * a4 * h ^ 6
    + (268736 : F) * a5 ^ 11 * b8 * h ^ 2
    - (1108536 : F) * a5 ^ 10 * a4 * lambda * h ^ 11
    - (2139280 : F) * a5 ^ 10 * a3 * h ^ 12
    - (272272 : F) * a5 ^ 10 * b7 * h ^ 8
    - (7779200 : F) * a5 ^ 9 * a4 ^ 2 * h ^ 12
    - (3111680 : F) * a5 ^ 9 * a4 * b8 * h ^ 8
    + (1166880 : F) * a5 ^ 9 * a3 * lambda * h ^ 17
    + (2288000 : F) * a5 ^ 9 * a2 * h ^ 18
    + (274560 : F) * a5 ^ 9 * b6 * h ^ 14
    + (5250960 : F) * a5 ^ 8 * a4 ^ 2 * lambda * h ^ 17
    + (14414400 : F) * a5 ^ 8 * a4 * a3 * h ^ 18
    + (2882880 : F) * a5 ^ 8 * a4 * b7 * h ^ 14
    + (3294720 : F) * a5 ^ 8 * a3 * b8 * h ^ 14
    - (1235520 : F) * a5 ^ 8 * a2 * lambda * h ^ 23
    - (2471040 : F) * a5 ^ 8 * a1 * h ^ 24
    - (274560 : F) * a5 ^ 8 * b5 * h ^ 20
    + (10982400 : F) * a5 ^ 7 * a4 ^ 3 * h ^ 18
    + (13178880 : F) * a5 ^ 7 * a4 ^ 2 * b8 * h ^ 14
    - (9884160 : F) * a5 ^ 7 * a4 * a3 * lambda * h ^ 23
    - (13178880 : F) * a5 ^ 7 * a4 * a2 * h ^ 24
    - (2635776 : F) * a5 ^ 7 * a4 * b6 * h ^ 20
    - (6589440 : F) * a5 ^ 7 * a3 ^ 2 * h ^ 24
    - (3075072 : F) * a5 ^ 7 * a3 * b7 * h ^ 20
    - (3514368 : F) * a5 ^ 7 * a2 * b8 * h ^ 20
    + (1317888 : F) * a5 ^ 7 * a1 * lambda * h ^ 29
    + (2703360 : F) * a5 ^ 7 * a0 * h ^ 30
    + (270336 : F) * a5 ^ 7 * b4 * h ^ 26
    - (11531520 : F) * a5 ^ 6 * a4 ^ 3 * lambda * h ^ 23
    - (23063040 : F) * a5 ^ 6 * a4 ^ 2 * a3 * h ^ 24
    - (10762752 : F) * a5 ^ 6 * a4 ^ 2 * b7 * h ^ 20
    - (24600576 : F) * a5 ^ 6 * a4 * a3 * b8 * h ^ 20
    + (9225216 : F) * a5 ^ 6 * a4 * a2 * lambda * h ^ 29
    + (11827200 : F) * a5 ^ 6 * a4 * a1 * h ^ 30
    + (2365440 : F) * a5 ^ 6 * a4 * b5 * h ^ 26
    + (4612608 : F) * a5 ^ 6 * a3 ^ 2 * lambda * h ^ 29
    + (11827200 : F) * a5 ^ 6 * a3 * a2 * h ^ 30
    + (2838528 : F) * a5 ^ 6 * a3 * b6 * h ^ 26
    + (3311616 : F) * a5 ^ 6 * a2 * b7 * h ^ 26
    + (3784704 : F) * a5 ^ 6 * a1 * b8 * h ^ 26
    - (1419264 : F) * a5 ^ 6 * a0 * lambda * h ^ 35
    - (258048 : F) * a5 ^ 6 * b3 * h ^ 32
    - (24600576 : F) * a5 ^ 5 * a4 ^ 3 * b8 * h ^ 20
    + (27675648 : F) * a5 ^ 5 * a4 ^ 2 * a3 * lambda * h ^ 29
    + (14192640 : F) * a5 ^ 5 * a4 ^ 2 * a2 * h ^ 30
    + (8515584 : F) * a5 ^ 5 * a4 ^ 2 * b6 * h ^ 26
    + (14192640 : F) * a5 ^ 5 * a4 * a3 ^ 2 * h ^ 30
    + (19869696 : F) * a5 ^ 5 * a4 * a3 * b7 * h ^ 26
    + (22708224 : F) * a5 ^ 5 * a4 * a2 * b8 * h ^ 26
    - (8515584 : F) * a5 ^ 5 * a4 * a1 * lambda * h ^ 35
    - (10321920 : F) * a5 ^ 5 * a4 * a0 * h ^ 36
    - (2064384 : F) * a5 ^ 5 * a4 * b4 * h ^ 32
    + (11354112 : F) * a5 ^ 5 * a3 ^ 2 * b8 * h ^ 26
    - (8515584 : F) * a5 ^ 5 * a3 * a2 * lambda * h ^ 35
    - (10321920 : F) * a5 ^ 5 * a3 * a1 * h ^ 36
    - (2580480 : F) * a5 ^ 5 * a3 * b5 * h ^ 32
    - (5160960 : F) * a5 ^ 5 * a2 ^ 2 * h ^ 36
    - (3096576 : F) * a5 ^ 5 * a2 * b6 * h ^ 32
    - (3612672 : F) * a5 ^ 5 * a1 * b7 * h ^ 32
    - (4128768 : F) * a5 ^ 5 * a0 * b8 * h ^ 32
    + (229376 : F) * a5 ^ 5 * b2 * h ^ 38
    + (11531520 : F) * a5 ^ 4 * a4 ^ 4 * lambda * h ^ 29
    - (11827200 : F) * a5 ^ 4 * a4 ^ 3 * a3 * h ^ 30
    + (16558080 : F) * a5 ^ 4 * a4 ^ 3 * b7 * h ^ 26
    + (56770560 : F) * a5 ^ 4 * a4 ^ 2 * a3 * b8 * h ^ 26
    - (21288960 : F) * a5 ^ 4 * a4 ^ 2 * a2 * lambda * h ^ 35
    - (6451200 : F) * a5 ^ 4 * a4 ^ 2 * a1 * h ^ 36
    - (6451200 : F) * a5 ^ 4 * a4 ^ 2 * b5 * h ^ 32
    - (21288960 : F) * a5 ^ 4 * a4 * a3 ^ 2 * lambda * h ^ 35
    - (12902400 : F) * a5 ^ 4 * a4 * a3 * a2 * h ^ 36
    - (15482880 : F) * a5 ^ 4 * a4 * a3 * b6 * h ^ 32
    - (18063360 : F) * a5 ^ 4 * a4 * a2 * b7 * h ^ 32
    - (20643840 : F) * a5 ^ 4 * a4 * a1 * b8 * h ^ 32
    + (7741440 : F) * a5 ^ 4 * a4 * a0 * lambda * h ^ 41
    + (1720320 : F) * a5 ^ 4 * a4 * b3 * h ^ 38
    - (2150400 : F) * a5 ^ 4 * a3 ^ 3 * h ^ 36
    - (9031680 : F) * a5 ^ 4 * a3 ^ 2 * b7 * h ^ 32
    - (20643840 : F) * a5 ^ 4 * a3 * a2 * b8 * h ^ 32
    + (7741440 : F) * a5 ^ 4 * a3 * a1 * lambda * h ^ 41
    + (8601600 : F) * a5 ^ 4 * a3 * a0 * h ^ 42
    + (2293760 : F) * a5 ^ 4 * a3 * b4 * h ^ 38
    + (3870720 : F) * a5 ^ 4 * a2 ^ 2 * lambda * h ^ 41
    + (8601600 : F) * a5 ^ 4 * a2 * a1 * h ^ 42
    + (2867200 : F) * a5 ^ 4 * a2 * b5 * h ^ 38
    + (3440640 : F) * a5 ^ 4 * a1 * b6 * h ^ 38
    + (4014080 : F) * a5 ^ 4 * a0 * b7 * h ^ 38
    - (163840 : F) * a5 ^ 4 * b1 * h ^ 44
    - (9461760 : F) * a5 ^ 3 * a4 ^ 5 * h ^ 30
    + (18923520 : F) * a5 ^ 3 * a4 ^ 4 * b8 * h ^ 26
    - (28385280 : F) * a5 ^ 3 * a4 ^ 3 * a3 * lambda * h ^ 35
    + (17203200 : F) * a5 ^ 3 * a4 ^ 3 * a2 * h ^ 36
    - (10321920 : F) * a5 ^ 3 * a4 ^ 3 * b6 * h ^ 32
    + (25804800 : F) * a5 ^ 3 * a4 ^ 2 * a3 ^ 2 * h ^ 36
    - (36126720 : F) * a5 ^ 3 * a4 ^ 2 * a3 * b7 * h ^ 32
    - (41287680 : F) * a5 ^ 3 * a4 ^ 2 * a2 * b8 * h ^ 32
    + (15482880 : F) * a5 ^ 3 * a4 ^ 2 * a1 * lambda * h ^ 41
    + (4587520 : F) * a5 ^ 3 * a4 ^ 2 * b4 * h ^ 38
    - (41287680 : F) * a5 ^ 3 * a4 * a3 ^ 2 * b8 * h ^ 32
    + (30965760 : F) * a5 ^ 3 * a4 * a3 * a2 * lambda * h ^ 41
    + (11468800 : F) * a5 ^ 3 * a4 * a3 * b5 * h ^ 38
    + (13762560 : F) * a5 ^ 3 * a4 * a2 * b6 * h ^ 38
    + (16056320 : F) * a5 ^ 3 * a4 * a1 * b7 * h ^ 38
    + (18350080 : F) * a5 ^ 3 * a4 * a0 * b8 * h ^ 38
    - (1310720 : F) * a5 ^ 3 * a4 * b2 * h ^ 44
    + (5160960 : F) * a5 ^ 3 * a3 ^ 3 * lambda * h ^ 41
    + (6881280 : F) * a5 ^ 3 * a3 ^ 2 * b6 * h ^ 38
    + (16056320 : F) * a5 ^ 3 * a3 * a2 * b7 * h ^ 38
    + (18350080 : F) * a5 ^ 3 * a3 * a1 * b8 * h ^ 38
    - (6881280 : F) * a5 ^ 3 * a3 * a0 * lambda * h ^ 47
    - (1966080 : F) * a5 ^ 3 * a3 * b3 * h ^ 44
    + (9175040 : F) * a5 ^ 3 * a2 ^ 2 * b8 * h ^ 38
    - (6881280 : F) * a5 ^ 3 * a2 * a1 * lambda * h ^ 47
    - (6553600 : F) * a5 ^ 3 * a2 * a0 * h ^ 48
    - (2621440 : F) * a5 ^ 3 * a2 * b4 * h ^ 44
    - (3276800 : F) * a5 ^ 3 * a1 ^ 2 * h ^ 48
    - (3276800 : F) * a5 ^ 3 * a1 * b5 * h ^ 44
    - (3932160 : F) * a5 ^ 3 * a0 * b6 * h ^ 44
    - (4257792 : F) * a5 ^ 2 * a4 ^ 5 * lambda * h ^ 35
    + (32256000 : F) * a5 ^ 2 * a4 ^ 4 * a3 * h ^ 36
    - (9031680 : F) * a5 ^ 2 * a4 ^ 4 * b7 * h ^ 32
    - (41287680 : F) * a5 ^ 2 * a4 ^ 3 * a3 * b8 * h ^ 32
    + (15482880 : F) * a5 ^ 2 * a4 ^ 3 * a2 * lambda * h ^ 41
    - (17203200 : F) * a5 ^ 2 * a4 ^ 3 * a1 * h ^ 42
    + (5734400 : F) * a5 ^ 2 * a4 ^ 3 * b5 * h ^ 38
    + (23224320 : F) * a5 ^ 2 * a4 ^ 2 * a3 ^ 2 * lambda * h ^ 41
    - (51609600 : F) * a5 ^ 2 * a4 ^ 2 * a3 * a2 * h ^ 42
    + (20643840 : F) * a5 ^ 2 * a4 ^ 2 * a3 * b6 * h ^ 38
    + (24084480 : F) * a5 ^ 2 * a4 ^ 2 * a2 * b7 * h ^ 38
    + (27525120 : F) * a5 ^ 2 * a4 ^ 2 * a1 * b8 * h ^ 38
    - (10321920 : F) * a5 ^ 2 * a4 ^ 2 * a0 * lambda * h ^ 47
    - (2949120 : F) * a5 ^ 2 * a4 ^ 2 * b3 * h ^ 44
    - (17203200 : F) * a5 ^ 2 * a4 * a3 ^ 3 * h ^ 42
    + (24084480 : F) * a5 ^ 2 * a4 * a3 ^ 2 * b7 * h ^ 38
    + (55050240 : F) * a5 ^ 2 * a4 * a3 * a2 * b8 * h ^ 38
    - (20643840 : F) * a5 ^ 2 * a4 * a3 * a1 * lambda * h ^ 47
    + (9830400 : F) * a5 ^ 2 * a4 * a3 * a0 * h ^ 48
    - (7864320 : F) * a5 ^ 2 * a4 * a3 * b4 * h ^ 44
    - (10321920 : F) * a5 ^ 2 * a4 * a2 ^ 2 * lambda * h ^ 47
    + (9830400 : F) * a5 ^ 2 * a4 * a2 * a1 * h ^ 48
    - (9830400 : F) * a5 ^ 2 * a4 * a2 * b5 * h ^ 44
    - (11796480 : F) * a5 ^ 2 * a4 * a1 * b6 * h ^ 44
    - (13762560 : F) * a5 ^ 2 * a4 * a0 * b7 * h ^ 44
    + (786432 : F) * a5 ^ 2 * a4 * b1 * h ^ 50
    + (9175040 : F) * a5 ^ 2 * a3 ^ 3 * b8 * h ^ 38
    - (10321920 : F) * a5 ^ 2 * a3 ^ 2 * a2 * lambda * h ^ 47
    + (4915200 : F) * a5 ^ 2 * a3 ^ 2 * a1 * h ^ 48
    - (4915200 : F) * a5 ^ 2 * a3 ^ 2 * b5 * h ^ 44
    + (4915200 : F) * a5 ^ 2 * a3 * a2 ^ 2 * h ^ 48
    - (11796480 : F) * a5 ^ 2 * a3 * a2 * b6 * h ^ 44
    - (13762560 : F) * a5 ^ 2 * a3 * a1 * b7 * h ^ 44
    - (15728640 : F) * a5 ^ 2 * a3 * a0 * b8 * h ^ 44
    + (1572864 : F) * a5 ^ 2 * a3 * b2 * h ^ 50
    - (6881280 : F) * a5 ^ 2 * a2 ^ 2 * b7 * h ^ 44
    - (15728640 : F) * a5 ^ 2 * a2 * a1 * b8 * h ^ 44
    + (5898240 : F) * a5 ^ 2 * a2 * a0 * lambda * h ^ 53
    + (2359296 : F) * a5 ^ 2 * a2 * b3 * h ^ 50
    + (2949120 : F) * a5 ^ 2 * a1 ^ 2 * lambda * h ^ 53
    + (3932160 : F) * a5 ^ 2 * a1 * a0 * h ^ 54
    + (3145728 : F) * a5 ^ 2 * a1 * b4 * h ^ 50
    + (3932160 : F) * a5 ^ 2 * a0 * b5 * h ^ 50
    + (3440640 : F) * a5 * a4 ^ 6 * h ^ 36
    - (4128768 : F) * a5 * a4 ^ 5 * b8 * h ^ 32
    + (7741440 : F) * a5 * a4 ^ 4 * a3 * lambda * h ^ 41
    - (17203200 : F) * a5 * a4 ^ 4 * a2 * h ^ 42
    + (3440640 : F) * a5 * a4 ^ 4 * b6 * h ^ 38
    - (34406400 : F) * a5 * a4 ^ 3 * a3 ^ 2 * h ^ 42
    + (16056320 : F) * a5 * a4 ^ 3 * a3 * b7 * h ^ 38
    + (18350080 : F) * a5 * a4 ^ 3 * a2 * b8 * h ^ 38
    - (6881280 : F) * a5 * a4 ^ 3 * a1 * lambda * h ^ 47
    + (13107200 : F) * a5 * a4 ^ 3 * a0 * h ^ 48
    - (2621440 : F) * a5 * a4 ^ 3 * b4 * h ^ 44
    + (27525120 : F) * a5 * a4 ^ 2 * a3 ^ 2 * b8 * h ^ 38
    - (20643840 : F) * a5 * a4 ^ 2 * a3 * a2 * lambda * h ^ 47
    + (39321600 : F) * a5 * a4 ^ 2 * a3 * a1 * h ^ 48
    - (9830400 : F) * a5 * a4 ^ 2 * a3 * b5 * h ^ 44
    + (19660800 : F) * a5 * a4 ^ 2 * a2 ^ 2 * h ^ 48
    - (11796480 : F) * a5 * a4 ^ 2 * a2 * b6 * h ^ 44
    - (13762560 : F) * a5 * a4 ^ 2 * a1 * b7 * h ^ 44
    - (15728640 : F) * a5 * a4 ^ 2 * a0 * b8 * h ^ 44
    + (1572864 : F) * a5 * a4 ^ 2 * b2 * h ^ 50
    - (6881280 : F) * a5 * a4 * a3 ^ 3 * lambda * h ^ 47
    + (39321600 : F) * a5 * a4 * a3 ^ 2 * a2 * h ^ 48
    - (11796480 : F) * a5 * a4 * a3 ^ 2 * b6 * h ^ 44
    - (27525120 : F) * a5 * a4 * a3 * a2 * b7 * h ^ 44
    - (31457280 : F) * a5 * a4 * a3 * a1 * b8 * h ^ 44
    + (11796480 : F) * a5 * a4 * a3 * a0 * lambda * h ^ 53
    + (4718592 : F) * a5 * a4 * a3 * b3 * h ^ 50
    - (15728640 : F) * a5 * a4 * a2 ^ 2 * b8 * h ^ 44
    + (11796480 : F) * a5 * a4 * a2 * a1 * lambda * h ^ 53
    - (15728640 : F) * a5 * a4 * a2 * a0 * h ^ 54
    + (6291456 : F) * a5 * a4 * a2 * b4 * h ^ 50
    - (7864320 : F) * a5 * a4 * a1 ^ 2 * h ^ 54
    + (7864320 : F) * a5 * a4 * a1 * b5 * h ^ 50
    + (9437184 : F) * a5 * a4 * a0 * b6 * h ^ 50
    + (3276800 : F) * a5 * a3 ^ 4 * h ^ 48
    - (4587520 : F) * a5 * a3 ^ 3 * b7 * h ^ 44
    - (15728640 : F) * a5 * a3 ^ 2 * a2 * b8 * h ^ 44
    + (5898240 : F) * a5 * a3 ^ 2 * a1 * lambda * h ^ 53
    - (7864320 : F) * a5 * a3 ^ 2 * a0 * h ^ 54
    + (3145728 : F) * a5 * a3 ^ 2 * b4 * h ^ 50
    + (5898240 : F) * a5 * a3 * a2 ^ 2 * lambda * h ^ 53
    - (15728640 : F) * a5 * a3 * a2 * a1 * h ^ 54
    + (7864320 : F) * a5 * a3 * a2 * b5 * h ^ 50
    + (9437184 : F) * a5 * a3 * a1 * b6 * h ^ 50
    + (11010048 : F) * a5 * a3 * a0 * b7 * h ^ 50
    - (1048576 : F) * a5 * a3 * b1 * h ^ 56
    - (2621440 : F) * a5 * a2 ^ 3 * h ^ 54
    + (4718592 : F) * a5 * a2 ^ 2 * b6 * h ^ 50
    + (11010048 : F) * a5 * a2 * a1 * b7 * h ^ 50
    + (12582912 : F) * a5 * a2 * a0 * b8 * h ^ 50
    - (2097152 : F) * a5 * a2 * b2 * h ^ 56
    + (6291456 : F) * a5 * a1 ^ 2 * b8 * h ^ 50
    - (4718592 : F) * a5 * a1 * a0 * lambda * h ^ 59
    - (3145728 : F) * a5 * a1 * b3 * h ^ 56
    - (4194304 : F) * a5 * a0 * b4 * h ^ 56
    + (258048 : F) * a4 ^ 6 * lambda * h ^ 41
    - (5160960 : F) * a4 ^ 5 * a3 * h ^ 42
    + (802816 : F) * a4 ^ 5 * b7 * h ^ 38
    + (4587520 : F) * a4 ^ 4 * a3 * b8 * h ^ 38
    - (1720320 : F) * a4 ^ 4 * a2 * lambda * h ^ 47
    + (5734400 : F) * a4 ^ 4 * a1 * h ^ 48
    - (819200 : F) * a4 ^ 4 * b5 * h ^ 44
    - (3440640 : F) * a4 ^ 3 * a3 ^ 2 * lambda * h ^ 47
    + (22937600 : F) * a4 ^ 3 * a3 * a2 * h ^ 48
    - (3932160 : F) * a4 ^ 3 * a3 * b6 * h ^ 44
    - (4587520 : F) * a4 ^ 3 * a2 * b7 * h ^ 44
    - (5242880 : F) * a4 ^ 3 * a1 * b8 * h ^ 44
    + (1966080 : F) * a4 ^ 3 * a0 * lambda * h ^ 53
    + (786432 : F) * a4 ^ 3 * b3 * h ^ 50
    + (11468800 : F) * a4 ^ 2 * a3 ^ 3 * h ^ 48
    - (6881280 : F) * a4 ^ 2 * a3 ^ 2 * b7 * h ^ 44
    - (15728640 : F) * a4 ^ 2 * a3 * a2 * b8 * h ^ 44
    + (5898240 : F) * a4 ^ 2 * a3 * a1 * lambda * h ^ 53
    - (19660800 : F) * a4 ^ 2 * a3 * a0 * h ^ 54
    + (3145728 : F) * a4 ^ 2 * a3 * b4 * h ^ 50
    + (2949120 : F) * a4 ^ 2 * a2 ^ 2 * lambda * h ^ 53
    - (19660800 : F) * a4 ^ 2 * a2 * a1 * h ^ 54
    + (3932160 : F) * a4 ^ 2 * a2 * b5 * h ^ 50
    + (4718592 : F) * a4 ^ 2 * a1 * b6 * h ^ 50
    + (5505024 : F) * a4 ^ 2 * a0 * b7 * h ^ 50
    - (524288 : F) * a4 ^ 2 * b1 * h ^ 56
    - (5242880 : F) * a4 * a3 ^ 3 * b8 * h ^ 44
    + (5898240 : F) * a4 * a3 ^ 2 * a2 * lambda * h ^ 53
    - (19660800 : F) * a4 * a3 ^ 2 * a1 * h ^ 54
    + (3932160 : F) * a4 * a3 ^ 2 * b5 * h ^ 50
    - (19660800 : F) * a4 * a3 * a2 ^ 2 * h ^ 54
    + (9437184 : F) * a4 * a3 * a2 * b6 * h ^ 50
    + (11010048 : F) * a4 * a3 * a1 * b7 * h ^ 50
    + (12582912 : F) * a4 * a3 * a0 * b8 * h ^ 50
    - (2097152 : F) * a4 * a3 * b2 * h ^ 56
    + (5505024 : F) * a4 * a2 ^ 2 * b7 * h ^ 50
    + (12582912 : F) * a4 * a2 * a1 * b8 * h ^ 50
    - (4718592 : F) * a4 * a2 * a0 * lambda * h ^ 59
    - (3145728 : F) * a4 * a2 * b3 * h ^ 56
    - (2359296 : F) * a4 * a1 ^ 2 * lambda * h ^ 59
    + (15728640 : F) * a4 * a1 * a0 * h ^ 60
    - (4194304 : F) * a4 * a1 * b4 * h ^ 56
    - (5242880 : F) * a4 * a0 * b5 * h ^ 56
    + (491520 : F) * a3 ^ 4 * lambda * h ^ 53
    - (6553600 : F) * a3 ^ 3 * a2 * h ^ 54
    + (1572864 : F) * a3 ^ 3 * b6 * h ^ 50
    + (5505024 : F) * a3 ^ 2 * a2 * b7 * h ^ 50
    + (6291456 : F) * a3 ^ 2 * a1 * b8 * h ^ 50
    - (2359296 : F) * a3 ^ 2 * a0 * lambda * h ^ 59
    - (1572864 : F) * a3 ^ 2 * b3 * h ^ 56
    + (6291456 : F) * a3 * a2 ^ 2 * b8 * h ^ 50
    - (4718592 : F) * a3 * a2 * a1 * lambda * h ^ 59
    + (15728640 : F) * a3 * a2 * a0 * h ^ 60
    - (4194304 : F) * a3 * a2 * b4 * h ^ 56
    + (7864320 : F) * a3 * a1 ^ 2 * h ^ 60
    - (5242880 : F) * a3 * a1 * b5 * h ^ 56
    - (6291456 : F) * a3 * a0 * b6 * h ^ 56
    - (786432 : F) * a2 ^ 3 * lambda * h ^ 59
    + (7864320 : F) * a2 ^ 2 * a1 * h ^ 60
    - (2621440 : F) * a2 ^ 2 * b5 * h ^ 56
    - (6291456 : F) * a2 * a1 * b6 * h ^ 56
    - (7340032 : F) * a2 * a0 * b7 * h ^ 56
    + (2097152 : F) * a2 * b1 * h ^ 62
    - (3670016 : F) * a1 ^ 2 * b7 * h ^ 56
    - (8388608 : F) * a1 * a0 * b8 * h ^ 56
    + (4194304 : F) * a1 * b2 * h ^ 62
    + (1572864 : F) * a0 ^ 2 * lambda * h ^ 65
    + (6291456 : F) * a0 * b3 * h ^ 62 := by
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
  have h24 : (24 : F) ≠ 0 := by norm_num
  have h108 : (108 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h162 : (162 : F) ≠ 0 := by norm_num
  have h576 : (576 : F) ≠ 0 := by norm_num
  have h972 : (972 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h1458 : (1458 : F) ≠ 0 := by norm_num
  have h3456 : (3456 : F) ≠ 0 := by norm_num
  have h15552 : (15552 : F) ≠ 0 := by norm_num
  have h12582912 : (12582912 : F) ≠ 0 := by norm_num
  have hh65 : h ^ 65 ≠ 0 := pow_ne_zero 65 hh
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
    speedBridgeMuResidual610Scaled65_eq h hh]
  unfold speedBridgeMuResidual610Scaled65
  ring

end BridgeMuDepression610

end Max11DegreeRoutes
