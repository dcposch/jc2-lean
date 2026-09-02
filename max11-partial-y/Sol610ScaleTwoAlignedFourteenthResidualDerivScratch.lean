import Sol610ScaleTwoAlignedFourteenthTailRecurrenceScratch

/-! # Exact differential certificate for the aligned `(6,10)` weight-70 tail

This file consumes the depressed differential-Jacobian rows without changing
the normalized source or choosing a new witness.  The multipliers are the
exact sparse certificate obtained from the fourth Laurent-tail recurrence.
Row two has zero multiplier; every other row from degree thirteen through
degree one is used.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000

section FourteenthResidualDifferentialCertificate610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- The exact algebraic certificate behind the fourth-tail differential
recurrence.  These are precisely the coefficient rows of a depressed monic
sextic and monic decic after `d L = 0`. -/
theorem fourteenthResidual610_deriv_zero_of_depressed_rows
    (d : Derivation k F F)
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (h13 : (10 : F) * d A - 6 * d P = 0)
    (h12 : (9 : F) * L * d A + 10 * d B - 6 * d Q = 0)
    (h11 : -(4 : F) * A * d P + 9 * L * d B + 8 * P * d A +
        10 * d C0 - 6 * d R = 0)
    (h10 : -(4 : F) * A * d Q - 3 * B * d P + 9 * L * d C0 +
        8 * P * d B + 7 * Q * d A + 10 * d D0 - 6 * d S0 = 0)
    (h9 : -(4 : F) * A * d R - 3 * B * d Q - 2 * C0 * d P +
        9 * L * d D0 + 8 * P * d C0 + 7 * Q * d B + 6 * R * d A +
        10 * d E0 - 6 * d T0 = 0)
    (h8 : -(4 : F) * A * d S0 - 3 * B * d R - 2 * C0 * d Q -
        D0 * d P + 9 * L * d E0 + 8 * P * d D0 + 7 * Q * d C0 +
        6 * R * d B + 5 * S0 * d A - 6 * d U0 = 0)
    (h7 : -(4 : F) * A * d T0 - 3 * B * d S0 - 2 * C0 * d R -
        D0 * d Q + 8 * P * d E0 + 7 * Q * d D0 + 6 * R * d C0 +
        5 * S0 * d B + 4 * T0 * d A - 6 * d V0 = 0)
    (h6 : -(4 : F) * A * d U0 - 3 * B * d T0 - 2 * C0 * d S0 -
        D0 * d R + 7 * Q * d E0 + 6 * R * d D0 + 5 * S0 * d C0 +
        4 * T0 * d B + 3 * U0 * d A - 6 * d W0 = 0)
    (h5 : -(4 : F) * A * d V0 - 3 * B * d U0 - 2 * C0 * d T0 -
        D0 * d S0 + 6 * R * d E0 + 5 * S0 * d D0 + 4 * T0 * d C0 +
        3 * U0 * d B + 2 * V0 * d A - 6 * d X0 = 0)
    (h4 : -(4 : F) * A * d W0 - 3 * B * d V0 - 2 * C0 * d U0 -
        D0 * d T0 + 5 * S0 * d E0 + 4 * T0 * d D0 + 3 * U0 * d C0 +
        2 * V0 * d B + W0 * d A = 0)
    (h3 : -(4 : F) * A * d X0 - 3 * B * d W0 - 2 * C0 * d V0 -
        D0 * d U0 + 4 * T0 * d E0 + 3 * U0 * d D0 + 2 * V0 * d C0 +
        W0 * d B = 0)
    (h1 : -(2 : F) * C0 * d X0 - D0 * d W0 + 2 * V0 * d E0 +
        W0 * d D0 = 0) :
    d (fourteenthResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0 := by
  have hn1 : d (1 : F) = 0 := by
    simpa only [Nat.cast_one] using d.map_natCast 1
  have hn2 : d (2 : F) = 0 := d.map_natCast 2
  have hn3 : d (3 : F) = 0 := d.map_natCast 3
  have hn4 : d (4 : F) = 0 := d.map_natCast 4
  have hn5 : d (5 : F) = 0 := d.map_natCast 5
  have hn6 : d (6 : F) = 0 := d.map_natCast 6
  have hn7 : d (7 : F) = 0 := d.map_natCast 7
  have hn8 : d (8 : F) = 0 := d.map_natCast 8
  have hn9 : d (9 : F) = 0 := d.map_natCast 9
  have hn10 : d (10 : F) = 0 := d.map_natCast 10
  have hn11 : d (11 : F) = 0 := d.map_natCast 11
  have hn14 : d (14 : F) = 0 := d.map_natCast 14
  have hn15 : d (15 : F) = 0 := d.map_natCast 15
  have hn16 : d (16 : F) = 0 := d.map_natCast 16
  have hn18 : d (18 : F) = 0 := d.map_natCast 18
  have hn20 : d (20 : F) = 0 := d.map_natCast 20
  have hn21 : d (21 : F) = 0 := d.map_natCast 21
  have hn25 : d (25 : F) = 0 := d.map_natCast 25
  have hn27 : d (27 : F) = 0 := d.map_natCast 27
  have hn32 : d (32 : F) = 0 := d.map_natCast 32
  have hn35 : d (35 : F) = 0 := d.map_natCast 35
  have hn36 : d (36 : F) = 0 := d.map_natCast 36
  have hn40 : d (40 : F) = 0 := d.map_natCast 40
  have hn44 : d (44 : F) = 0 := d.map_natCast 44
  have hn45 : d (45 : F) = 0 := d.map_natCast 45
  have hn55 : d (55 : F) = 0 := d.map_natCast 55
  have hn56 : d (56 : F) = 0 := d.map_natCast 56
  have hn64 : d (64 : F) = 0 := d.map_natCast 64
  have hn65 : d (65 : F) = 0 := d.map_natCast 65
  have hn70 : d (70 : F) = 0 := d.map_natCast 70
  have hn72 : d (72 : F) = 0 := d.map_natCast 72
  have hn80 : d (80 : F) = 0 := d.map_natCast 80
  have hn81 : d (81 : F) = 0 := d.map_natCast 81
  have hn100 : d (100 : F) = 0 := d.map_natCast 100
  have hn128 : d (128 : F) = 0 := d.map_natCast 128
  have hn140 : d (140 : F) = 0 := d.map_natCast 140
  have hn175 : d (175 : F) = 0 := d.map_natCast 175
  have hn216 : d (216 : F) = 0 := d.map_natCast 216
  have hn243 : d (243 : F) = 0 := d.map_natCast 243
  have hn256 : d (256 : F) = 0 := d.map_natCast 256
  have hn385 : d (385 : F) = 0 := d.map_natCast 385
  have hn432 : d (432 : F) = 0 := d.map_natCast 432
  have hn455 : d (455 : F) = 0 := d.map_natCast 455
  have hn512 : d (512 : F) = 0 := d.map_natCast 512
  have hn729 : d (729 : F) = 0 := d.map_natCast 729
  have hn1296 : d (1296 : F) = 0 := d.map_natCast 1296
  have hn2187 : d (2187 : F) = 0 := d.map_natCast 2187
  have hn2592 : d (2592 : F) = 0 := d.map_natCast 2592
  have hn6545 : d (6545 : F) = 0 := d.map_natCast 6545
  have hn6561 : d (6561 : F) = 0 := d.map_natCast 6561
  have hn7776 : d (7776 : F) = 0 := d.map_natCast 7776
  have hn19683 : d (19683 : F) = 0 := d.map_natCast 19683
  have hn31104 : d (31104 : F) = 0 := d.map_natCast 31104
  have hn186624 : d (186624 : F) = 0 := d.map_natCast 186624
  simp only [fourteenthResidual610, rawFourthTailCoefficient610,
    rawFourthTailPure610, rawFourthTailLBlock610,
    rawFourthTailAlphaBlock610, rawFourthTailBetaBlock610,
    rawFourthTailDeltaBlock610, rawFourthTailEpsilonBlock610,
    rawFourthTailEtaBlock610, rawFourthTailThetaBlock610,
    rawFourthTailZetaBlock610, alphaResidual610, betaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, thetaResidual610, kappaResidual610, lambdaResidual610,
    gammaResidual610, map_add, map_sub, map_neg, Derivation.leibniz,
    Derivation.leibniz_pow, Derivation.leibniz_div,
    hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn14,
    hn15, hn16, hn18, hn20, hn21, hn25, hn27, hn32, hn35, hn36, hn40,
    hn44, hn45, hn55, hn56, hn64, hn65, hn70, hn72, hn80, hn81, hn100,
    hn128, hn140, hn175, hn216, hn243, hn256, hn385, hn432, hn455,
    hn512, hn729, hn1296, hn2187, hn2592, hn6545, hn6561, hn7776,
    hn19683, hn31104, hn186624, hL, nsmul_eq_mul, smul_eq_mul, zero_mul, mul_zero,
    zero_add, add_zero]
  linear_combination
    ((728 * A ^ 6 - 4095 * A ^ 4 * C0 - 8190 * A ^ 3 * B ^ 2 +
        3780 * A ^ 3 * E0 + 11340 * A ^ 2 * B * D0 +
        5670 * A ^ 2 * C0 ^ 2 + 11340 * A * B ^ 2 * C0 -
        6804 * A * C0 * E0 - 3402 * A * D0 ^ 2 + 945 * B ^ 4 -
        3402 * B ^ 2 * E0 - 6804 * B * C0 * D0 - 1134 * C0 ^ 3 +
        1458 * E0 ^ 2) / 39366 : F) * h13 -
    ((455 * A ^ 4 * B - 420 * A ^ 3 * D0 - 1260 * A ^ 2 * B * C0 -
        420 * A * B ^ 3 + 756 * A * B * E0 + 756 * A * C0 * D0 +
        378 * B ^ 2 * D0 + 378 * B * C0 ^ 2 - 324 * D0 * E0) /
        4374 : F) * h12 -
    ((91 * A ^ 5 - 420 * A ^ 3 * C0 - 630 * A ^ 2 * B ^ 2 +
        378 * A ^ 2 * E0 + 756 * A * B * D0 + 378 * A * C0 ^ 2 +
        378 * B ^ 2 * C0 - 324 * C0 * E0 - 162 * D0 ^ 2) /
        4374 : F) * h11 +
    ((70 * A ^ 3 * B - 63 * A ^ 2 * D0 - 126 * A * B * C0 -
        21 * B ^ 3 + 54 * B * E0 + 54 * C0 * D0) / 729 : F) * h10 +
    ((35 * A ^ 4 - 126 * A ^ 2 * C0 - 126 * A * B ^ 2 +
        108 * A * E0 + 108 * B * D0 + 54 * C0 ^ 2) / 1458 : F) * h9 -
    ((7 * A ^ 2 * B - 6 * A * D0 - 6 * B * C0) / 81 : F) * h8 -
    ((14 * A ^ 3 - 36 * A * C0 - 18 * B ^ 2 + 27 * E0) / 486 : F) * h7 +
    ((4 * A * B - 3 * D0) / 54 : F) * h6 +
    ((2 * A ^ 2 - 3 * C0) / 54 : F) * h5 -
    (B / 18 : F) * h4 - (A / 18 : F) * h3 + (1 / 6 : F) * h1

#print axioms fourteenthResidual610_deriv_zero_of_depressed_rows

end FourteenthResidualDifferentialCertificate610

end Max11DegreeRoutes
