import Sol810PiSourceClearingDraftScratch

/-! # Polynomial-uniform unsolved left jet for the 810 pi numerator

This file makes only the six displayed valuation substitutions.  In
particular it does not insert any scalar load solve, so its order-96
factorization remains valid when first-order deviations are retained. -/

noncomputable section

namespace Max11DegreeRoutes

open scoped Polynomial

set_option maxRecDepth 1000000

section PiLeftUnsolvedBlocks810

variable {R : Type*} [CommRing R]

/-- Order-96 head contributed by source block 0. -/
def piLeftUnsolvedHeadBlock0_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Quotient tail contributed by source block 0. -/
def piLeftUnsolvedTailBlock0_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (21990232555520 : R) * h ^ 15 * a0 ^ 2
    + (9895604649984 : R) * h ^ 14 * a1 * a0 * lambda
    + (5497558138880 : R) * h ^ 13 * t0 * a1 * a0
    + (17592186044416 : R) * h ^ 13 * a1 * b1
    + (35184372088832 : R) * h ^ 13 * a0 * b2
    - (12369505812480 : R) * h ^ 12 * t0 * a2 * a0 * lambda
    - (6184752906240 : R) * h ^ 12 * t0 * a1 ^ 2 * lambda
    - (4398046511104 : R) * h ^ 11 * t0 * a2 * b1
    - (8796093022208 : R) * h ^ 11 * t0 * a1 * b2
    - (13194139533312 : R) * h ^ 11 * t0 * a0 * b3
    + (54975581388800 : R) * h ^ 11 * v1 * a2 * a0
    + (27487790694400 : R) * h ^ 11 * v1 * a1 ^ 2
    - (12369505812480 : R) * h ^ 10 * v1 * a3 * a0 * lambda
    - (12369505812480 : R) * h ^ 10 * v1 * a2 * a1 * lambda
    - (4398046511104 : R) * h ^ 9 * v1 * a3 * b1
    - (8796093022208 : R) * h ^ 9 * v1 * a2 * b2
    - (13194139533312 : R) * h ^ 9 * v1 * a1 * b3
    - (17592186044416 : R) * h ^ 9 * v1 * a0 * b4
    + (54975581388800 : R) * h ^ 9 * u1 * a3 * a0
    + (54975581388800 : R) * h ^ 9 * u1 * a2 * a1
    - (12369505812480 : R) * h ^ 8 * u1 * a4 * a0 * lambda
    - (12369505812480 : R) * h ^ 8 * u1 * a3 * a1 * lambda
    - (6184752906240 : R) * h ^ 8 * u1 * a2 ^ 2 * lambda
    - (4398046511104 : R) * h ^ 7 * u1 * a4 * b1
    - (8796093022208 : R) * h ^ 7 * u1 * a3 * b2
    - (13194139533312 : R) * h ^ 7 * u1 * a2 * b3
    - (17592186044416 : R) * h ^ 7 * u1 * a1 * b4
    - (21990232555520 : R) * h ^ 7 * u1 * a0 * b5
    + (27487790694400 : R) * h ^ 7 * a4 ^ 2 * a0
    + (54975581388800 : R) * h ^ 7 * a4 * a3 * a1
    + (27487790694400 : R) * h ^ 7 * a4 * a2 ^ 2
    - (26388279066624 : R) * h ^ 7 * a4 * a0 * b62
    + (27487790694400 : R) * h ^ 7 * a3 ^ 2 * a2
    - (6184752906240 : R) * h ^ 6 * a4 ^ 2 * a1 * lambda
    - (12369505812480 : R) * h ^ 6 * a4 * a3 * a2 * lambda
    - (2061584302080 : R) * h ^ 6 * a3 ^ 3 * lambda
    - (4398046511104 : R) * h ^ 5 * a4 ^ 2 * b2
    - (13194139533312 : R) * h ^ 5 * a4 * a3 * b3
    - (17592186044416 : R) * h ^ 5 * a4 * a2 * b4
    - (21990232555520 : R) * h ^ 5 * a4 * a1 * b5

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock0_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock0_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock0_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock0_810,
    piLeftUnsolvedHeadBlock0_810, piLeftUnsolvedTailBlock0_810]
  ring

/-- Order-96 head contributed by source block 1. -/
def piLeftUnsolvedHeadBlock1_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5153960755200 : R) * a4 ^ 4

/-- Quotient tail contributed by source block 1. -/
def piLeftUnsolvedTailBlock1_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (35184372088832 : R) * h ^ 11 * a2 * a0 * s1
    - (17592186044416 : R) * h ^ 11 * a1 ^ 2 * s1
    + (13915694039040 : R) * h ^ 10 * t0 ^ 2 * a3 * a0 * lambda
    + (13915694039040 : R) * h ^ 10 * t0 ^ 2 * a2 * a1 * lambda
    - (61847529062400 : R) * h ^ 9 * t0 * v1 * a3 * a0
    - (61847529062400 : R) * h ^ 9 * t0 * v1 * a2 * a1
    - (30786325577728 : R) * h ^ 9 * a3 * a0 * w1
    - (30786325577728 : R) * h ^ 9 * a2 * a1 * w1
    + (27831388078080 : R) * h ^ 8 * t0 * v1 * a4 * a0 * lambda
    + (27831388078080 : R) * h ^ 8 * t0 * v1 * a3 * a1 * lambda
    + (13915694039040 : R) * h ^ 8 * t0 * v1 * a2 ^ 2 * lambda
    + (13915694039040 : R) * h ^ 8 * t0 * u1 ^ 2 * a0 * lambda
    + (13915694039040 : R) * h ^ 8 * v1 ^ 2 * u1 * a0 * lambda
    - (61847529062400 : R) * h ^ 7 * t0 * u1 * a4 * a0
    - (61847529062400 : R) * h ^ 7 * t0 * u1 * a3 * a1
    - (30923764531200 : R) * h ^ 7 * t0 * u1 * a2 ^ 2
    - (61847529062400 : R) * h ^ 7 * v1 ^ 2 * a4 * a0
    - (61847529062400 : R) * h ^ 7 * v1 ^ 2 * a3 * a1
    - (30923764531200 : R) * h ^ 7 * v1 ^ 2 * a2 ^ 2
    - (61847529062400 : R) * h ^ 7 * v1 * u1 ^ 2 * a0
    - (26388279066624 : R) * h ^ 7 * a3 * a1 * b62
    - (13194139533312 : R) * h ^ 7 * a2 ^ 2 * b62
    + (27831388078080 : R) * h ^ 6 * t0 * u1 * a4 * a1 * lambda
    + (27831388078080 : R) * h ^ 6 * t0 * u1 * a3 * a2 * lambda
    - (30923764531200 : R) * h ^ 5 * t0 * a4 ^ 2 * a1
    - (61847529062400 : R) * h ^ 5 * t0 * a4 * a3 * a2
    - (10307921510400 : R) * h ^ 5 * t0 * a3 ^ 3
    - (123695058124800 : R) * h ^ 5 * v1 * u1 * a4 * a1
    - (123695058124800 : R) * h ^ 5 * v1 * u1 * a3 * a2
    - (20615843020800 : R) * h ^ 5 * u1 ^ 3 * a1
    - (8796093022208 : R) * h ^ 5 * a3 ^ 2 * b4
    - (21990232555520 : R) * h ^ 5 * a3 * a2 * b5
    + (13915694039040 : R) * h ^ 4 * t0 * a4 ^ 2 * a2 * lambda
    + (13915694039040 : R) * h ^ 4 * t0 * a4 * a3 ^ 2 * lambda
    - (61847529062400 : R) * h ^ 3 * v1 * a4 ^ 2 * a2
    - (61847529062400 : R) * h ^ 3 * v1 * a4 * a3 ^ 2
    - (61847529062400 : R) * h ^ 3 * u1 ^ 2 * a4 * a2
    - (30923764531200 : R) * h ^ 3 * u1 ^ 2 * a3 ^ 2
    - (61847529062400 : R) * h * u1 * a4 ^ 2 * a3

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock1_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock1_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock1_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock1_810,
    piLeftUnsolvedHeadBlock1_810, piLeftUnsolvedTailBlock1_810]
  ring

/-- Order-96 head contributed by source block 2. -/
def piLeftUnsolvedHeadBlock2_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Quotient tail contributed by source block 2. -/
def piLeftUnsolvedTailBlock2_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2748779069440 : R) * h ^ 9 * t0 ^ 2 * a3 * b1
    + (5497558138880 : R) * h ^ 9 * t0 ^ 2 * a2 * b2
    + (8246337208320 : R) * h ^ 9 * t0 ^ 2 * a1 * b3
    + (10995116277760 : R) * h ^ 9 * t0 ^ 2 * a0 * b4
    + (43980465111040 : R) * h ^ 9 * t0 * a3 * a0 * s1
    + (43980465111040 : R) * h ^ 9 * t0 * a2 * a1 * s1
    + (5497558138880 : R) * h ^ 7 * t0 * v1 * a4 * b1
    + (10995116277760 : R) * h ^ 7 * t0 * v1 * a3 * b2
    + (16492674416640 : R) * h ^ 7 * t0 * v1 * a2 * b3
    + (21990232555520 : R) * h ^ 7 * t0 * v1 * a1 * b4
    + (27487790694400 : R) * h ^ 7 * t0 * v1 * a0 * b5
    + (2748779069440 : R) * h ^ 7 * t0 * u1 ^ 2 * b1
    + (32985348833280 : R) * h ^ 7 * t0 * u1 * a0 * b62
    + (38482906972160 : R) * h ^ 7 * t0 * a4 * a0 * w1
    + (38482906972160 : R) * h ^ 7 * t0 * a3 * a1 * w1
    + (19241453486080 : R) * h ^ 7 * t0 * a2 ^ 2 * w1
    + (2748779069440 : R) * h ^ 7 * v1 ^ 2 * u1 * b1
    + (13915694039040 : R) * h ^ 6 * v1 ^ 2 * a4 * a1 * lambda
    + (13915694039040 : R) * h ^ 6 * v1 ^ 2 * a3 * a2 * lambda
    + (13915694039040 : R) * h ^ 6 * v1 * u1 ^ 2 * a1 * lambda
    + (10995116277760 : R) * h ^ 5 * t0 * u1 * a4 * b2
    + (16492674416640 : R) * h ^ 5 * t0 * u1 * a3 * b3
    + (21990232555520 : R) * h ^ 5 * t0 * u1 * a2 * b4
    + (27487790694400 : R) * h ^ 5 * t0 * u1 * a1 * b5
    + (32985348833280 : R) * h ^ 5 * t0 * a4 * a1 * b62
    + (32985348833280 : R) * h ^ 5 * t0 * a3 * a2 * b62
    + (5497558138880 : R) * h ^ 5 * v1 ^ 2 * a4 * b2
    + (8246337208320 : R) * h ^ 5 * v1 ^ 2 * a3 * b3
    + (10995116277760 : R) * h ^ 5 * v1 ^ 2 * a2 * b4
    + (13743895347200 : R) * h ^ 5 * v1 ^ 2 * a1 * b5
    + (27831388078080 : R) * h ^ 4 * v1 * u1 * a4 * a2 * lambda
    + (13915694039040 : R) * h ^ 4 * v1 * u1 * a3 ^ 2 * lambda
    + (4638564679680 : R) * h ^ 4 * u1 ^ 3 * a2 * lambda
    + (8246337208320 : R) * h ^ 3 * t0 * a4 ^ 2 * b3
    + (21990232555520 : R) * h ^ 3 * t0 * a4 * a3 * b4
    + (27487790694400 : R) * h ^ 3 * t0 * a4 * a2 * b5
    + (13743895347200 : R) * h ^ 3 * t0 * a3 ^ 2 * b5
    + (13915694039040 : R) * h ^ 2 * v1 * a4 ^ 2 * a3 * lambda
    + (13915694039040 : R) * h ^ 2 * u1 ^ 2 * a4 * a3 * lambda
    + (4638564679680 : R) * u1 * a4 ^ 3 * lambda

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock2_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock2_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock2_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock2_810,
    piLeftUnsolvedHeadBlock2_810, piLeftUnsolvedTailBlock2_810]
  ring

/-- Order-96 head contributed by source block 3. -/
def piLeftUnsolvedHeadBlock3_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (13743895347200 : R) * u1 * a4 ^ 2 * b5
    + (5497558138880 : R) * a4 ^ 3 * b62

/-- Quotient tail contributed by source block 3. -/
def piLeftUnsolvedTailBlock3_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2576980377600 : R) * h ^ 9 * t0 ^ 3 * a3 * a0
    - (2576980377600 : R) * h ^ 9 * t0 ^ 3 * a2 * a1
    + (61847529062400 : R) * h ^ 7 * t0 ^ 2 * v1 * a4 * a0
    + (61847529062400 : R) * h ^ 7 * t0 ^ 2 * v1 * a3 * a1
    + (30923764531200 : R) * h ^ 7 * t0 ^ 2 * v1 * a2 ^ 2
    + (30923764531200 : R) * h ^ 7 * t0 ^ 2 * u1 ^ 2 * a0
    + (16492674416640 : R) * h ^ 7 * v1 ^ 2 * a0 * b62
    + (38482906972160 : R) * h ^ 7 * v1 * u1 * a0 * w1
    + (43980465111040 : R) * h ^ 7 * v1 * a4 * a0 * s1
    + (43980465111040 : R) * h ^ 7 * v1 * a3 * a1 * s1
    + (21990232555520 : R) * h ^ 7 * v1 * a2 ^ 2 * s1
    + (21990232555520 : R) * h ^ 7 * u1 ^ 2 * a0 * s1
    + (61847529062400 : R) * h ^ 5 * t0 ^ 2 * u1 * a4 * a1
    + (61847529062400 : R) * h ^ 5 * t0 ^ 2 * u1 * a3 * a2
    + (5497558138880 : R) * h ^ 5 * v1 * u1 ^ 2 * b2
    + (32985348833280 : R) * h ^ 5 * v1 * u1 * a1 * b62
    + (38482906972160 : R) * h ^ 5 * v1 * a4 * a1 * w1
    + (38482906972160 : R) * h ^ 5 * v1 * a3 * a2 * w1
    + (19241453486080 : R) * h ^ 5 * u1 ^ 2 * a1 * w1
    + (43980465111040 : R) * h ^ 5 * u1 * a4 * a1 * s1
    + (43980465111040 : R) * h ^ 5 * u1 * a3 * a2 * s1
    + (16492674416640 : R) * h ^ 3 * v1 * u1 * a4 * b3
    + (21990232555520 : R) * h ^ 3 * v1 * u1 * a3 * b4
    + (27487790694400 : R) * h ^ 3 * v1 * u1 * a2 * b5
    + (32985348833280 : R) * h ^ 3 * v1 * a4 * a2 * b62
    + (16492674416640 : R) * h ^ 3 * v1 * a3 ^ 2 * b62
    + (2748779069440 : R) * h ^ 3 * u1 ^ 3 * b3
    + (16492674416640 : R) * h ^ 3 * u1 ^ 2 * a2 * b62
    + (38482906972160 : R) * h ^ 3 * u1 * a4 * a2 * w1
    + (19241453486080 : R) * h ^ 3 * u1 * a3 ^ 2 * w1
    + (21990232555520 : R) * h ^ 3 * a4 ^ 2 * a2 * s1
    + (21990232555520 : R) * h ^ 3 * a4 * a3 ^ 2 * s1
    + (10995116277760 : R) * h * v1 * a4 ^ 2 * b4
    + (27487790694400 : R) * h * v1 * a4 * a3 * b5
    + (10995116277760 : R) * h * u1 ^ 2 * a4 * b4
    + (13743895347200 : R) * h * u1 ^ 2 * a3 * b5
    + (32985348833280 : R) * h * u1 * a4 * a3 * b62
    + (19241453486080 : R) * h * a4 ^ 2 * a3 * w1

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock3_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock3_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock3_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock3_810,
    piLeftUnsolvedHeadBlock3_810, piLeftUnsolvedTailBlock3_810]
  ring

/-- Order-96 head contributed by source block 4. -/
def piLeftUnsolvedHeadBlock4_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (43808666419200 : R) * t0 * u1 * a4 ^ 3
    + (33500744908800 : R) * v1 ^ 2 * a4 ^ 3
    + (100502234726400 : R) * v1 * u1 ^ 2 * a4 ^ 2
    + (16750372454400 : R) * u1 ^ 4 * a4

/-- Quotient tail contributed by source block 4. -/
def piLeftUnsolvedTailBlock4_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (15075335208960 : R) * h ^ 8 * t0 ^ 3 * a4 * a0 * lambda
    - (15075335208960 : R) * h ^ 8 * t0 ^ 3 * a3 * a1 * lambda
    - (7537667604480 : R) * h ^ 8 * t0 ^ 3 * a2 ^ 2 * lambda
    - (45226005626880 : R) * h ^ 8 * t0 ^ 2 * v1 * u1 * a0 * lambda
    - (15075335208960 : R) * h ^ 8 * t0 * v1 ^ 3 * a0 * lambda
    + (131425999257600 : R) * h ^ 7 * t0 * v1 ^ 2 * u1 * a0
    + (16750372454400 : R) * h ^ 7 * v1 ^ 4 * a0
    - (45226005626880 : R) * h ^ 6 * t0 ^ 2 * v1 * a4 * a1 * lambda
    - (45226005626880 : R) * h ^ 6 * t0 ^ 2 * v1 * a3 * a2 * lambda
    - (22613002813440 : R) * h ^ 6 * t0 ^ 2 * u1 ^ 2 * a1 * lambda
    - (45226005626880 : R) * h ^ 6 * t0 * v1 ^ 2 * u1 * a1 * lambda
    + (131425999257600 : R) * h ^ 5 * t0 * v1 ^ 2 * a4 * a1
    + (131425999257600 : R) * h ^ 5 * t0 * v1 ^ 2 * a3 * a2
    + (131425999257600 : R) * h ^ 5 * t0 * v1 * u1 ^ 2 * a1
    + (67001489817600 : R) * h ^ 5 * v1 ^ 3 * u1 * a1
    - (45226005626880 : R) * h ^ 4 * t0 ^ 2 * u1 * a4 * a2 * lambda
    - (22613002813440 : R) * h ^ 4 * t0 ^ 2 * u1 * a3 ^ 2 * lambda
    - (45226005626880 : R) * h ^ 4 * t0 * v1 ^ 2 * a4 * a2 * lambda
    - (22613002813440 : R) * h ^ 4 * t0 * v1 ^ 2 * a3 ^ 2 * lambda
    - (45226005626880 : R) * h ^ 4 * t0 * v1 * u1 ^ 2 * a2 * lambda
    + (30923764531200 : R) * h ^ 3 * t0 ^ 2 * a4 ^ 2 * a2
    + (30923764531200 : R) * h ^ 3 * t0 ^ 2 * a4 * a3 ^ 2
    + (262851998515200 : R) * h ^ 3 * t0 * v1 * u1 * a4 * a2
    + (131425999257600 : R) * h ^ 3 * t0 * v1 * u1 * a3 ^ 2
    + (43808666419200 : R) * h ^ 3 * t0 * u1 ^ 3 * a2
    + (67001489817600 : R) * h ^ 3 * v1 ^ 3 * a4 * a2
    + (33500744908800 : R) * h ^ 3 * v1 ^ 3 * a3 ^ 2
    + (100502234726400 : R) * h ^ 3 * v1 ^ 2 * u1 ^ 2 * a2
    - (22613002813440 : R) * h ^ 2 * t0 ^ 2 * a4 ^ 2 * a3 * lambda
    - (90452011253760 : R) * h ^ 2 * t0 * v1 * u1 * a4 * a3 * lambda
    - (15075335208960 : R) * h ^ 2 * t0 * u1 ^ 3 * a3 * lambda
    + (131425999257600 : R) * h * t0 * v1 * a4 ^ 2 * a3
    + (131425999257600 : R) * h * t0 * u1 ^ 2 * a4 * a3
    + (201004469452800 : R) * h * v1 ^ 2 * u1 * a4 * a3
    + (67001489817600 : R) * h * v1 * u1 ^ 3 * a3
    - (15075335208960 : R) * t0 * v1 * a4 ^ 3 * lambda

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock4_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock4_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock4_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock4_810,
    piLeftUnsolvedHeadBlock4_810, piLeftUnsolvedTailBlock4_810]
  ring

/-- Order-96 head contributed by source block 5. -/
def piLeftUnsolvedHeadBlock5_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Quotient tail contributed by source block 5. -/
def piLeftUnsolvedTailBlock5_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2061584302080 : R) * h ^ 7 * t0 ^ 3 * a4 * b1
    - (4123168604160 : R) * h ^ 7 * t0 ^ 3 * a3 * b2
    - (6184752906240 : R) * h ^ 7 * t0 ^ 3 * a2 * b3
    - (8246337208320 : R) * h ^ 7 * t0 ^ 3 * a1 * b4
    - (10307921510400 : R) * h ^ 7 * t0 ^ 3 * a0 * b5
    - (6184752906240 : R) * h ^ 7 * t0 ^ 2 * v1 * u1 * b1
    - (37108517437440 : R) * h ^ 7 * t0 ^ 2 * v1 * a0 * b62
    - (43293270343680 : R) * h ^ 7 * t0 ^ 2 * u1 * a0 * w1
    - (49478023249920 : R) * h ^ 7 * t0 ^ 2 * a4 * a0 * s1
    - (49478023249920 : R) * h ^ 7 * t0 ^ 2 * a3 * a1 * s1
    - (24739011624960 : R) * h ^ 7 * t0 ^ 2 * a2 ^ 2 * s1
    - (2061584302080 : R) * h ^ 7 * t0 * v1 ^ 3 * b1
    - (3768833802240 : R) * h ^ 6 * v1 ^ 4 * a1 * lambda
    - (12369505812480 : R) * h ^ 5 * t0 ^ 2 * v1 * a4 * b2
    - (18554258718720 : R) * h ^ 5 * t0 ^ 2 * v1 * a3 * b3
    - (24739011624960 : R) * h ^ 5 * t0 ^ 2 * v1 * a2 * b4
    - (30923764531200 : R) * h ^ 5 * t0 ^ 2 * v1 * a1 * b5
    - (6184752906240 : R) * h ^ 5 * t0 ^ 2 * u1 ^ 2 * b2
    - (37108517437440 : R) * h ^ 5 * t0 ^ 2 * u1 * a1 * b62
    - (43293270343680 : R) * h ^ 5 * t0 ^ 2 * a4 * a1 * w1
    - (43293270343680 : R) * h ^ 5 * t0 ^ 2 * a3 * a2 * w1
    - (12369505812480 : R) * h ^ 5 * t0 * v1 ^ 2 * u1 * b2
    - (37108517437440 : R) * h ^ 5 * t0 * v1 ^ 2 * a1 * b62
    - (15075335208960 : R) * h ^ 4 * v1 ^ 3 * u1 * a2 * lambda
    - (18554258718720 : R) * h ^ 3 * t0 ^ 2 * u1 * a4 * b3
    - (24739011624960 : R) * h ^ 3 * t0 ^ 2 * u1 * a3 * b4
    - (30923764531200 : R) * h ^ 3 * t0 ^ 2 * u1 * a2 * b5
    - (37108517437440 : R) * h ^ 3 * t0 ^ 2 * a4 * a2 * b62
    - (18554258718720 : R) * h ^ 3 * t0 ^ 2 * a3 ^ 2 * b62
    - (18554258718720 : R) * h ^ 3 * t0 * v1 ^ 2 * a4 * b3
    - (24739011624960 : R) * h ^ 3 * t0 * v1 ^ 2 * a3 * b4
    - (30923764531200 : R) * h ^ 3 * t0 * v1 ^ 2 * a2 * b5
    - (15075335208960 : R) * h ^ 2 * v1 ^ 3 * a4 * a3 * lambda
    - (22613002813440 : R) * h ^ 2 * v1 ^ 2 * u1 ^ 2 * a3 * lambda
    - (12369505812480 : R) * h * t0 ^ 2 * a4 ^ 2 * b4
    - (30923764531200 : R) * h * t0 ^ 2 * a4 * a3 * b5
    - (22613002813440 : R) * t0 * u1 ^ 2 * a4 ^ 2 * lambda
    - (22613002813440 : R) * v1 ^ 2 * u1 * a4 ^ 2 * lambda
    - (15075335208960 : R) * v1 * u1 ^ 3 * a4 * lambda
    - (753766760448 : R) * u1 ^ 5 * lambda

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock5_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock5_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock5_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock5_810,
    piLeftUnsolvedHeadBlock5_810, piLeftUnsolvedTailBlock5_810]
  ring

/-- Order-96 head contributed by source block 6. -/
def piLeftUnsolvedHeadBlock6_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (30923764531200 : R) * t0 * v1 * a4 ^ 2 * b5
    - (30923764531200 : R) * t0 * u1 ^ 2 * a4 * b5
    - (37108517437440 : R) * t0 * u1 * a4 ^ 2 * b62
    - (14431090114560 : R) * t0 * a4 ^ 3 * w1
    - (30923764531200 : R) * v1 ^ 2 * u1 * a4 * b5
    - (18554258718720 : R) * v1 ^ 2 * a4 ^ 2 * b62

/-- Quotient tail contributed by source block 6. -/
def piLeftUnsolvedTailBlock6_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (43293270343680 : R) * h ^ 7 * t0 * v1 ^ 2 * a0 * w1
    - (98956046499840 : R) * h ^ 7 * t0 * v1 * u1 * a0 * s1
    - (16492674416640 : R) * h ^ 7 * v1 ^ 3 * a0 * s1
    - (86586540687360 : R) * h ^ 5 * t0 * v1 * u1 * a1 * w1
    - (98956046499840 : R) * h ^ 5 * t0 * v1 * a4 * a1 * s1
    - (98956046499840 : R) * h ^ 5 * t0 * v1 * a3 * a2 * s1
    - (49478023249920 : R) * h ^ 5 * t0 * u1 ^ 2 * a1 * s1
    - (1030792151040 : R) * h ^ 5 * v1 ^ 4 * b2
    - (14431090114560 : R) * h ^ 5 * v1 ^ 3 * a1 * w1
    - (49478023249920 : R) * h ^ 5 * v1 ^ 2 * u1 * a1 * s1
    - (18554258718720 : R) * h ^ 3 * t0 * v1 * u1 ^ 2 * b3
    - (74217034874880 : R) * h ^ 3 * t0 * v1 * u1 * a2 * b62
    - (86586540687360 : R) * h ^ 3 * t0 * v1 * a4 * a2 * w1
    - (43293270343680 : R) * h ^ 3 * t0 * v1 * a3 ^ 2 * w1
    - (43293270343680 : R) * h ^ 3 * t0 * u1 ^ 2 * a2 * w1
    - (98956046499840 : R) * h ^ 3 * t0 * u1 * a4 * a2 * s1
    - (49478023249920 : R) * h ^ 3 * t0 * u1 * a3 ^ 2 * s1
    - (6184752906240 : R) * h ^ 3 * v1 ^ 3 * u1 * b3
    - (12369505812480 : R) * h ^ 3 * v1 ^ 3 * a2 * b62
    - (43293270343680 : R) * h ^ 3 * v1 ^ 2 * u1 * a2 * w1
    - (49478023249920 : R) * h ^ 3 * v1 ^ 2 * a4 * a2 * s1
    - (24739011624960 : R) * h ^ 3 * v1 ^ 2 * a3 ^ 2 * s1
    - (49478023249920 : R) * h * t0 * v1 * u1 * a4 * b4
    - (61847529062400 : R) * h * t0 * v1 * u1 * a3 * b5
    - (74217034874880 : R) * h * t0 * v1 * a4 * a3 * b62
    - (8246337208320 : R) * h * t0 * u1 ^ 3 * b4
    - (37108517437440 : R) * h * t0 * u1 ^ 2 * a3 * b62
    - (86586540687360 : R) * h * t0 * u1 * a4 * a3 * w1
    - (49478023249920 : R) * h * t0 * a4 ^ 2 * a3 * s1
    - (8246337208320 : R) * h * v1 ^ 3 * a4 * b4
    - (10307921510400 : R) * h * v1 ^ 3 * a3 * b5
    - (12369505812480 : R) * h * v1 ^ 2 * u1 ^ 2 * b4
    - (37108517437440 : R) * h * v1 ^ 2 * u1 * a3 * b62
    - (43293270343680 : R) * h * v1 ^ 2 * a4 * a3 * w1

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock6_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock6_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock6_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock6_810,
    piLeftUnsolvedHeadBlock6_810, piLeftUnsolvedTailBlock6_810]
  ring

/-- Order-96 head contributed by source block 7. -/
def piLeftUnsolvedHeadBlock7_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (67001489817600 : R) * t0 ^ 2 * v1 * a4 ^ 3
    - (100502234726400 : R) * t0 ^ 2 * u1 ^ 2 * a4 ^ 2
    - (314069483520000 : R) * t0 * v1 ^ 2 * u1 * a4 ^ 2
    - (209379655680000 : R) * t0 * v1 * u1 ^ 3 * a4
    - (10468982784000 : R) * t0 * u1 ^ 5
    - (35594541465600 : R) * v1 ^ 4 * a4 ^ 2
    - (10307921510400 : R) * v1 * u1 ^ 3 * b5
    - (37108517437440 : R) * v1 * u1 ^ 2 * a4 * b62
    - (43293270343680 : R) * v1 * u1 * a4 ^ 2 * w1
    - (16492674416640 : R) * v1 * a4 ^ 3 * s1
    - (3092376453120 : R) * u1 ^ 4 * b62
    - (14431090114560 : R) * u1 ^ 3 * a4 * w1
    - (24739011624960 : R) * u1 ^ 2 * a4 ^ 2 * s1

/-- Quotient tail contributed by source block 7. -/
def piLeftUnsolvedTailBlock7_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (4187593113600 : R) * h ^ 7 * t0 ^ 4 * a4 * a0
    + (4187593113600 : R) * h ^ 7 * t0 ^ 4 * a3 * a1
    + (2093796556800 : R) * h ^ 7 * t0 ^ 4 * a2 ^ 2
    - (58626303590400 : R) * h ^ 7 * t0 ^ 3 * v1 * u1 * a0
    - (67001489817600 : R) * h ^ 7 * t0 ^ 2 * v1 ^ 3 * a0
    - (58626303590400 : R) * h ^ 5 * t0 ^ 3 * v1 * a4 * a1
    - (58626303590400 : R) * h ^ 5 * t0 ^ 3 * v1 * a3 * a2
    - (29313151795200 : R) * h ^ 5 * t0 ^ 3 * u1 ^ 2 * a1
    - (201004469452800 : R) * h ^ 5 * t0 ^ 2 * v1 ^ 2 * u1 * a1
    - (52344913920000 : R) * h ^ 5 * t0 * v1 ^ 4 * a1
    - (58626303590400 : R) * h ^ 3 * t0 ^ 3 * u1 * a4 * a2
    - (29313151795200 : R) * h ^ 3 * t0 ^ 3 * u1 * a3 ^ 2
    - (201004469452800 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 2 * a4 * a2
    - (100502234726400 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 2 * a3 ^ 2
    - (201004469452800 : R) * h ^ 3 * t0 ^ 2 * v1 * u1 ^ 2 * a2
    - (209379655680000 : R) * h ^ 3 * t0 * v1 ^ 3 * u1 * a2
    - (14237816586240 : R) * h ^ 3 * v1 ^ 5 * a2
    - (49478023249920 : R) * h ^ 3 * v1 * u1 ^ 2 * a2 * s1
    - (29313151795200 : R) * h * t0 ^ 3 * a4 ^ 2 * a3
    - (402008938905600 : R) * h * t0 ^ 2 * v1 * u1 * a4 * a3
    - (67001489817600 : R) * h * t0 ^ 2 * u1 ^ 3 * a3
    - (209379655680000 : R) * h * t0 * v1 ^ 3 * a4 * a3
    - (314069483520000 : R) * h * t0 * v1 ^ 2 * u1 ^ 2 * a3
    - (71189082931200 : R) * h * v1 ^ 4 * u1 * a3
    - (43293270343680 : R) * h * v1 * u1 ^ 2 * a3 * w1
    - (98956046499840 : R) * h * v1 * u1 * a4 * a3 * s1
    - (16492674416640 : R) * h * u1 ^ 3 * a3 * s1

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock7_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock7_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock7_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock7_810,
    piLeftUnsolvedHeadBlock7_810, piLeftUnsolvedTailBlock7_810]
  ring

/-- Order-96 head contributed by source block 8. -/
def piLeftUnsolvedHeadBlock8_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (142378165862400 : R) * v1 ^ 3 * u1 ^ 2 * a4
    - (35594541465600 : R) * v1 ^ 2 * u1 ^ 4

/-- Quotient tail contributed by source block 8. -/
def piLeftUnsolvedTailBlock8_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (16017543659520 : R) * h ^ 8 * t0 ^ 4 * u1 * a0 * lambda
    + (32035087319040 : R) * h ^ 8 * t0 ^ 3 * v1 ^ 2 * a0 * lambda
    + (1675037245440 : R) * h ^ 7 * t0 ^ 4 * u1 * b1
    + (10050223472640 : R) * h ^ 7 * t0 ^ 4 * a0 * b62
    + (3350074490880 : R) * h ^ 7 * t0 ^ 3 * v1 ^ 2 * b1
    + (46901042872320 : R) * h ^ 7 * t0 ^ 3 * v1 * a0 * w1
    + (16017543659520 : R) * h ^ 6 * t0 ^ 4 * a4 * a1 * lambda
    + (16017543659520 : R) * h ^ 6 * t0 ^ 4 * a3 * a2 * lambda
    + (64070174638080 : R) * h ^ 6 * t0 ^ 3 * v1 * u1 * a1 * lambda
    + (32035087319040 : R) * h ^ 6 * t0 ^ 2 * v1 ^ 3 * a1 * lambda
    + (3350074490880 : R) * h ^ 5 * t0 ^ 4 * a4 * b2
    + (5025111736320 : R) * h ^ 5 * t0 ^ 4 * a3 * b3
    + (6700148981760 : R) * h ^ 5 * t0 ^ 4 * a2 * b4
    + (8375186227200 : R) * h ^ 5 * t0 ^ 4 * a1 * b5
    + (13400297963520 : R) * h ^ 5 * t0 ^ 3 * v1 * u1 * b2
    + (40200893890560 : R) * h ^ 5 * t0 ^ 3 * v1 * a1 * b62
    + (64070174638080 : R) * h ^ 4 * t0 ^ 3 * v1 * a4 * a2 * lambda
    + (32035087319040 : R) * h ^ 4 * t0 ^ 3 * v1 * a3 ^ 2 * lambda
    + (32035087319040 : R) * h ^ 4 * t0 ^ 3 * u1 ^ 2 * a2 * lambda
    + (96105261957120 : R) * h ^ 4 * t0 ^ 2 * v1 ^ 2 * u1 * a2 * lambda
    + (16017543659520 : R) * h ^ 4 * t0 * v1 ^ 4 * a2 * lambda
    + (20100446945280 : R) * h ^ 3 * t0 ^ 3 * v1 * a4 * b3
    + (26800595927040 : R) * h ^ 3 * t0 ^ 3 * v1 * a3 * b4
    + (33500744908800 : R) * h ^ 3 * t0 ^ 3 * v1 * a2 * b5
    + (10050223472640 : R) * h ^ 3 * t0 ^ 3 * u1 ^ 2 * b3
    + (64070174638080 : R) * h ^ 2 * t0 ^ 3 * u1 * a4 * a3 * lambda
    + (96105261957120 : R) * h ^ 2 * t0 ^ 2 * v1 ^ 2 * a4 * a3 * lambda
    + (96105261957120 : R) * h ^ 2 * t0 ^ 2 * v1 * u1 ^ 2 * a3 * lambda
    + (64070174638080 : R) * h ^ 2 * t0 * v1 ^ 3 * u1 * a3 * lambda
    + (3203508731904 : R) * h ^ 2 * v1 ^ 5 * a3 * lambda
    + (10678362439680 : R) * t0 ^ 3 * a4 ^ 3 * lambda
    + (96105261957120 : R) * t0 ^ 2 * v1 * u1 * a4 ^ 2 * lambda
    + (32035087319040 : R) * t0 ^ 2 * u1 ^ 3 * a4 * lambda
    + (32035087319040 : R) * t0 * v1 ^ 3 * a4 ^ 2 * lambda
    + (96105261957120 : R) * t0 * v1 ^ 2 * u1 ^ 2 * a4 * lambda
    + (16017543659520 : R) * t0 * v1 * u1 ^ 4 * lambda
    + (16017543659520 : R) * v1 ^ 4 * u1 * a4 * lambda
    + (10678362439680 : R) * v1 ^ 3 * u1 ^ 3 * lambda

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock8_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock8_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock8_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock8_810,
    piLeftUnsolvedHeadBlock8_810, piLeftUnsolvedTailBlock8_810]
  ring

/-- Order-96 head contributed by source block 9. -/
def piLeftUnsolvedHeadBlock9_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (16750372454400 : R) * t0 ^ 3 * a4 ^ 2 * b5
    + (100502234726400 : R) * t0 ^ 2 * v1 * u1 * a4 * b5
    + (60301340835840 : R) * t0 ^ 2 * v1 * a4 ^ 2 * b62
    + (16750372454400 : R) * t0 ^ 2 * u1 ^ 3 * b5
    + (60301340835840 : R) * t0 ^ 2 * u1 ^ 2 * a4 * b62
    + (70351564308480 : R) * t0 ^ 2 * u1 * a4 ^ 2 * w1
    + (26800595927040 : R) * t0 ^ 2 * a4 ^ 3 * s1
    + (33500744908800 : R) * t0 * v1 ^ 3 * a4 * b5

/-- Quotient tail contributed by source block 9. -/
def piLeftUnsolvedTailBlock9_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (53601191854080 : R) * h ^ 7 * t0 ^ 3 * u1 * a0 * s1
    + (80401787781120 : R) * h ^ 7 * t0 ^ 2 * v1 ^ 2 * a0 * s1
    + (46901042872320 : R) * h ^ 5 * t0 ^ 3 * u1 * a1 * w1
    + (53601191854080 : R) * h ^ 5 * t0 ^ 3 * a4 * a1 * s1
    + (53601191854080 : R) * h ^ 5 * t0 ^ 3 * a3 * a2 * s1
    + (6700148981760 : R) * h ^ 5 * t0 ^ 2 * v1 ^ 3 * b2
    + (70351564308480 : R) * h ^ 5 * t0 ^ 2 * v1 ^ 2 * a1 * w1
    + (160803575562240 : R) * h ^ 5 * t0 ^ 2 * v1 * u1 * a1 * s1
    + (53601191854080 : R) * h ^ 5 * t0 * v1 ^ 3 * a1 * s1
    + (40200893890560 : R) * h ^ 3 * t0 ^ 3 * u1 * a2 * b62
    + (46901042872320 : R) * h ^ 3 * t0 ^ 3 * a4 * a2 * w1
    + (23450521436160 : R) * h ^ 3 * t0 ^ 3 * a3 ^ 2 * w1
    + (30150670417920 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 2 * u1 * b3
    + (60301340835840 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 2 * a2 * b62
    + (140703128616960 : R) * h ^ 3 * t0 ^ 2 * v1 * u1 * a2 * w1
    + (160803575562240 : R) * h ^ 3 * t0 ^ 2 * v1 * a4 * a2 * s1
    + (80401787781120 : R) * h ^ 3 * t0 ^ 2 * v1 * a3 ^ 2 * s1
    + (80401787781120 : R) * h ^ 3 * t0 ^ 2 * u1 ^ 2 * a2 * s1
    + (5025111736320 : R) * h ^ 3 * t0 * v1 ^ 4 * b3
    + (46901042872320 : R) * h ^ 3 * t0 * v1 ^ 3 * a2 * w1
    + (26800595927040 : R) * h * t0 ^ 3 * u1 * a4 * b4
    + (33500744908800 : R) * h * t0 ^ 3 * u1 * a3 * b5
    + (40200893890560 : R) * h * t0 ^ 3 * a4 * a3 * b62
    + (40200893890560 : R) * h * t0 ^ 2 * v1 ^ 2 * a4 * b4
    + (50251117363200 : R) * h * t0 ^ 2 * v1 ^ 2 * a3 * b5
    + (40200893890560 : R) * h * t0 ^ 2 * v1 * u1 ^ 2 * b4
    + (120602681671680 : R) * h * t0 ^ 2 * v1 * u1 * a3 * b62
    + (140703128616960 : R) * h * t0 ^ 2 * v1 * a4 * a3 * w1
    + (70351564308480 : R) * h * t0 ^ 2 * u1 ^ 2 * a3 * w1
    + (160803575562240 : R) * h * t0 ^ 2 * u1 * a4 * a3 * s1
    + (26800595927040 : R) * h * t0 * v1 ^ 3 * u1 * b4
    + (40200893890560 : R) * h * t0 * v1 ^ 3 * a3 * b62

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock9_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock9_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock9_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock9_810,
    piLeftUnsolvedHeadBlock9_810, piLeftUnsolvedTailBlock9_810]
  ring

/-- Order-96 head contributed by source block 10. -/
def piLeftUnsolvedHeadBlock10_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (8898635366400 : R) * t0 ^ 4 * a4 ^ 3
    + (266959060992000 : R) * t0 ^ 3 * v1 * u1 * a4 ^ 2
    + (88986353664000 : R) * t0 ^ 3 * u1 ^ 3 * a4
    + (50251117363200 : R) * t0 * v1 ^ 2 * u1 ^ 2 * b5
    + (120602681671680 : R) * t0 * v1 ^ 2 * u1 * a4 * b62
    + (70351564308480 : R) * t0 * v1 ^ 2 * a4 ^ 2 * w1
    + (40200893890560 : R) * t0 * v1 * u1 ^ 3 * b62
    + (140703128616960 : R) * t0 * v1 * u1 ^ 2 * a4 * w1
    + (160803575562240 : R) * t0 * v1 * u1 * a4 ^ 2 * s1
    + (11725260718080 : R) * t0 * u1 ^ 4 * w1
    + (53601191854080 : R) * t0 * u1 ^ 3 * a4 * s1
    + (8375186227200 : R) * v1 ^ 4 * u1 * b5
    + (10050223472640 : R) * v1 ^ 4 * a4 * b62
    + (20100446945280 : R) * v1 ^ 3 * u1 ^ 2 * b62
    + (46901042872320 : R) * v1 ^ 3 * u1 * a4 * w1
    + (26800595927040 : R) * v1 ^ 3 * a4 ^ 2 * s1
    + (23450521436160 : R) * v1 ^ 2 * u1 ^ 3 * w1
    + (80401787781120 : R) * v1 ^ 2 * u1 ^ 2 * a4 * s1
    + (13400297963520 : R) * v1 * u1 ^ 4 * s1

/-- Quotient tail contributed by source block 10. -/
def piLeftUnsolvedTailBlock10_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5339181219840 : R) * h ^ 7 * t0 ^ 5 * u1 * a0
    + (26695906099200 : R) * h ^ 7 * t0 ^ 4 * v1 ^ 2 * a0
    - (5339181219840 : R) * h ^ 5 * t0 ^ 5 * a4 * a1
    - (5339181219840 : R) * h ^ 5 * t0 ^ 5 * a3 * a2
    + (53391812198400 : R) * h ^ 5 * t0 ^ 4 * v1 * u1 * a1
    + (88986353664000 : R) * h ^ 5 * t0 ^ 3 * v1 ^ 3 * a1
    + (53391812198400 : R) * h ^ 3 * t0 ^ 4 * v1 * a4 * a2
    + (26695906099200 : R) * h ^ 3 * t0 ^ 4 * v1 * a3 ^ 2
    + (26695906099200 : R) * h ^ 3 * t0 ^ 4 * u1 ^ 2 * a2
    + (266959060992000 : R) * h ^ 3 * t0 ^ 3 * v1 ^ 2 * u1 * a2
    + (160803575562240 : R) * h ^ 3 * t0 * v1 ^ 2 * u1 * a2 * s1
    + (13400297963520 : R) * h ^ 3 * v1 ^ 4 * a2 * s1
    + (53391812198400 : R) * h * t0 ^ 4 * u1 * a4 * a3
    + (266959060992000 : R) * h * t0 ^ 3 * v1 ^ 2 * a4 * a3
    + (266959060992000 : R) * h * t0 ^ 3 * v1 * u1 ^ 2 * a3
    + (140703128616960 : R) * h * t0 * v1 ^ 2 * u1 * a3 * w1
    + (160803575562240 : R) * h * t0 * v1 ^ 2 * a4 * a3 * s1
    + (160803575562240 : R) * h * t0 * v1 * u1 ^ 2 * a3 * s1
    + (1340029796352 : R) * h * v1 ^ 5 * b4
    + (11725260718080 : R) * h * v1 ^ 4 * a3 * w1
    + (53601191854080 : R) * h * v1 ^ 3 * u1 * a3 * s1

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock10_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock10_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock10_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock10_810,
    piLeftUnsolvedHeadBlock10_810, piLeftUnsolvedTailBlock10_810]
  ring

/-- Order-96 head contributed by source block 11. -/
def piLeftUnsolvedHeadBlock11_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (213567248793600 : R) * t0 ^ 2 * v1 ^ 3 * a4 ^ 2
    + (640701746380800 : R) * t0 ^ 2 * v1 ^ 2 * u1 ^ 2 * a4
    + (106783624396800 : R) * t0 ^ 2 * v1 * u1 ^ 4
    + (293654967091200 : R) * t0 * v1 ^ 4 * u1 * a4
    + (195769978060800 : R) * t0 * v1 ^ 3 * u1 ^ 3
    + (12458089512960 : R) * v1 ^ 6 * a4
    + (37374268538880 : R) * v1 ^ 5 * u1 ^ 2

/-- Quotient tail contributed by source block 11. -/
def piLeftUnsolvedTailBlock11_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (16818420842496 : R) * h ^ 8 * t0 ^ 5 * v1 * a0 * lambda
    - (1423781658624 : R) * h ^ 7 * t0 ^ 5 * v1 * b1
    - (9966471610368 : R) * h ^ 7 * t0 ^ 5 * a0 * w1
    - (16818420842496 : R) * h ^ 6 * t0 ^ 5 * u1 * a1 * lambda
    - (42046052106240 : R) * h ^ 6 * t0 ^ 4 * v1 ^ 2 * a1 * lambda
    - (2847563317248 : R) * h ^ 5 * t0 ^ 5 * u1 * b2
    - (8542689951744 : R) * h ^ 5 * t0 ^ 5 * a1 * b62
    - (7118908293120 : R) * h ^ 5 * t0 ^ 4 * v1 ^ 2 * b2
    - (16818420842496 : R) * h ^ 4 * t0 ^ 5 * a4 * a2 * lambda
    - (8409210421248 : R) * h ^ 4 * t0 ^ 5 * a3 ^ 2 * lambda
    - (84092104212480 : R) * h ^ 4 * t0 ^ 4 * v1 * u1 * a2 * lambda
    - (56061402808320 : R) * h ^ 4 * t0 ^ 3 * v1 ^ 3 * a2 * lambda
    - (4271344975872 : R) * h ^ 3 * t0 ^ 5 * a4 * b3
    - (5695126634496 : R) * h ^ 3 * t0 ^ 5 * a3 * b4
    - (7118908293120 : R) * h ^ 3 * t0 ^ 5 * a2 * b5
    - (21356724879360 : R) * h ^ 3 * t0 ^ 4 * v1 * u1 * b3
    + (106783624396800 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 4 * a2
    - (84092104212480 : R) * h ^ 2 * t0 ^ 4 * v1 * a4 * a3 * lambda
    - (42046052106240 : R) * h ^ 2 * t0 ^ 4 * u1 ^ 2 * a3 * lambda
    - (168184208424960 : R) * h ^ 2 * t0 ^ 3 * v1 ^ 2 * u1 * a3 * lambda
    - (42046052106240 : R) * h ^ 2 * t0 ^ 2 * v1 ^ 4 * a3 * lambda
    - (28475633172480 : R) * h * t0 ^ 4 * v1 * a4 * b4
    + (427134497587200 : R) * h * t0 ^ 2 * v1 ^ 3 * u1 * a3
    + (58730993418240 : R) * h * t0 * v1 ^ 5 * a3
    - (42046052106240 : R) * t0 ^ 4 * u1 * a4 ^ 2 * lambda
    - (84092104212480 : R) * t0 ^ 3 * v1 ^ 2 * a4 ^ 2 * lambda
    - (168184208424960 : R) * t0 ^ 3 * v1 * u1 ^ 2 * a4 * lambda
    - (14015350702080 : R) * t0 ^ 3 * u1 ^ 4 * lambda
    - (168184208424960 : R) * t0 ^ 2 * v1 ^ 3 * u1 * a4 * lambda
    - (84092104212480 : R) * t0 ^ 2 * v1 ^ 2 * u1 ^ 3 * lambda
    - (16818420842496 : R) * t0 * v1 ^ 5 * a4 * lambda
    - (42046052106240 : R) * t0 * v1 ^ 4 * u1 ^ 2 * lambda
    - (2803070140416 : R) * v1 ^ 6 * u1 * lambda

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock11_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock11_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock11_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock11_810,
    piLeftUnsolvedHeadBlock11_810, piLeftUnsolvedTailBlock11_810]
  ring

/-- Order-96 head contributed by source block 12. -/
def piLeftUnsolvedHeadBlock12_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (35594541465600 : R) * t0 ^ 4 * u1 * a4 * b5
    - (21356724879360 : R) * t0 ^ 4 * a4 ^ 2 * b62
    - (71189082931200 : R) * t0 ^ 3 * v1 ^ 2 * a4 * b5
    - (71189082931200 : R) * t0 ^ 3 * v1 * u1 ^ 2 * b5
    - (170853799034880 : R) * t0 ^ 3 * v1 * u1 * a4 * b62
    - (99664716103680 : R) * t0 ^ 3 * v1 * a4 ^ 2 * w1
    - (28475633172480 : R) * t0 ^ 3 * u1 ^ 3 * b62
    - (99664716103680 : R) * t0 ^ 3 * u1 ^ 2 * a4 * w1
    - (113902532689920 : R) * t0 ^ 3 * u1 * a4 ^ 2 * s1
    - (71189082931200 : R) * t0 ^ 2 * v1 ^ 3 * u1 * b5
    - (85426899517440 : R) * t0 ^ 2 * v1 ^ 3 * a4 * b62
    - (128140349276160 : R) * t0 ^ 2 * v1 ^ 2 * u1 ^ 2 * b62
    - (298994148311040 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a4 * w1
    - (170853799034880 : R) * t0 ^ 2 * v1 ^ 2 * a4 ^ 2 * s1
    - (99664716103680 : R) * t0 ^ 2 * v1 * u1 ^ 3 * w1
    - (341707598069760 : R) * t0 ^ 2 * v1 * u1 ^ 2 * a4 * s1

/-- Quotient tail contributed by source block 12. -/
def piLeftUnsolvedTailBlock12_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (56951266344960 : R) * h ^ 7 * t0 ^ 4 * v1 * a0 * s1
    - (49832358051840 : R) * h ^ 5 * t0 ^ 4 * v1 * a1 * w1
    - (56951266344960 : R) * h ^ 5 * t0 ^ 4 * u1 * a1 * s1
    - (113902532689920 : R) * h ^ 5 * t0 ^ 3 * v1 ^ 2 * a1 * s1
    - (42713449758720 : R) * h ^ 3 * t0 ^ 4 * v1 * a2 * b62
    - (49832358051840 : R) * h ^ 3 * t0 ^ 4 * u1 * a2 * w1
    - (56951266344960 : R) * h ^ 3 * t0 ^ 4 * a4 * a2 * s1
    - (28475633172480 : R) * h ^ 3 * t0 ^ 4 * a3 ^ 2 * s1
    - (14237816586240 : R) * h ^ 3 * t0 ^ 3 * v1 ^ 3 * b3
    - (99664716103680 : R) * h ^ 3 * t0 ^ 3 * v1 ^ 2 * a2 * w1
    - (227805065379840 : R) * h ^ 3 * t0 ^ 3 * v1 * u1 * a2 * s1
    - (113902532689920 : R) * h ^ 3 * t0 ^ 2 * v1 ^ 3 * a2 * s1
    - (35594541465600 : R) * h * t0 ^ 4 * v1 * a3 * b5
    - (14237816586240 : R) * h * t0 ^ 4 * u1 ^ 2 * b4
    - (42713449758720 : R) * h * t0 ^ 4 * u1 * a3 * b62
    - (49832358051840 : R) * h * t0 ^ 4 * a4 * a3 * w1
    - (56951266344960 : R) * h * t0 ^ 3 * v1 ^ 2 * u1 * b4
    - (85426899517440 : R) * h * t0 ^ 3 * v1 ^ 2 * a3 * b62
    - (199329432207360 : R) * h * t0 ^ 3 * v1 * u1 * a3 * w1
    - (227805065379840 : R) * h * t0 ^ 3 * v1 * a4 * a3 * s1
    - (113902532689920 : R) * h * t0 ^ 3 * u1 ^ 2 * a3 * s1
    - (14237816586240 : R) * h * t0 ^ 2 * v1 ^ 4 * b4
    - (99664716103680 : R) * h * t0 ^ 2 * v1 ^ 3 * a3 * w1
    - (341707598069760 : R) * h * t0 ^ 2 * v1 ^ 2 * u1 * a3 * s1

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock12_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock12_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock12_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock12_810,
    piLeftUnsolvedHeadBlock12_810, piLeftUnsolvedTailBlock12_810]
  ring

/-- Order-96 head contributed by source block 13. -/
def piLeftUnsolvedHeadBlock13_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (23358917836800 : R) * t0 ^ 5 * u1 * a4 ^ 2
    - (163512424857600 : R) * t0 ^ 4 * v1 ^ 2 * a4 ^ 2
    - (327024849715200 : R) * t0 ^ 4 * v1 * u1 ^ 2 * a4
    - (27252070809600 : R) * t0 ^ 4 * u1 ^ 4
    - (716340146995200 : R) * t0 ^ 3 * v1 ^ 3 * u1 * a4
    - (358170073497600 : R) * t0 ^ 3 * v1 ^ 2 * u1 ^ 3
    - (149497074155520 : R) * t0 ^ 2 * v1 ^ 5 * a4
    - (373742685388800 : R) * t0 ^ 2 * v1 ^ 4 * u1 ^ 2
    - (28475633172480 : R) * t0 ^ 2 * u1 ^ 4 * s1
    - (63847708753920 : R) * t0 * v1 ^ 6 * u1
    - (7118908293120 : R) * t0 * v1 ^ 5 * b5
    - (42713449758720 : R) * t0 * v1 ^ 4 * u1 * b62
    - (49832358051840 : R) * t0 * v1 ^ 4 * a4 * w1
    - (99664716103680 : R) * t0 * v1 ^ 3 * u1 ^ 2 * w1
    - (227805065379840 : R) * t0 * v1 ^ 3 * u1 * a4 * s1
    - (113902532689920 : R) * t0 * v1 ^ 2 * u1 ^ 3 * s1
    - (1390411776000 : R) * v1 ^ 8
    - (1423781658624 : R) * v1 ^ 6 * b62
    - (9966471610368 : R) * v1 ^ 5 * u1 * w1
    - (11390253268992 : R) * v1 ^ 5 * a4 * s1
    - (28475633172480 : R) * v1 ^ 4 * u1 ^ 2 * s1

/-- Quotient tail contributed by source block 13. -/
def piLeftUnsolvedTailBlock13_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2502741196800 : R) * h ^ 8 * t0 ^ 7 * a0 * lambda
    + (6229044756480 : R) * h ^ 7 * t0 ^ 6 * v1 * a0
    + (17519188377600 : R) * h ^ 6 * t0 ^ 6 * v1 * a1 * lambda
    + (6229044756480 : R) * h ^ 5 * t0 ^ 6 * u1 * a1
    - (23358917836800 : R) * h ^ 5 * t0 ^ 5 * v1 ^ 2 * a1
    + (17519188377600 : R) * h ^ 4 * t0 ^ 6 * u1 * a2 * lambda
    + (52557565132800 : R) * h ^ 4 * t0 ^ 5 * v1 ^ 2 * a2 * lambda
    + (6229044756480 : R) * h ^ 3 * t0 ^ 6 * a4 * a2
    + (3114522378240 : R) * h ^ 3 * t0 ^ 6 * a3 ^ 2
    - (46717835673600 : R) * h ^ 3 * t0 ^ 5 * v1 * u1 * a2
    - (109008283238400 : R) * h ^ 3 * t0 ^ 4 * v1 ^ 3 * a2
    + (17519188377600 : R) * h ^ 2 * t0 ^ 6 * a4 * a3 * lambda
    + (105115130265600 : R) * h ^ 2 * t0 ^ 5 * v1 * u1 * a3 * lambda
    - (46717835673600 : R) * h * t0 ^ 5 * v1 * a4 * a3
    - (23358917836800 : R) * h * t0 ^ 5 * u1 ^ 2 * a3
    - (327024849715200 : R) * h * t0 ^ 4 * v1 ^ 2 * u1 * a3
    - (179085036748800 : R) * h * t0 ^ 3 * v1 ^ 4 * a3
    - (56951266344960 : R) * h * t0 * v1 ^ 4 * a3 * s1
    + (52557565132800 : R) * t0 ^ 5 * v1 * a4 ^ 2 * lambda

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock13_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock13_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock13_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock13_810,
    piLeftUnsolvedHeadBlock13_810, piLeftUnsolvedTailBlock13_810]
  ring

/-- Order-96 head contributed by source block 14. -/
def piLeftUnsolvedHeadBlock14_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (37374268538880 : R) * t0 ^ 5 * v1 * a4 * b5
    + (18687134269440 : R) * t0 ^ 5 * u1 ^ 2 * b5
    + (44849122246656 : R) * t0 ^ 5 * u1 * a4 * b62
    + (26161987977216 : R) * t0 ^ 5 * a4 ^ 2 * w1
    + (93435671347200 : R) * t0 ^ 4 * v1 ^ 2 * u1 * b5
    + (112122805616640 : R) * t0 ^ 4 * v1 ^ 2 * a4 * b62
    + (112122805616640 : R) * t0 ^ 4 * v1 * u1 ^ 2 * b62
    + (261619879772160 : R) * t0 ^ 4 * v1 * u1 * a4 * w1
    + (149497074155520 : R) * t0 ^ 4 * v1 * a4 ^ 2 * s1
    + (43603313295360 : R) * t0 ^ 4 * u1 ^ 3 * w1
    + (149497074155520 : R) * t0 ^ 4 * u1 ^ 2 * a4 * s1
    + (31145223782400 : R) * t0 ^ 3 * v1 ^ 4 * b5

/-- Quotient tail contributed by source block 14. -/
def piLeftUnsolvedTailBlock14_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (177972707328 : R) * h ^ 7 * t0 ^ 7 * b1
    + (9966471610368 : R) * h ^ 7 * t0 ^ 6 * a0 * s1
    + (2491617902592 : R) * h ^ 5 * t0 ^ 6 * v1 * b2
    + (8720662659072 : R) * h ^ 5 * t0 ^ 6 * a1 * w1
    + (59798829662208 : R) * h ^ 5 * t0 ^ 5 * v1 * a1 * s1
    + (3737426853888 : R) * h ^ 3 * t0 ^ 6 * u1 * b3
    + (7474853707776 : R) * h ^ 3 * t0 ^ 6 * a2 * b62
    + (11212280561664 : R) * h ^ 3 * t0 ^ 5 * v1 ^ 2 * b3
    + (52323975954432 : R) * h ^ 3 * t0 ^ 5 * v1 * a2 * w1
    + (59798829662208 : R) * h ^ 3 * t0 ^ 5 * u1 * a2 * s1
    + (149497074155520 : R) * h ^ 3 * t0 ^ 4 * v1 ^ 2 * a2 * s1
    + (87595941888000 : R) * h ^ 2 * t0 ^ 4 * v1 ^ 3 * a3 * lambda
    + (4983235805184 : R) * h * t0 ^ 6 * a4 * b4
    + (6229044756480 : R) * h * t0 ^ 6 * a3 * b5
    + (29899414831104 : R) * h * t0 ^ 5 * v1 * u1 * b4
    + (44849122246656 : R) * h * t0 ^ 5 * v1 * a3 * b62
    + (52323975954432 : R) * h * t0 ^ 5 * u1 * a3 * w1
    + (59798829662208 : R) * h * t0 ^ 5 * a4 * a3 * s1
    + (24916179025920 : R) * h * t0 ^ 4 * v1 ^ 3 * b4
    + (130809939886080 : R) * h * t0 ^ 4 * v1 ^ 2 * a3 * w1
    + (298994148311040 : R) * h * t0 ^ 4 * v1 * u1 * a3 * s1
    + (52557565132800 : R) * t0 ^ 5 * u1 ^ 2 * a4 * lambda
    + (262787825664000 : R) * t0 ^ 4 * v1 ^ 2 * u1 * a4 * lambda
    + (87595941888000 : R) * t0 ^ 4 * v1 * u1 ^ 3 * lambda
    + (87595941888000 : R) * t0 ^ 3 * v1 ^ 4 * a4 * lambda
    + (175191883776000 : R) * t0 ^ 3 * v1 ^ 3 * u1 ^ 2 * lambda
    + (52557565132800 : R) * t0 ^ 2 * v1 ^ 5 * u1 * lambda
    + (2502741196800 : R) * t0 * v1 ^ 7 * lambda

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock14_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock14_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock14_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock14_810,
    piLeftUnsolvedHeadBlock14_810, piLeftUnsolvedTailBlock14_810]
  ring

/-- Order-96 head contributed by source block 15. -/
def piLeftUnsolvedHeadBlock15_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (19465764864000 : R) * t0 ^ 6 * v1 * a4 ^ 2
    + (19465764864000 : R) * t0 ^ 6 * u1 ^ 2 * a4
    + (379582414848000 : R) * t0 ^ 5 * v1 ^ 2 * u1 * a4
    + (126527471616000 : R) * t0 ^ 5 * v1 * u1 ^ 3
    + (267654266880000 : R) * t0 ^ 4 * v1 ^ 4 * a4
    + (535308533760000 : R) * t0 ^ 4 * v1 ^ 3 * u1 ^ 2
    + (301719355392000 : R) * t0 ^ 3 * v1 ^ 5 * u1
    + (149497074155520 : R) * t0 ^ 3 * v1 ^ 3 * u1 * b62
    + (174413253181440 : R) * t0 ^ 3 * v1 ^ 3 * a4 * w1
    + (261619879772160 : R) * t0 ^ 3 * v1 ^ 2 * u1 ^ 2 * w1
    + (597988296622080 : R) * t0 ^ 3 * v1 ^ 2 * u1 * a4 * s1
    + (199329432207360 : R) * t0 ^ 3 * v1 * u1 ^ 3 * s1
    + (27808235520000 : R) * t0 ^ 2 * v1 ^ 7
    + (22424561123328 : R) * t0 ^ 2 * v1 ^ 5 * b62
    + (130809939886080 : R) * t0 ^ 2 * v1 ^ 4 * u1 * w1
    + (149497074155520 : R) * t0 ^ 2 * v1 ^ 4 * a4 * s1
    + (298994148311040 : R) * t0 ^ 2 * v1 ^ 3 * u1 ^ 2 * s1
    + (8720662659072 : R) * t0 * v1 ^ 6 * w1
    + (59798829662208 : R) * t0 * v1 ^ 5 * u1 * s1
    + (1423781658624 : R) * v1 ^ 7 * s1

/-- Quotient tail contributed by source block 15. -/
def piLeftUnsolvedTailBlock15_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2433220608000 : R) * h ^ 7 * t0 ^ 8 * a0
    - (2268109209600 : R) * h ^ 6 * t0 ^ 8 * a1 * lambda
    - (278082355200 : R) * h ^ 5 * t0 ^ 8 * b2
    - (6952058880000 : R) * h ^ 5 * t0 ^ 7 * v1 * a1
    - (18144873676800 : R) * h ^ 4 * t0 ^ 7 * v1 * a2 * lambda
    - (6952058880000 : R) * h ^ 3 * t0 ^ 7 * u1 * a2
    + (19465764864000 : R) * h ^ 3 * t0 ^ 6 * v1 ^ 2 * a2
    - (18144873676800 : R) * h ^ 2 * t0 ^ 7 * u1 * a3 * lambda
    - (63507057868800 : R) * h ^ 2 * t0 ^ 6 * v1 ^ 2 * a3 * lambda
    - (6952058880000 : R) * h * t0 ^ 7 * a4 * a3
    + (38931529728000 : R) * h * t0 ^ 6 * v1 * u1 * a3
    + (126527471616000 : R) * h * t0 ^ 5 * v1 ^ 3 * a3
    + (199329432207360 : R) * h * t0 ^ 3 * v1 ^ 3 * a3 * s1
    - (9072436838400 : R) * t0 ^ 7 * a4 ^ 2 * lambda
    - (127014115737600 : R) * t0 ^ 6 * v1 * u1 * a4 * lambda
    - (21169019289600 : R) * t0 ^ 6 * u1 ^ 3 * lambda
    - (127014115737600 : R) * t0 ^ 5 * v1 ^ 3 * a4 * lambda
    - (190521173606400 : R) * t0 ^ 5 * v1 ^ 2 * u1 ^ 2 * lambda
    - (158767644672000 : R) * t0 ^ 4 * v1 ^ 4 * u1 * lambda
    - (21169019289600 : R) * t0 ^ 3 * v1 ^ 6 * lambda

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock15_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock15_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock15_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock15_810,
    piLeftUnsolvedHeadBlock15_810, piLeftUnsolvedTailBlock15_810]
  ring

/-- Order-96 head contributed by source block 16. -/
def piLeftUnsolvedHeadBlock16_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (3780182016000 : R) * t0 ^ 8 * a4 ^ 2
    - (30241456128000 : R) * t0 ^ 7 * v1 * u1 * a4
    - (5040242688000 : R) * t0 ^ 7 * u1 ^ 3
    - (5561647104000 : R) * t0 ^ 7 * a4 * b5
    - (141126795264000 : R) * t0 ^ 6 * v1 ^ 3 * a4
    - (211690192896000 : R) * t0 ^ 6 * v1 ^ 2 * u1 ^ 2
    - (38931529728000 : R) * t0 ^ 6 * v1 * u1 * b5
    - (46717835673600 : R) * t0 ^ 6 * v1 * a4 * b62
    - (23358917836800 : R) * t0 ^ 6 * u1 ^ 2 * b62
    - (54504141619200 : R) * t0 ^ 6 * u1 * a4 * w1
    - (31145223782400 : R) * t0 ^ 6 * a4 ^ 2 * s1
    - (370457837568000 : R) * t0 ^ 5 * v1 ^ 4 * u1
    - (38931529728000 : R) * t0 ^ 5 * v1 ^ 3 * b5
    - (140153507020800 : R) * t0 ^ 5 * v1 ^ 2 * u1 * b62
    - (163512424857600 : R) * t0 ^ 5 * v1 ^ 2 * a4 * w1
    - (163512424857600 : R) * t0 ^ 5 * v1 * u1 ^ 2 * w1
    - (373742685388800 : R) * t0 ^ 5 * v1 * u1 * a4 * s1
    - (62290447564800 : R) * t0 ^ 5 * u1 ^ 3 * s1
    - (88204247040000 : R) * t0 ^ 4 * v1 ^ 6
    - (58397294592000 : R) * t0 ^ 4 * v1 ^ 4 * b62
    - (272520708096000 : R) * t0 ^ 4 * v1 ^ 3 * u1 * w1
    - (311452237824000 : R) * t0 ^ 4 * v1 ^ 3 * a4 * s1
    - (467178356736000 : R) * t0 ^ 4 * v1 ^ 2 * u1 ^ 2 * s1
    - (54504141619200 : R) * t0 ^ 3 * v1 ^ 5 * w1
    - (311452237824000 : R) * t0 ^ 3 * v1 ^ 4 * u1 * s1
    - (31145223782400 : R) * t0 ^ 2 * v1 ^ 6 * s1

/-- Quotient tail contributed by source block 16. -/
def piLeftUnsolvedTailBlock16_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2100101120000 : R) * h ^ 5 * t0 ^ 9 * a1
    - (8898635366400 : R) * h ^ 5 * t0 ^ 7 * a1 * s1
    + (7560364032000 : R) * h ^ 3 * t0 ^ 8 * v1 * a2
    - (3336988262400 : R) * h ^ 3 * t0 ^ 7 * v1 * b3
    - (7786305945600 : R) * h ^ 3 * t0 ^ 7 * a2 * w1
    - (62290447564800 : R) * h ^ 3 * t0 ^ 6 * v1 * a2 * s1
    + (7560364032000 : R) * h * t0 ^ 8 * u1 * a3
    - (15120728064000 : R) * h * t0 ^ 7 * v1 ^ 2 * a3
    - (4449317683200 : R) * h * t0 ^ 7 * u1 * b4
    - (6673976524800 : R) * h * t0 ^ 7 * a3 * b62
    - (15572611891200 : R) * h * t0 ^ 6 * v1 ^ 2 * b4
    - (54504141619200 : R) * h * t0 ^ 6 * v1 * a3 * w1
    - (62290447564800 : R) * h * t0 ^ 6 * u1 * a3 * s1
    - (186871342694400 : R) * h * t0 ^ 5 * v1 ^ 2 * a3 * s1

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock16_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock16_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock16_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock16_810,
    piLeftUnsolvedHeadBlock16_810, piLeftUnsolvedTailBlock16_810]
  ring

/-- Order-96 head contributed by source block 17. -/
def piLeftUnsolvedHeadBlock17_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4620222464000 : R) * t0 ^ 9 * v1 * b5
    - (8085389312000 : R) * t0 ^ 9 * u1 * a4
    + (10395500544000 : R) * t0 ^ 8 * v1 ^ 2 * a4
    + (10395500544000 : R) * t0 ^ 8 * v1 * u1 ^ 2
    + (5040242688000 : R) * t0 ^ 8 * u1 * b5
    + (6048291225600 : R) * t0 ^ 8 * a4 * b62
    + (152467341312000 : R) * t0 ^ 7 * v1 ^ 3 * u1
    + (20160970752000 : R) * t0 ^ 7 * v1 ^ 2 * b5
    + (48386329804800 : R) * t0 ^ 7 * v1 * u1 * b62
    + (56450718105600 : R) * t0 ^ 7 * v1 * a4 * w1
    + (28225359052800 : R) * t0 ^ 7 * u1 ^ 2 * w1
    + (64515106406400 : R) * t0 ^ 7 * u1 * a4 * s1
    + (97024671744000 : R) * t0 ^ 6 * v1 ^ 5
    + (56450718105600 : R) * t0 ^ 6 * v1 ^ 3 * b62
    + (197577513369600 : R) * t0 ^ 6 * v1 ^ 2 * u1 * w1
    + (225802872422400 : R) * t0 ^ 6 * v1 ^ 2 * a4 * s1
    + (225802872422400 : R) * t0 ^ 6 * v1 * u1 ^ 2 * s1
    + (98788756684800 : R) * t0 ^ 5 * v1 ^ 4 * w1
    + (451605744844800 : R) * t0 ^ 5 * v1 ^ 3 * u1 * s1
    + (112901436211200 : R) * t0 ^ 4 * v1 ^ 5 * s1

/-- Quotient tail contributed by source block 17. -/
def piLeftUnsolvedTailBlock17_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2079100108800 : R) * h ^ 4 * t0 ^ 9 * a2 * lambda
    - (1848088985600 : R) * h ^ 3 * t0 ^ 10 * a2
    + (336016179200 : R) * h ^ 3 * t0 ^ 9 * b3
    + (8064388300800 : R) * h ^ 3 * t0 ^ 8 * a2 * s1
    - (1923167600640 : R) * h ^ 2 * t0 ^ 10 * a3 * lambda
    + (18711900979200 : R) * h ^ 2 * t0 ^ 8 * v1 * a3 * lambda
    - (369617797120 : R) * h * t0 ^ 10 * b4
    - (8085389312000 : R) * h * t0 ^ 9 * v1 * a3
    + (4032194150400 : R) * h * t0 ^ 8 * v1 * b4
    + (7056339763200 : R) * h * t0 ^ 8 * a3 * w1
    + (64515106406400 : R) * h * t0 ^ 7 * v1 * a3 * s1
    - (19231676006400 : R) * t0 ^ 9 * v1 * a4 * lambda
    - (9615838003200 : R) * t0 ^ 9 * u1 ^ 2 * lambda
    - (86542542028800 : R) * t0 ^ 8 * v1 ^ 2 * u1 * lambda
    + (18711900979200 : R) * t0 ^ 8 * u1 * a4 * lambda
    - (57695028019200 : R) * t0 ^ 7 * v1 ^ 4 * lambda
    + (74847603916800 : R) * t0 ^ 7 * v1 ^ 2 * a4 * lambda
    + (74847603916800 : R) * t0 ^ 7 * v1 * u1 ^ 2 * lambda
    + (174644409139200 : R) * t0 ^ 6 * v1 ^ 3 * u1 * lambda
    + (52393322741760 : R) * t0 ^ 5 * v1 ^ 5 * lambda

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock17_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock17_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock17_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock17_810,
    piLeftUnsolvedHeadBlock17_810, piLeftUnsolvedTailBlock17_810]
  ring

/-- Order-96 head contributed by source block 18. -/
def piLeftUnsolvedHeadBlock18_810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (104048944125 : R) * t0 ^ 16
    - (1256440080000 : R) * t0 ^ 14 * v1
    - (402060825600 : R) * t0 ^ 14 * s1
    + (1364134944000 : R) * t0 ^ 13 * u1
    + (402060825600 : R) * t0 ^ 13 * w1
    + (4666777440000 : R) * t0 ^ 12 * v1 ^ 2
    + (5973475123200 : R) * t0 ^ 12 * v1 * s1
    - (1493368780800 : R) * t0 ^ 12 * a4
    - (398231674880 : R) * t0 ^ 12 * b62
    - (8960212684800 : R) * t0 ^ 11 * v1 * u1
    - (5575243448320 : R) * t0 ^ 11 * v1 * w1
    - (6371706798080 : R) * t0 ^ 11 * u1 * s1
    + (388518707200 : R) * t0 ^ 11 * b5
    - (35044387389440 : R) * t0 ^ 10 * v1 ^ 2 * s1
    + (8547411558400 : R) * t0 ^ 10 * v1 * a4
    + (5128446935040 : R) * t0 ^ 10 * v1 * b62
    + (4273705779200 : R) * t0 ^ 10 * u1 ^ 2
    + (5983188090880 : R) * t0 ^ 10 * u1 * w1
    + (6837929246720 : R) * t0 ^ 10 * a4 * s1
    - (5342132224000 : R) * t0 ^ 9 * v1 ^ 2 * u1
    + (29915940454400 : R) * t0 ^ 9 * v1 ^ 2 * w1
    + (68379292467200 : R) * t0 ^ 9 * v1 * u1 * s1
    - (5544266956800 : R) * t0 ^ 9 * u1 * b62
    - (6468311449600 : R) * t0 ^ 9 * a4 * w1
    - (40065991680000 : R) * t0 ^ 8 * v1 ^ 4
    + (102568938700800 : R) * t0 ^ 8 * v1 ^ 3 * s1
    - (24949201305600 : R) * t0 ^ 8 * v1 ^ 2 * b62
    - (58214803046400 : R) * t0 ^ 8 * v1 * u1 * w1
    - (66531203481600 : R) * t0 ^ 8 * v1 * a4 * s1
    - (33265601740800 : R) * t0 ^ 8 * u1 ^ 2 * s1
    - (77619737395200 : R) * t0 ^ 7 * v1 ^ 3 * w1
    - (266124813926400 : R) * t0 ^ 7 * v1 ^ 2 * u1 * s1
    - (155239474790400 : R) * t0 ^ 6 * v1 ^ 4 * s1

/-- Quotient tail contributed by source block 18. -/
def piLeftUnsolvedTailBlock18_810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1651204505600 : R) * h * t0 ^ 11 * a3
    - (7392355942400 : R) * h * t0 ^ 9 * a3 * s1
    - (99886986360 : R) * t0 ^ 15 * lambda
    + (1583114500800 : R) * t0 ^ 13 * v1 * lambda
    - (1680039878400 : R) * t0 ^ 12 * u1 * lambda
    - (10080239270400 : R) * t0 ^ 11 * v1 ^ 2 * lambda
    + (1792042536960 : R) * t0 ^ 11 * a4 * lambda
    + (19712467906560 : R) * t0 ^ 10 * v1 * u1 * lambda
    + (32854113177600 : R) * t0 ^ 9 * v1 ^ 3 * lambda

set_option maxHeartbeats 100000000 in
private theorem piLeftUnsolvedBlock18_factored810
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefectBlock18_810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHeadBlock18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTailBlock18_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefectBlock18_810,
    piLeftUnsolvedHeadBlock18_810, piLeftUnsolvedTailBlock18_810]
  ring

def piLeftUnsolvedHead810 (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    piLeftUnsolvedHeadBlock0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedHeadBlock18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

def piLeftUnsolvedTail810 (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    piLeftUnsolvedTailBlock0_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock1_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock2_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock3_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock4_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock5_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock6_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock7_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock8_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock9_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock10_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock11_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock12_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock13_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock14_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock15_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock16_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock17_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
    + piLeftUnsolvedTailBlock18_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

set_option maxHeartbeats 400000000 in
/-- Exact polynomial-uniform order-96 factorization before any scalar
load solve is inserted. -/
theorem localClearedSixteenthDefect810_left_unsolved_factored
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    localClearedSixteenthDefect810
        h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
        a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =
      h ^ 96 * (piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0
        s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0
          s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by
  simp only [localClearedSixteenthDefect810,
    localClearedSixteenthDefectCore810]
  rw [piLeftUnsolvedBlock0_factored810]
  rw [piLeftUnsolvedBlock1_factored810]
  rw [piLeftUnsolvedBlock2_factored810]
  rw [piLeftUnsolvedBlock3_factored810]
  rw [piLeftUnsolvedBlock4_factored810]
  rw [piLeftUnsolvedBlock5_factored810]
  rw [piLeftUnsolvedBlock6_factored810]
  rw [piLeftUnsolvedBlock7_factored810]
  rw [piLeftUnsolvedBlock8_factored810]
  rw [piLeftUnsolvedBlock9_factored810]
  rw [piLeftUnsolvedBlock10_factored810]
  rw [piLeftUnsolvedBlock11_factored810]
  rw [piLeftUnsolvedBlock12_factored810]
  rw [piLeftUnsolvedBlock13_factored810]
  rw [piLeftUnsolvedBlock14_factored810]
  rw [piLeftUnsolvedBlock15_factored810]
  rw [piLeftUnsolvedBlock16_factored810]
  rw [piLeftUnsolvedBlock17_factored810]
  rw [piLeftUnsolvedBlock18_factored810]
  simp only [piLeftUnsolvedHead810, piLeftUnsolvedTail810]
  ring

#print axioms localClearedSixteenthDefect810_left_unsolved_factored

end PiLeftUnsolvedBlocks810

section PiLeftUnsolvedRootPeel810

variable {k : Type*} [Field k] [CharZero k]

/-- A weight-112 source power relation kills the unsolved order-96 head
at every root of the local parameter. -/
theorem piLeftUnsolvedHead810_eval_root_of_power
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda eta x : k) (hh : h ≠ 0) (hroot : h.eval x = 0)
    (hpower :
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 112) :
    (piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval x = 0 := by
  have h96 : h ^ 96 ≠ 0 := pow_ne_zero 96 hh
  have hquot :
      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
          b5 b4 b3 b2 b1 (Polynomial.C lambda) +
        h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        Polynomial.C eta * h ^ 16 := by
    apply mul_left_cancel₀ h96
    rw [← localClearedSixteenthDefect810_left_unsolved_factored]
    rw [hpower]
    ring
  have hev := congrArg (Polynomial.eval x) hquot
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, hroot] using hev

#print axioms piLeftUnsolvedHead810_eval_root_of_power

end PiLeftUnsolvedRootPeel810

end Max11DegreeRoutes
