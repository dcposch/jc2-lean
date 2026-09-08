import Fable610ScaleTwoAlignedEleventhFacePart02Scratch
import Fable610ScaleTwoAlignedEleventhFacePart11Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 6400000000 in
/-- Descent of the consumed degree-`4` row in the nonsquare chamber:
the eleventh defect vanishes identically, the `H²²`-peeled core
absorbs the undecic head through the seventh-face divisibilities,
peeling `H²` onto the squared carried `p₂` divisor, one `H` onto the
cubed carried `t₃` divisor, one `H` onto the squared carried `v`
divisor, and `H²` beyond — bottoming out on the residue relation
WITHOUT any new witness: every divisor of the cascade is carried. -/
theorem alignedNonsquareEleventh_descent_610 {K : Type*}
    [Field K] [CharZero K]
    {H g1 f t1 t2 u t3 v a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 :
      K[X]}
    {κ κ₅ κ₇ : K}
    (hH : H ≠ 0)
    (hg1 : a5 = H ^ 2 * g1) (hf : a4 = H * f)
    (hD0 : alignedThirdDefect610 H a3 a4 a5 b7 κ = 0)
    (hF0 : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ = 0)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15)
    (hI0 :
      alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ = 0)
    (hJ : alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₇ * H ^ 20)
    (hL0 : alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6
        b7 κ = 0)
    (hLam0 : alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4
        b5 b6 b7 κ = 0)
    (ht1 : (3 : K[X]) * f - g1 ^ 2 = H * t1)
    (ht2 : (27 : K[X]) * a3 - g1 ^ 3 = H * t2)
    (hu : (81 : K[X]) * a2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
      H * u)
    (ht3 : t2 - (6 : K[X]) * g1 * t1 = H * t3)
    (hv : (243 : K[X]) * a1 - g1 * u = H * v) :
    alignedEleventhNonsquareResidue610 H g1 t1 u t3 v a0 κ κ₅ κ₇ =
      0 := by
  have hL' := hLam0
  unfold alignedEleventhDefect610 at hL'
  rw [hD0, hF0, hG, hI0, hJ, hL0, hg1, hf] at hL'
  have hcore :
      ((15049359360 : K[X]) * f ^ 5 * g1 - (22574039040 : K[X]) * f ^ 4 *
      a3 - (54344908800 : K[X]) * f ^ 4 * g1 ^ 3 + (150493593600 : K[X]) *
      f ^ 3 * a3 * g1 ^ 2 + (57967902720 : K[X]) * f ^ 3 * g1 ^ 5 -
      (135444234240 : K[X]) * f ^ 2 * a3 ^ 2 * g1 - (163034726400 : K[X])
      * f ^ 2 * a3 * g1 ^ 4 - (26223575040 : K[X]) * f ^ 2 * g1 ^ 7 +
      (38698352640 : K[X]) * f * a3 ^ 3 + (150493593600 : K[X]) * f * a3 ^
      2 * g1 ^ 3 + (57967902720 : K[X]) * f * a3 * g1 ^ 6 + (5341839360 :
      K[X]) * f * g1 ^ 9 - (45148078080 : K[X]) * a3 ^ 3 * g1 ^ 2 -
      (32606945280 : K[X]) * a3 ^ 2 * g1 ^ 5 - (6555893760 : K[X]) * a3 *
      g1 ^ 8 - (404684800 : K[X]) * g1 ^ 11) + H * (-((90296156160 : K[X])
      * f ^ 3 * g1 * a2) + (116095057920 : K[X]) * f ^ 2 * a3 * a2 +
      (150493593600 : K[X]) * f ^ 2 * g1 ^ 3 * a2 - (270888468480 : K[X])
      * f * a3 * g1 ^ 2 * a2 - (65213890560 : K[X]) * f * g1 ^ 5 * a2 +
      (116095057920 : K[X]) * a3 ^ 2 * g1 * a2 + (75246796800 : K[X]) * a3
      * g1 ^ 4 * a2 + (8281128960 : K[X]) * g1 ^ 7 * a2 - Polynomial.C κ *
      ((2866544640 : K[X]) * f ^ 4 * g1) + Polynomial.C κ * ((4299816960 :
      K[X]) * f ^ 3 * a3) + Polynomial.C κ * ((7007109120 : K[X]) * f ^ 3
      * g1 ^ 3) - Polynomial.C κ * ((17199267840 : K[X]) * f ^ 2 * a3 * g1
      ^ 2) - Polynomial.C κ * ((4904976384 : K[X]) * f ^ 2 * g1 ^ 5) +
      Polynomial.C κ * ((12899450880 : K[X]) * f * a3 ^ 2 * g1) +
      Polynomial.C κ * ((10510663680 : K[X]) * f * a3 * g1 ^ 4) +
      Polynomial.C κ * ((1323565056 : K[X]) * f * g1 ^ 7) - Polynomial.C κ
      * ((2579890176 : K[X]) * a3 ^ 3) - Polynomial.C κ * ((5733089280 :
      K[X]) * a3 ^ 2 * g1 ^ 3) - Polynomial.C κ * ((1634992128 : K[X]) *
      a3 * g1 ^ 6) - Polynomial.C κ * ((122552320 : K[X]) * g1 ^ 9)) + H ^
      2 * ((38698352640 : K[X]) * f ^ 3 * a1 - (135444234240 : K[X]) * f ^
      2 * g1 ^ 2 * a1 + (232190115840 : K[X]) * f * a3 * g1 * a1 +
      (75246796800 : K[X]) * f * g1 ^ 4 * a1 + (116095057920 : K[X]) * f *
      g1 * a2 ^ 2 - (87071293440 : K[X]) * a3 ^ 2 * a1 - (90296156160 :
      K[X]) * a3 * g1 ^ 3 * a1 - (87071293440 : K[X]) * a3 * a2 ^ 2 -
      (10868981760 : K[X]) * g1 ^ 6 * a1 - (45148078080 : K[X]) * g1 ^ 3 *
      a2 ^ 2 + Polynomial.C κ * ((12899450880 : K[X]) * f ^ 2 * g1 * a2) -
      Polynomial.C κ * ((15479341056 : K[X]) * f * a3 * a2) - Polynomial.C
      κ * ((11466178560 : K[X]) * f * g1 ^ 3 * a2) + Polynomial.C κ *
      ((12899450880 : K[X]) * a3 * g1 ^ 2 * a2) + Polynomial.C κ *
      ((2102132736 : K[X]) * g1 ^ 5 * a2)) + H ^ 3 * ((116095057920 :
      K[X]) * f ^ 2 * g1 * a0 - (174142586880 : K[X]) * f * a3 * a0 -
      (90296156160 : K[X]) * f * g1 ^ 3 * a0 - (174142586880 : K[X]) * f *
      a1 * a2 + (116095057920 : K[X]) * a3 * g1 ^ 2 * a0 + (15049359360 :
      K[X]) * g1 ^ 5 * a0 + (116095057920 : K[X]) * g1 ^ 2 * a1 * a2 -
      Polynomial.C κ₅ * ((663552 : K[X]) * f ^ 2 * g1) + Polynomial.C κ₅ *
      ((995328 : K[X]) * f * a3) + Polynomial.C κ₅ * ((516096 : K[X]) * f
      * g1 ^ 3) - Polynomial.C κ₅ * ((663552 : K[X]) * a3 * g1 ^ 2) -
      Polynomial.C κ₅ * ((86016 : K[X]) * g1 ^ 5) - Polynomial.C κ *
      ((7739670528 : K[X]) * f ^ 2 * a1) + Polynomial.C κ * ((12899450880
      : K[X]) * f * g1 ^ 2 * a1) - Polynomial.C κ * ((15479341056 : K[X])
      * a3 * g1 * a1) - Polynomial.C κ * ((2866544640 : K[X]) * g1 ^ 4 *
      a1) - Polynomial.C κ * ((7739670528 : K[X]) * g1 * a2 ^ 2)) + H ^ 4
      * (-((174142586880 : K[X]) * g1 * a0 * a2) - (87071293440 : K[X]) *
      g1 * a1 ^ 2 + Polynomial.C κ₇ * ((6912 : K[X]) * f * g1) -
      Polynomial.C κ₇ * ((10368 : K[X]) * a3) - Polynomial.C κ₇ * ((1920 :
      K[X]) * g1 ^ 3) + Polynomial.C κ₅ * ((995328 : K[X]) * g1 * a2) -
      Polynomial.C κ * ((15479341056 : K[X]) * f * g1 * a0) + Polynomial.C
      κ * ((23219011584 : K[X]) * a3 * a0) + Polynomial.C κ * ((4299816960
      : K[X]) * g1 ^ 3 * a0) + Polynomial.C κ * ((23219011584 : K[X]) * a1
      * a2)) + H ^ 5 * ((522427760640 : K[X]) * a0 * a1 - Polynomial.C κ₅
      * ((2985984 : K[X]) * a1)) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 22 hH)
    linear_combination hL'
  have hR2n :
      (-((13271040 : K[X]) * t1 ^ 2 * g1 ^ 7) + (8847360 : K[X]) * t1 * t2
      * g1 ^ 6 - (716636160 : K[X]) * t1 * g1 ^ 5 * a2 - (1474560 : K[X])
      * t2 ^ 2 * g1 ^ 5 + (238878720 : K[X]) * t2 * g1 ^ 4 * a2 -
      (9674588160 : K[X]) * g1 ^ 3 * a2 ^ 2) + H * ((247726080 : K[X]) *
      t1 ^ 3 * g1 ^ 5 - (154828800 : K[X]) * t1 ^ 2 * t2 * g1 ^ 4 +
      (7166361600 : K[X]) * t1 ^ 2 * g1 ^ 3 * a2 + (29491200 : K[X]) * t1
      * t2 ^ 2 * g1 ^ 3 - (2388787200 : K[X]) * t1 * t2 * g1 ^ 2 * a2 +
      (2149908480 : K[X]) * t1 * g1 ^ 4 * a1 + (38698352640 : K[X]) * t1 *
      g1 * a2 ^ 2 - (1638400 : K[X]) * t2 ^ 3 * g1 ^ 2 + (159252480 :
      K[X]) * t2 ^ 2 * g1 * a2 - (716636160 : K[X]) * t2 * g1 ^ 3 * a1 -
      (3224862720 : K[X]) * t2 * a2 ^ 2 + (58047528960 : K[X]) * g1 ^ 2 *
      a1 * a2 - Polynomial.C κ * ((31850496 : K[X]) * t1 ^ 2 * g1 ^ 5) +
      Polynomial.C κ * ((17694720 : K[X]) * t1 * t2 * g1 ^ 4) -
      Polynomial.C κ * ((1146617856 : K[X]) * t1 * g1 ^ 3 * a2) -
      Polynomial.C κ * ((2359296 : K[X]) * t2 ^ 2 * g1 ^ 3) + Polynomial.C
      κ * ((286654464 : K[X]) * t2 * g1 ^ 2 * a2) - Polynomial.C κ *
      ((7739670528 : K[X]) * g1 * a2 ^ 2)) + H ^ 2 * (-((371589120 : K[X])
      * t1 ^ 4 * g1 ^ 3) + (165150720 : K[X]) * t1 ^ 3 * t2 * g1 ^ 2 -
      (3344302080 : K[X]) * t1 ^ 3 * g1 * a2 - (20643840 : K[X]) * t1 ^ 2
      * t2 ^ 2 * g1 + (477757440 : K[X]) * t1 ^ 2 * t2 * a2 - (10749542400
      : K[X]) * t1 ^ 2 * g1 ^ 2 * a1 + (655360 : K[X]) * t1 * t2 ^ 3 +
      (2866544640 : K[X]) * t1 * t2 * g1 * a1 - (6449725440 : K[X]) * t1 *
      g1 ^ 3 * a0 - (58047528960 : K[X]) * t1 * a1 * a2 - (119439360 :
      K[X]) * t2 ^ 2 * a1 + (2149908480 : K[X]) * t2 * g1 ^ 2 * a0 -
      (174142586880 : K[X]) * g1 * a0 * a2 - (87071293440 : K[X]) * g1 *
      a1 ^ 2 + Polynomial.C κ₅ * ((36864 : K[X]) * t1 * g1 ^ 3) -
      Polynomial.C κ₅ * ((12288 : K[X]) * t2 * g1 ^ 2) + Polynomial.C κ₅ *
      ((995328 : K[X]) * g1 * a2) + Polynomial.C κ * ((123863040 : K[X]) *
      t1 ^ 3 * g1 ^ 3) - Polynomial.C κ * ((53084160 : K[X]) * t1 ^ 2 * t2
      * g1 ^ 2) + Polynomial.C κ * ((1433272320 : K[X]) * t1 ^ 2 * g1 *
      a2) + Polynomial.C κ * ((5898240 : K[X]) * t1 * t2 ^ 2 * g1) -
      Polynomial.C κ * ((191102976 : K[X]) * t1 * t2 * a2) + Polynomial.C
      κ * ((2579890176 : K[X]) * t1 * g1 ^ 2 * a1) - Polynomial.C κ *
      ((131072 : K[X]) * t2 ^ 3) - Polynomial.C κ * ((573308928 : K[X]) *
      t2 * g1 * a1) + Polynomial.C κ * ((23219011584 : K[X]) * a1 * a2)) +
      H ^ 3 * ((61931520 : K[X]) * t1 ^ 5 * g1 - (10321920 : K[X]) * t1 ^
      4 * t2 + (1433272320 : K[X]) * t1 ^ 3 * a1 + (12899450880 : K[X]) *
      t1 ^ 2 * g1 * a0 - (2149908480 : K[X]) * t1 * t2 * a0 +
      (522427760640 : K[X]) * a0 * a1 + Polynomial.C κ₇ * ((2304 : K[X]) *
      t1 * g1) - Polynomial.C κ₇ * ((384 : K[X]) * t2) - Polynomial.C κ₅ *
      ((73728 : K[X]) * t1 ^ 2 * g1) + Polynomial.C κ₅ * ((12288 : K[X]) *
      t1 * t2) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) - Polynomial.C
      κ * ((35389440 : K[X]) * t1 ^ 4 * g1) + Polynomial.C κ * ((5898240 :
      K[X]) * t1 ^ 3 * t2) - Polynomial.C κ * ((859963392 : K[X]) * t1 ^ 2
      * a1) - Polynomial.C κ * ((5159780352 : K[X]) * t1 * g1 * a0) +
      Polynomial.C κ * ((859963392 : K[X]) * t2 * a0)) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    linear_combination hcore + (-((61931520 : K[X]) * t1 ^ 4 * g1 * H ^ 4 - (423198720 : K[X]) * t1 ^
      3 * g1 ^ 3 * H ^ 3 + (185794560 : K[X]) * t1 ^ 3 * g1 * f * H ^ 3 -
      (278691840 : K[X]) * t1 ^ 3 * a3 * H ^ 3 + (505774080 : K[X]) * t1 ^
      2 * g1 ^ 5 * H ^ 2 - (1455390720 : K[X]) * t1 ^ 2 * g1 ^ 3 * f * H ^
      2 + (4737761280 : K[X]) * t1 ^ 2 * g1 ^ 2 * a3 * H ^ 2 + (557383680
      : K[X]) * t1 ^ 2 * g1 * f ^ 2 * H ^ 2 - (3344302080 : K[X]) * t1 ^ 2
      * g1 * a2 * H ^ 3 - (836075520 : K[X]) * t1 ^ 2 * f * a3 * H ^ 2 +
      (1433272320 : K[X]) * t1 ^ 2 * a1 * H ^ 4 - (384860160 : K[X]) * t1
      * g1 ^ 7 * H + (2972712960 : K[X]) * t1 * g1 ^ 5 * f * H -
      (7803371520 : K[X]) * t1 * g1 ^ 4 * a3 * H - (4923555840 : K[X]) *
      t1 * g1 ^ 3 * f ^ 2 * H + (10032906240 : K[X]) * t1 * g1 ^ 3 * a2 *
      H ^ 2 + (15049359360 : K[X]) * t1 * g1 ^ 2 * f * a3 * H -
      (12182814720 : K[X]) * t1 * g1 ^ 2 * a1 * H ^ 3 + (1672151040 :
      K[X]) * t1 * g1 * f ^ 3 * H - (10032906240 : K[X]) * t1 * g1 * f *
      a2 * H ^ 2 - (15049359360 : K[X]) * t1 * g1 * a3 ^ 2 * H +
      (12899450880 : K[X]) * t1 * g1 * a0 * H ^ 4 - (2508226560 : K[X]) *
      t1 * f ^ 2 * a3 * H + (4299816960 : K[X]) * t1 * f * a1 * H ^ 3 +
      (12899450880 : K[X]) * t1 * a3 * a2 * H ^ 2 + (404848640 : K[X]) *
      g1 ^ 9 - (4127293440 : K[X]) * g1 ^ 7 * f + (6502809600 : K[X]) * g1
      ^ 6 * a3 + (13841694720 : K[X]) * g1 ^ 5 * f ^ 2 - (8360755200 :
      K[X]) * g1 ^ 5 * a2 * H - (38459473920 : K[X]) * g1 ^ 4 * f * a3 +
      (11466178560 : K[X]) * g1 ^ 4 * a1 * H ^ 2 - (16442818560 : K[X]) *
      g1 ^ 3 * f ^ 3 + (40131624960 : K[X]) * g1 ^ 3 * f * a2 * H +
      (35115171840 : K[X]) * g1 ^ 3 * a3 ^ 2 - (17199267840 : K[X]) * g1 ^
      3 * a0 * H ^ 3 + (47656304640 : K[X]) * g1 ^ 2 * f ^ 2 * a3 -
      (40848261120 : K[X]) * g1 ^ 2 * f * a1 * H ^ 2 - (77396705280 :
      K[X]) * g1 ^ 2 * a3 * a2 * H + (5016453120 : K[X]) * g1 * f ^ 4 -
      (30098718720 : K[X]) * g1 * f ^ 2 * a2 * H - (45148078080 : K[X]) *
      g1 * f * a3 ^ 2 + (38698352640 : K[X]) * g1 * f * a0 * H ^ 3 +
      (77396705280 : K[X]) * g1 * a3 * a1 * H ^ 2 + (38698352640 : K[X]) *
      g1 * a2 ^ 2 * H ^ 2 - (7524679680 : K[X]) * f ^ 3 * a3 +
      (12899450880 : K[X]) * f ^ 2 * a1 * H ^ 2 + (38698352640 : K[X]) * f
      * a3 * a2 * H + (12899450880 : K[X]) * a3 ^ 3 - (58047528960 : K[X])
      * a3 * a0 * H ^ 3 - (58047528960 : K[X]) * a1 * a2 * H ^ 3 +
      Polynomial.C κ₇ * ((2304 : K[X]) * g1 * H ^ 4) - Polynomial.C κ₅ *
      ((73728 : K[X]) * t1 * g1 * H ^ 4) + Polynomial.C κ₅ * ((98304 :
      K[X]) * g1 ^ 3 * H ^ 3) - Polynomial.C κ₅ * ((221184 : K[X]) * g1 *
      f * H ^ 3) + Polynomial.C κ₅ * ((331776 : K[X]) * a3 * H ^ 3) -
      Polynomial.C κ * ((35389440 : K[X]) * t1 ^ 3 * g1 * H ^ 4) +
      Polynomial.C κ * ((153354240 : K[X]) * t1 ^ 2 * g1 ^ 3 * H ^ 3) -
      Polynomial.C κ * ((106168320 : K[X]) * t1 ^ 2 * g1 * f * H ^ 3) +
      Polynomial.C κ * ((159252480 : K[X]) * t1 ^ 2 * a3 * H ^ 3) -
      Polynomial.C κ * ((132120576 : K[X]) * t1 * g1 ^ 5 * H ^ 2) +
      Polynomial.C κ * ((566231040 : K[X]) * t1 * g1 ^ 3 * f * H ^ 2) -
      Polynomial.C κ * ((1592524800 : K[X]) * t1 * g1 ^ 2 * a3 * H ^ 2) -
      Polynomial.C κ * ((318504960 : K[X]) * t1 * g1 * f ^ 2 * H ^ 2) +
      Polynomial.C κ * ((1433272320 : K[X]) * t1 * g1 * a2 * H ^ 3) +
      Polynomial.C κ * ((477757440 : K[X]) * t1 * f * a3 * H ^ 2) -
      Polynomial.C κ * ((859963392 : K[X]) * t1 * a1 * H ^ 4) +
      Polynomial.C κ * ((120324096 : K[X]) * g1 ^ 7 * H) - Polynomial.C κ
      * ((962592768 : K[X]) * g1 ^ 5 * f * H) + Polynomial.C κ *
      ((1751777280 : K[X]) * g1 ^ 4 * a3 * H) + Polynomial.C κ *
      ((2017198080 : K[X]) * g1 ^ 3 * f ^ 2 * H) - Polynomial.C κ *
      ((2388787200 : K[X]) * g1 ^ 3 * a2 * H ^ 2) - Polynomial.C κ *
      ((5255331840 : K[X]) * g1 ^ 2 * f * a3 * H) + Polynomial.C κ *
      ((3439853568 : K[X]) * g1 ^ 2 * a1 * H ^ 3) - Polynomial.C κ *
      ((955514880 : K[X]) * g1 * f ^ 3 * H) + Polynomial.C κ *
      ((4299816960 : K[X]) * g1 * f * a2 * H ^ 2) + Polynomial.C κ *
      ((4299816960 : K[X]) * g1 * a3 ^ 2 * H) - Polynomial.C κ *
      ((5159780352 : K[X]) * g1 * a0 * H ^ 4) + Polynomial.C κ *
      ((1433272320 : K[X]) * f ^ 2 * a3 * H) - Polynomial.C κ *
      ((2579890176 : K[X]) * f * a1 * H ^ 3) - Polynomial.C κ *
      ((5159780352 : K[X]) * a3 * a2 * H ^ 2))) * ht1 + (-(-((10321920 :
      K[X]) * t1 ^ 4 * H ^ 4) + (165150720 : K[X]) * t1 ^ 3 * g1 ^ 2 * H ^
      3 - (20643840 : K[X]) * t1 ^ 2 * t2 * g1 * H ^ 3 - (134184960 :
      K[X]) * t1 ^ 2 * g1 ^ 4 * H ^ 2 - (557383680 : K[X]) * t1 ^ 2 * g1 *
      a3 * H ^ 2 + (477757440 : K[X]) * t1 ^ 2 * a2 * H ^ 3 + (655360 :
      K[X]) * t1 * t2 ^ 2 * H ^ 3 + (28835840 : K[X]) * t1 * t2 * g1 ^ 3 *
      H ^ 2 + (17694720 : K[X]) * t1 * t2 * a3 * H ^ 2 - (19988480 : K[X])
      * t1 * g1 ^ 6 * H + (760872960 : K[X]) * t1 * g1 ^ 3 * a3 * H -
      (2388787200 : K[X]) * t1 * g1 ^ 2 * a2 * H ^ 2 + (2866544640 : K[X])
      * t1 * g1 * a1 * H ^ 3 + (477757440 : K[X]) * t1 * a3 ^ 2 * H -
      (2149908480 : K[X]) * t1 * a0 * H ^ 4 - (1638400 : K[X]) * t2 ^ 2 *
      g1 ^ 2 * H ^ 2 + (163840 : K[X]) * t2 * g1 ^ 5 * H - (44236800 :
      K[X]) * t2 * g1 ^ 2 * a3 * H + (159252480 : K[X]) * t2 * g1 * a2 * H
      ^ 2 - (119439360 : K[X]) * t2 * a1 * H ^ 3 - (163840 : K[X]) * g1 ^
      8 + (48660480 : K[X]) * g1 ^ 5 * a3 + (79626240 : K[X]) * g1 ^ 4 *
      a2 * H - (597196800 : K[X]) * g1 ^ 3 * a1 * H ^ 2 - (1194393600 :
      K[X]) * g1 ^ 2 * a3 ^ 2 + (2149908480 : K[X]) * g1 ^ 2 * a0 * H ^ 3
      + (4299816960 : K[X]) * g1 * a3 * a2 * H - (3224862720 : K[X]) * a3
      * a1 * H ^ 2 - (3224862720 : K[X]) * a2 ^ 2 * H ^ 2 - Polynomial.C
      κ₇ * ((384 : K[X]) * H ^ 4) + Polynomial.C κ₅ * ((12288 : K[X]) * t1
      * H ^ 4) - Polynomial.C κ₅ * ((12288 : K[X]) * g1 ^ 2 * H ^ 3) +
      Polynomial.C κ * ((5898240 : K[X]) * t1 ^ 3 * H ^ 4) - Polynomial.C
      κ * ((53084160 : K[X]) * t1 ^ 2 * g1 ^ 2 * H ^ 3) + Polynomial.C κ *
      ((5898240 : K[X]) * t1 * t2 * g1 * H ^ 3) + Polynomial.C κ *
      ((11796480 : K[X]) * t1 * g1 ^ 4 * H ^ 2) + Polynomial.C κ *
      ((159252480 : K[X]) * t1 * g1 * a3 * H ^ 2) - Polynomial.C κ *
      ((191102976 : K[X]) * t1 * a2 * H ^ 3) - Polynomial.C κ * ((131072 :
      K[X]) * t2 ^ 2 * H ^ 3) - Polynomial.C κ * ((2228224 : K[X]) * t2 *
      g1 ^ 3 * H ^ 2) - Polynomial.C κ * ((3538944 : K[X]) * t2 * a3 * H ^
      2) + Polynomial.C κ * ((2228224 : K[X]) * g1 ^ 6 * H) - Polynomial.C
      κ * ((56623104 : K[X]) * g1 ^ 3 * a3 * H) + Polynomial.C κ *
      ((286654464 : K[X]) * g1 ^ 2 * a2 * H ^ 2) - Polynomial.C κ *
      ((573308928 : K[X]) * g1 * a1 * H ^ 3) - Polynomial.C κ * ((95551488
      : K[X]) * a3 ^ 2 * H) + Polynomial.C κ * ((859963392 : K[X]) * a0 *
      H ^ 4))) * ht2
  have hR3n :
      ((35389440 : K[X]) * t1 ^ 3 * g1 ^ 5 - (17694720 : K[X]) * t1 ^ 2 *
      t2 * g1 ^ 4 + (2949120 : K[X]) * t1 * t2 ^ 2 * g1 ^ 3 - (163840 :
      K[X]) * t2 ^ 3 * g1 ^ 2) + H * (-((247726080 : K[X]) * t1 ^ 4 * g1 ^
      3) + (106168320 : K[X]) * t1 ^ 3 * t2 * g1 ^ 2 - (14745600 : K[X]) *
      t1 ^ 2 * t2 ^ 2 * g1 + (53084160 : K[X]) * t1 ^ 2 * u * g1 ^ 3 -
      (8599633920 : K[X]) * t1 ^ 2 * g1 ^ 2 * a1 + (655360 : K[X]) * t1 *
      t2 ^ 3 - (14745600 : K[X]) * t1 * t2 * u * g1 ^ 2 + (2149908480 :
      K[X]) * t1 * t2 * g1 * a1 + (983040 : K[X]) * t2 ^ 2 * u * g1 -
      (119439360 : K[X]) * t2 ^ 2 * a1 - (1474560 : K[X]) * u ^ 2 * g1 ^ 3
      + (716636160 : K[X]) * u * g1 ^ 2 * a1 - (87071293440 : K[X]) * g1 *
      a1 ^ 2 + Polynomial.C κ * ((70778880 : K[X]) * t1 ^ 3 * g1 ^ 3) -
      Polynomial.C κ * ((28311552 : K[X]) * t1 ^ 2 * t2 * g1 ^ 2) +
      Polynomial.C κ * ((3538944 : K[X]) * t1 * t2 ^ 2 * g1) -
      Polynomial.C κ * ((7077888 : K[X]) * t1 * u * g1 ^ 3) + Polynomial.C
      κ * ((1719926784 : K[X]) * t1 * g1 ^ 2 * a1) - Polynomial.C κ *
      ((131072 : K[X]) * t2 ^ 3) + Polynomial.C κ * ((1179648 : K[X]) * t2
      * u * g1 ^ 2) - Polynomial.C κ * ((286654464 : K[X]) * t2 * g1 *
      a1)) + H ^ 2 * ((61931520 : K[X]) * t1 ^ 5 * g1 - (10321920 : K[X])
      * t1 ^ 4 * t2 - (41287680 : K[X]) * t1 ^ 3 * u * g1 + (1433272320 :
      K[X]) * t1 ^ 3 * a1 + (5898240 : K[X]) * t1 ^ 2 * t2 * u +
      (12899450880 : K[X]) * t1 ^ 2 * g1 * a0 - (2149908480 : K[X]) * t1 *
      t2 * a0 + (5898240 : K[X]) * t1 * u ^ 2 * g1 - (716636160 : K[X]) *
      t1 * u * a1 - (491520 : K[X]) * t2 * u ^ 2 - (2149908480 : K[X]) * u
      * g1 * a0 + (522427760640 : K[X]) * a0 * a1 + Polynomial.C κ₇ *
      ((2304 : K[X]) * t1 * g1) - Polynomial.C κ₇ * ((384 : K[X]) * t2) -
      Polynomial.C κ₅ * ((73728 : K[X]) * t1 ^ 2 * g1) + Polynomial.C κ₅ *
      ((12288 : K[X]) * t1 * t2) + Polynomial.C κ₅ * ((12288 : K[X]) * u *
      g1) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) - Polynomial.C κ *
      ((35389440 : K[X]) * t1 ^ 4 * g1) + Polynomial.C κ * ((5898240 :
      K[X]) * t1 ^ 3 * t2) + Polynomial.C κ * ((17694720 : K[X]) * t1 ^ 2
      * u * g1) - Polynomial.C κ * ((859963392 : K[X]) * t1 ^ 2 * a1) -
      Polynomial.C κ * ((2359296 : K[X]) * t1 * t2 * u) - Polynomial.C κ *
      ((5159780352 : K[X]) * t1 * g1 * a0) + Polynomial.C κ * ((859963392
      : K[X]) * t2 * a0) - Polynomial.C κ * ((1179648 : K[X]) * u ^ 2 *
      g1) + Polynomial.C κ * ((286654464 : K[X]) * u * a1)) = 0 := by
    apply mul_left_cancel₀ hH
    linear_combination hR2n + (-(-((41287680 : K[X]) * t1 ^ 3 * g1 * H ^ 2) + (5898240 : K[X]) * t1 ^
      2 * t2 * H ^ 2 + (70778880 : K[X]) * t1 ^ 2 * g1 ^ 3 * H - (22118400
      : K[X]) * t1 * t2 * g1 ^ 2 * H + (5898240 : K[X]) * t1 * u * g1 * H
      ^ 2 - (4423680 : K[X]) * t1 * g1 ^ 5 + (477757440 : K[X]) * t1 * g1
      * a2 * H - (716636160 : K[X]) * t1 * a1 * H ^ 2 + (1474560 : K[X]) *
      t2 ^ 2 * g1 * H - (491520 : K[X]) * t2 * u * H ^ 2 + (1474560 :
      K[X]) * t2 * g1 ^ 4 - (39813120 : K[X]) * t2 * a2 * H - (1474560 :
      K[X]) * u * g1 ^ 3 * H - (119439360 : K[X]) * g1 ^ 3 * a2 +
      (716636160 : K[X]) * g1 ^ 2 * a1 * H - (2149908480 : K[X]) * g1 * a0
      * H ^ 2 + Polynomial.C κ₅ * ((12288 : K[X]) * g1 * H ^ 2) +
      Polynomial.C κ * ((17694720 : K[X]) * t1 ^ 2 * g1 * H ^ 2) -
      Polynomial.C κ * ((2359296 : K[X]) * t1 * t2 * H ^ 2) - Polynomial.C
      κ * ((10616832 : K[X]) * t1 * g1 ^ 3 * H) + Polynomial.C κ *
      ((2359296 : K[X]) * t2 * g1 ^ 2 * H) - Polynomial.C κ * ((1179648 :
      K[X]) * u * g1 * H ^ 2) - Polynomial.C κ * ((95551488 : K[X]) * g1 *
      a2 * H) + Polynomial.C κ * ((286654464 : K[X]) * a1 * H ^ 2))) * hu
  have hR4n :
      (-((1474560 : K[X]) * u ^ 2 * g1 ^ 3) + (716636160 : K[X]) * u * g1
      ^ 2 * a1 - (87071293440 : K[X]) * g1 * a1 ^ 2) + H * (-((5898240 :
      K[X]) * t1 ^ 3 * u * g1) + (1433272320 : K[X]) * t1 ^ 3 * a1 +
      (2949120 : K[X]) * t1 * u ^ 2 * g1 - (2949120 : K[X]) * t1 * u * t3
      * g1 ^ 2 - (716636160 : K[X]) * t1 * u * a1 + (716636160 : K[X]) *
      t1 * t3 * g1 * a1 - (2149908480 : K[X]) * u * g1 * a0 +
      (522427760640 : K[X]) * a0 * a1 + Polynomial.C κ₅ * ((12288 : K[X])
      * u * g1) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) + Polynomial.C
      κ * ((3538944 : K[X]) * t1 ^ 2 * u * g1) - Polynomial.C κ *
      ((859963392 : K[X]) * t1 ^ 2 * a1) - Polynomial.C κ * ((1179648 :
      K[X]) * u ^ 2 * g1) + Polynomial.C κ * ((1179648 : K[X]) * u * t3 *
      g1 ^ 2) + Polynomial.C κ * ((286654464 : K[X]) * u * a1) -
      Polynomial.C κ * ((286654464 : K[X]) * t3 * g1 * a1)) + H ^ 2 *
      (-((10321920 : K[X]) * t1 ^ 4 * t3) + (5898240 : K[X]) * t1 ^ 2 * u
      * t3 - (2949120 : K[X]) * t1 ^ 2 * t3 ^ 2 * g1 - (2149908480 : K[X])
      * t1 * t3 * a0 - (491520 : K[X]) * u ^ 2 * t3 + (983040 : K[X]) * u
      * t3 ^ 2 * g1 - (163840 : K[X]) * t3 ^ 3 * g1 ^ 2 - (119439360 :
      K[X]) * t3 ^ 2 * a1 - Polynomial.C κ₇ * ((384 : K[X]) * t3) +
      Polynomial.C κ₅ * ((12288 : K[X]) * t1 * t3) + Polynomial.C κ *
      ((5898240 : K[X]) * t1 ^ 3 * t3) - Polynomial.C κ * ((2359296 :
      K[X]) * t1 * u * t3) + Polynomial.C κ * ((1179648 : K[X]) * t1 * t3
      ^ 2 * g1) + Polynomial.C κ * ((859963392 : K[X]) * t3 * a0)) + H ^ 3
      * ((655360 : K[X]) * t1 * t3 ^ 3 - Polynomial.C κ * ((131072 : K[X])
      * t3 ^ 3)) = 0 := by
    apply mul_left_cancel₀ hH
    linear_combination hR3n + (-(-((10321920 : K[X]) * t1 ^ 4 * H ^ 2) + (41287680 : K[X]) * t1 ^ 3 *
      g1 ^ 2 * H - (10813440 : K[X]) * t1 ^ 2 * t2 * g1 * H + (5898240 :
      K[X]) * t1 ^ 2 * u * H ^ 2 - (6881280 : K[X]) * t1 ^ 2 * t3 * g1 * H
      ^ 2 - (5898240 : K[X]) * t1 ^ 2 * g1 ^ 4 + (655360 : K[X]) * t1 * t2
      ^ 2 * H + (655360 : K[X]) * t1 * t2 * t3 * H ^ 2 + (1966080 : K[X])
      * t1 * t2 * g1 ^ 3 - (8847360 : K[X]) * t1 * u * g1 ^ 2 * H +
      (655360 : K[X]) * t1 * t3 ^ 2 * H ^ 3 + (983040 : K[X]) * t1 * t3 *
      g1 ^ 3 * H + (1433272320 : K[X]) * t1 * g1 * a1 * H - (2149908480 :
      K[X]) * t1 * a0 * H ^ 2 - (163840 : K[X]) * t2 ^ 2 * g1 ^ 2 +
      (983040 : K[X]) * t2 * u * g1 * H - (163840 : K[X]) * t2 * t3 * g1 ^
      2 * H - (119439360 : K[X]) * t2 * a1 * H - (491520 : K[X]) * u ^ 2 *
      H ^ 2 + (983040 : K[X]) * u * t3 * g1 * H ^ 2 - (163840 : K[X]) * t3
      ^ 2 * g1 ^ 2 * H ^ 2 - (119439360 : K[X]) * t3 * a1 * H ^ 2 -
      Polynomial.C κ₇ * ((384 : K[X]) * H ^ 2) + Polynomial.C κ₅ * ((12288
      : K[X]) * t1 * H ^ 2) + Polynomial.C κ * ((5898240 : K[X]) * t1 ^ 3
      * H ^ 2) - Polynomial.C κ * ((11796480 : K[X]) * t1 ^ 2 * g1 ^ 2 *
      H) + Polynomial.C κ * ((2752512 : K[X]) * t1 * t2 * g1 * H) -
      Polynomial.C κ * ((2359296 : K[X]) * t1 * u * H ^ 2) + Polynomial.C
      κ * ((1966080 : K[X]) * t1 * t3 * g1 * H ^ 2) - Polynomial.C κ *
      ((131072 : K[X]) * t2 ^ 2 * H) - Polynomial.C κ * ((131072 : K[X]) *
      t2 * t3 * H ^ 2) + Polynomial.C κ * ((1179648 : K[X]) * u * g1 ^ 2 *
      H) - Polynomial.C κ * ((131072 : K[X]) * t3 ^ 2 * H ^ 3) -
      Polynomial.C κ * ((286654464 : K[X]) * g1 * a1 * H) + Polynomial.C κ
      * ((859963392 : K[X]) * a0 * H ^ 2))) * ht3
  simp only [alignedEleventhNonsquareResidue610]
  apply mul_left_cancel₀ (mul_ne_zero
    (show (-128 : K[X]) ≠ 0 by norm_num) (pow_ne_zero 2 hH))
  linear_combination hR4n + (-((5898240 : K[X]) * t1 ^ 3 * H - (2949120 : K[X]) * t1 * u * H +
    (2949120 : K[X]) * t1 * t3 * g1 * H + (1474560 : K[X]) * u * g1 ^ 2 -
    (491520 : K[X]) * t3 ^ 2 * H ^ 2 - (1474560 : K[X]) * v * g1 * H -
    (358318080 : K[X]) * g1 * a1 + (2149908480 : K[X]) * a0 * H -
    Polynomial.C κ₅ * ((12288 : K[X]) * H) - Polynomial.C κ * ((3538944 :
    K[X]) * t1 ^ 2 * H) + Polynomial.C κ * ((1179648 : K[X]) * u * H) -
    Polynomial.C κ * ((1179648 : K[X]) * t3 * g1 * H))) * hv

end Max11DegreeRoutes
