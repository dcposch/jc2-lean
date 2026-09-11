import Fable610ScaleTwoAlignedTenthFacePart101Scratch
import Fable610ScaleTwoAlignedEleventhFacePart101Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 6400000000 in
/-- Descent of the consumed degree-`4` row in the square chamber: the
`h₀⁴⁴`-peeled core absorbs the undecic head through the seventh-face
divisibilities and the eighth-face product divisor `u₂`, and the
carried tenth-face divisor `s₂` collapses the head to the pure
monomial `1215 μ w₁⁸`; at the root of `h₀` the head transfers to the
NEW divisibility `μ w₁⁸ = h₀ s₄`, and substituting `s₄` peels one more
`h₀` into the peeled row `= μ₄ h₀⁷`.  At the root the peeled head, the
carried facts `e₂(a) = 0` and the `u₂` root product, and the
tenth-face tie force `s₄(a) = 0`, deepening the new divisor to
`μ w₁⁸ = h₀² s₅`. -/
theorem alignedSquareEleventh_descent_610 {K : Type*} [Field K]
    [CharZero K]
    {H h0 w1 f2 e1 e2 e3 u2 s2 a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6
      b7 : K[X]}
    {κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ κ₉ μ₄ : K}
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1) (hHsq : H = h0 ^ 2)
    (hp5 : a5 = h0 ^ 4 * w1) (hp4 : a4 = h0 ^ 2 * f2)
    (hD : alignedThirdDefect610 H a3 a4 a5 b7 κ =
      Polynomial.C μ * h0 ^ 15)
    (hF : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ =
      Polynomial.C ν * h0 ^ 25)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15)
    (hI : alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ =
      Polynomial.C ν₂ * h0 ^ 35)
    (hJ : alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₇ * H ^ 20)
    (hL : alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6
        b7 κ = Polynomial.C μ₃ * h0 ^ 45)
    (hLam : alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5
        b6 b7 κ = Polynomial.C μ₄ * h0 ^ 55)
    (he1 : (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1)
    (he2 : (27 : K[X]) * a3 - w1 ^ 3 = h0 * e2)
    (hu2 : w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2)
    (hs2 : (2048 : K[X]) * e1 ^ 3 * w1 ^ 4 - Polynomial.C μ * w1 ^ 7 =
      h0 * s2)
    (he3 : e2 = h0 * e3)
    (hR10 : alignedTenthSquarePeeledRow610 h0 w1 e1 e2 u2 s2 a0 a1 a2
        b0 κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ = Polynomial.C κ₉ * h0 ^ 6) :
    ∃ s4 s5 : K[X],
      Polynomial.C μ * w1 ^ 8 = h0 * s4 ∧
      alignedEleventhSquarePeeledRow610 h0 w1 e1 e2 u2 s2 s4 a0 a1 a2
          κ μ ν κ₅ ν₂ κ₇ μ₃ = Polynomial.C μ₄ * h0 ^ 7 ∧
      s4 = h0 * s5 ∧
      Polynomial.C μ * w1 ^ 8 = h0 ^ 2 * s5 := by
  have hL' := hLam
  unfold alignedEleventhDefect610 at hL'
  rw [hD, hF, hG, hI, hJ, hL, hHsq, hp5, hp4] at hL'
  have hcore :
      ((15049359360 : K[X]) * f2 ^ 5 * w1 - (22574039040 : K[X]) * f2 ^ 4
      * a3 - (54344908800 : K[X]) * f2 ^ 4 * w1 ^ 3 + (150493593600 :
      K[X]) * f2 ^ 3 * a3 * w1 ^ 2 + (57967902720 : K[X]) * f2 ^ 3 * w1 ^
      5 - (135444234240 : K[X]) * f2 ^ 2 * a3 ^ 2 * w1 - (163034726400 :
      K[X]) * f2 ^ 2 * a3 * w1 ^ 4 - (26223575040 : K[X]) * f2 ^ 2 * w1 ^
      7 + (38698352640 : K[X]) * f2 * a3 ^ 3 + (150493593600 : K[X]) * f2
      * a3 ^ 2 * w1 ^ 3 + (57967902720 : K[X]) * f2 * a3 * w1 ^ 6 +
      (5341839360 : K[X]) * f2 * w1 ^ 9 - (45148078080 : K[X]) * a3 ^ 3 *
      w1 ^ 2 - (32606945280 : K[X]) * a3 ^ 2 * w1 ^ 5 - (6555893760 :
      K[X]) * a3 * w1 ^ 8 - (404684800 : K[X]) * w1 ^ 11) + h0 ^ 2 *
      (-((90296156160 : K[X]) * f2 ^ 3 * w1 * a2) + (116095057920 : K[X])
      * f2 ^ 2 * a3 * a2 + (150493593600 : K[X]) * f2 ^ 2 * w1 ^ 3 * a2 -
      (270888468480 : K[X]) * f2 * a3 * w1 ^ 2 * a2 - (65213890560 : K[X])
      * f2 * w1 ^ 5 * a2 + (116095057920 : K[X]) * a3 ^ 2 * w1 * a2 +
      (75246796800 : K[X]) * a3 * w1 ^ 4 * a2 + (8281128960 : K[X]) * w1 ^
      7 * a2 - Polynomial.C κ * ((2866544640 : K[X]) * f2 ^ 4 * w1) +
      Polynomial.C κ * ((4299816960 : K[X]) * f2 ^ 3 * a3) + Polynomial.C
      κ * ((7007109120 : K[X]) * f2 ^ 3 * w1 ^ 3) - Polynomial.C κ *
      ((17199267840 : K[X]) * f2 ^ 2 * a3 * w1 ^ 2) - Polynomial.C κ *
      ((4904976384 : K[X]) * f2 ^ 2 * w1 ^ 5) + Polynomial.C κ *
      ((12899450880 : K[X]) * f2 * a3 ^ 2 * w1) + Polynomial.C κ *
      ((10510663680 : K[X]) * f2 * a3 * w1 ^ 4) + Polynomial.C κ *
      ((1323565056 : K[X]) * f2 * w1 ^ 7) - Polynomial.C κ * ((2579890176
      : K[X]) * a3 ^ 3) - Polynomial.C κ * ((5733089280 : K[X]) * a3 ^ 2 *
      w1 ^ 3) - Polynomial.C κ * ((1634992128 : K[X]) * a3 * w1 ^ 6) -
      Polynomial.C κ * ((122552320 : K[X]) * w1 ^ 9)) + h0 ^ 3 *
      (-(Polynomial.C μ * ((71850240 : K[X]) * f2 ^ 4)) + Polynomial.C μ *
      ((407151360 : K[X]) * f2 ^ 3 * w1 ^ 2) - Polynomial.C μ *
      ((862202880 : K[X]) * f2 ^ 2 * a3 * w1) - Polynomial.C μ *
      ((390186720 : K[X]) * f2 ^ 2 * w1 ^ 4) + Polynomial.C μ *
      ((470292480 : K[X]) * f2 * a3 ^ 2) + Polynomial.C μ * ((814302720 :
      K[X]) * f2 * a3 * w1 ^ 3) + Polynomial.C μ * ((125726832 : K[X]) *
      f2 * w1 ^ 6) - Polynomial.C μ * ((431101440 : K[X]) * a3 ^ 2 * w1 ^
      2) - Polynomial.C μ * ((156074688 : K[X]) * a3 * w1 ^ 5) -
      Polynomial.C μ * ((13096545 : K[X]) * w1 ^ 8)) + h0 ^ 4 *
      ((38698352640 : K[X]) * f2 ^ 3 * a1 - (135444234240 : K[X]) * f2 ^ 2
      * w1 ^ 2 * a1 + (232190115840 : K[X]) * f2 * a3 * w1 * a1 +
      (75246796800 : K[X]) * f2 * w1 ^ 4 * a1 + (116095057920 : K[X]) * f2
      * w1 * a2 ^ 2 - (87071293440 : K[X]) * a3 ^ 2 * a1 - (90296156160 :
      K[X]) * a3 * w1 ^ 3 * a1 - (87071293440 : K[X]) * a3 * a2 ^ 2 -
      (10868981760 : K[X]) * w1 ^ 6 * a1 - (45148078080 : K[X]) * w1 ^ 3 *
      a2 ^ 2 + Polynomial.C κ * ((12899450880 : K[X]) * f2 ^ 2 * w1 * a2)
      - Polynomial.C κ * ((15479341056 : K[X]) * f2 * a3 * a2) -
      Polynomial.C κ * ((11466178560 : K[X]) * f2 * w1 ^ 3 * a2) +
      Polynomial.C κ * ((12899450880 : K[X]) * a3 * w1 ^ 2 * a2) +
      Polynomial.C κ * ((2102132736 : K[X]) * w1 ^ 5 * a2)) + h0 ^ 5 *
      (-(Polynomial.C ν * ((2177280 : K[X]) * f2 ^ 3)) + Polynomial.C ν *
      ((7076160 : K[X]) * f2 ^ 2 * w1 ^ 2) - Polynomial.C ν * ((13063680 :
      K[X]) * f2 * a3 * w1) - Polynomial.C ν * ((3734640 : K[X]) * f2 * w1
      ^ 4) + Polynomial.C ν * ((5598720 : K[X]) * a3 ^ 2) + Polynomial.C ν
      * ((4717440 : K[X]) * a3 * w1 ^ 3) + Polynomial.C ν * ((518700 :
      K[X]) * w1 ^ 6) + Polynomial.C μ * ((470292480 : K[X]) * f2 ^ 2 *
      a2) - Polynomial.C μ * ((862202880 : K[X]) * f2 * w1 ^ 2 * a2) +
      Polynomial.C μ * ((940584960 : K[X]) * a3 * w1 * a2) + Polynomial.C
      μ * ((203575680 : K[X]) * w1 ^ 4 * a2)) + h0 ^ 6 * ((116095057920 :
      K[X]) * f2 ^ 2 * w1 * a0 - (174142586880 : K[X]) * f2 * a3 * a0 -
      (90296156160 : K[X]) * f2 * w1 ^ 3 * a0 - (174142586880 : K[X]) * f2
      * a1 * a2 + (116095057920 : K[X]) * a3 * w1 ^ 2 * a0 + (15049359360
      : K[X]) * w1 ^ 5 * a0 + (116095057920 : K[X]) * w1 ^ 2 * a1 * a2 -
      Polynomial.C κ₅ * ((663552 : K[X]) * f2 ^ 2 * w1) + Polynomial.C κ₅
      * ((995328 : K[X]) * f2 * a3) + Polynomial.C κ₅ * ((516096 : K[X]) *
      f2 * w1 ^ 3) - Polynomial.C κ₅ * ((663552 : K[X]) * a3 * w1 ^ 2) -
      Polynomial.C κ₅ * ((86016 : K[X]) * w1 ^ 5) - Polynomial.C κ *
      ((7739670528 : K[X]) * f2 ^ 2 * a1) + Polynomial.C κ * ((12899450880
      : K[X]) * f2 * w1 ^ 2 * a1) - Polynomial.C κ * ((15479341056 : K[X])
      * a3 * w1 * a1) - Polynomial.C κ * ((2866544640 : K[X]) * w1 ^ 4 *
      a1) - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) + h0 ^ 7
      * (Polynomial.C ν₂ * ((23328 : K[X]) * f2 ^ 2) - Polynomial.C ν₂ *
      ((34992 : K[X]) * f2 * w1 ^ 2) + Polynomial.C ν₂ * ((46656 : K[X]) *
      a3 * w1) + Polynomial.C ν₂ * ((7290 : K[X]) * w1 ^ 4) + Polynomial.C
      ν * ((11197440 : K[X]) * f2 * a2) - Polynomial.C ν * ((6531840 :
      K[X]) * w1 ^ 2 * a2) + Polynomial.C μ * ((940584960 : K[X]) * f2 *
      w1 * a1) - Polynomial.C μ * ((1128701952 : K[X]) * a3 * a1) -
      Polynomial.C μ * ((287400960 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ
      * ((564350976 : K[X]) * a2 ^ 2)) + h0 ^ 8 * (-((174142586880 : K[X])
      * w1 * a0 * a2) - (87071293440 : K[X]) * w1 * a1 ^ 2 + Polynomial.C
      κ₇ * ((6912 : K[X]) * f2 * w1) - Polynomial.C κ₇ * ((10368 : K[X]) *
      a3) - Polynomial.C κ₇ * ((1920 : K[X]) * w1 ^ 3) + Polynomial.C κ₅ *
      ((995328 : K[X]) * w1 * a2) - Polynomial.C κ * ((15479341056 : K[X])
      * f2 * w1 * a0) + Polynomial.C κ * ((23219011584 : K[X]) * a3 * a0)
      + Polynomial.C κ * ((4299816960 : K[X]) * w1 ^ 3 * a0) +
      Polynomial.C κ * ((23219011584 : K[X]) * a1 * a2)) + h0 ^ 9 *
      (-(Polynomial.C μ₃ * ((48 : K[X]) * f2)) + Polynomial.C μ₃ * ((20 :
      K[X]) * w1 ^ 2) - Polynomial.C ν₂ * ((93312 : K[X]) * a2) +
      Polynomial.C ν * ((11197440 : K[X]) * w1 * a1) - Polynomial.C μ *
      ((1128701952 : K[X]) * f2 * a0) + Polynomial.C μ * ((470292480 :
      K[X]) * w1 ^ 2 * a0)) + h0 ^ 10 * ((522427760640 : K[X]) * a0 * a1 -
      Polynomial.C κ₅ * ((2985984 : K[X]) * a1)) + h0 ^ 11 *
      (-(Polynomial.C ν * ((67184640 : K[X]) * a0))) = Polynomial.C μ₄ *
      h0 ^ 11 := by
    apply mul_left_cancel₀ (pow_ne_zero 44 hh0)
    linear_combination hL'
  have hcs2 :
      (-((13271040 : K[X]) * e1 ^ 2 * w1 ^ 7) + (8847360 : K[X]) * e1 * e2
      * w1 ^ 6 - (1474560 : K[X]) * e2 ^ 2 * w1 ^ 5) + h0 * ((247726080 :
      K[X]) * e1 ^ 3 * w1 ^ 5 - (154828800 : K[X]) * e1 ^ 2 * e2 * w1 ^ 4
      + (29491200 : K[X]) * e1 * e2 ^ 2 * w1 ^ 3 - (716636160 : K[X]) * e1
      * w1 ^ 5 * a2 - (1638400 : K[X]) * e2 ^ 3 * w1 ^ 2 + (238878720 :
      K[X]) * e2 * w1 ^ 4 * a2 - Polynomial.C μ * ((945 : K[X]) * w1 ^ 8))
      + h0 ^ 2 * (-((371589120 : K[X]) * e1 ^ 4 * w1 ^ 3) + (165150720 :
      K[X]) * e1 ^ 3 * e2 * w1 ^ 2 - (20643840 : K[X]) * e1 ^ 2 * e2 ^ 2 *
      w1 + (7166361600 : K[X]) * e1 ^ 2 * w1 ^ 3 * a2 + (655360 : K[X]) *
      e1 * e2 ^ 3 - (2388787200 : K[X]) * e1 * e2 * w1 ^ 2 * a2 +
      (159252480 : K[X]) * e2 ^ 2 * w1 * a2 - (9674588160 : K[X]) * w1 ^ 3
      * a2 ^ 2 + Polynomial.C μ * ((63504 : K[X]) * e1 * w1 ^ 6) -
      Polynomial.C μ * ((28224 : K[X]) * e2 * w1 ^ 5) - Polynomial.C κ *
      ((31850496 : K[X]) * e1 ^ 2 * w1 ^ 5) + Polynomial.C κ * ((17694720
      : K[X]) * e1 * e2 * w1 ^ 4) - Polynomial.C κ * ((2359296 : K[X]) *
      e2 ^ 2 * w1 ^ 3)) + h0 ^ 3 * ((61931520 : K[X]) * e1 ^ 5 * w1 -
      (10321920 : K[X]) * e1 ^ 4 * e2 - (3344302080 : K[X]) * e1 ^ 3 * w1
      * a2 + (477757440 : K[X]) * e1 ^ 2 * e2 * a2 + (2149908480 : K[X]) *
      e1 * w1 ^ 4 * a1 + (38698352640 : K[X]) * e1 * w1 * a2 ^ 2 -
      (716636160 : K[X]) * e2 * w1 ^ 3 * a1 - (3224862720 : K[X]) * e2 *
      a2 ^ 2 + Polynomial.C ν * ((540 : K[X]) * w1 ^ 6) - Polynomial.C μ *
      ((6985440 : K[X]) * e1 ^ 2 * w1 ^ 4) + Polynomial.C μ * ((3386880 :
      K[X]) * e1 * e2 * w1 ^ 3) - Polynomial.C μ * ((376320 : K[X]) * e2 ^
      2 * w1 ^ 2) + Polynomial.C μ * ((3265920 : K[X]) * w1 ^ 4 * a2) +
      Polynomial.C κ * ((123863040 : K[X]) * e1 ^ 3 * w1 ^ 3) -
      Polynomial.C κ * ((53084160 : K[X]) * e1 ^ 2 * e2 * w1 ^ 2) +
      Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 ^ 2 * w1) -
      Polynomial.C κ * ((1146617856 : K[X]) * e1 * w1 ^ 3 * a2) -
      Polynomial.C κ * ((131072 : K[X]) * e2 ^ 3) + Polynomial.C κ *
      ((286654464 : K[X]) * e2 * w1 ^ 2 * a2)) + h0 ^ 4 * (-((10749542400
      : K[X]) * e1 ^ 2 * w1 ^ 2 * a1) + (2866544640 : K[X]) * e1 * e2 * w1
      * a1 - (119439360 : K[X]) * e2 ^ 2 * a1 + (58047528960 : K[X]) * w1
      ^ 2 * a1 * a2 - Polynomial.C ν * ((75600 : K[X]) * e1 * w1 ^ 4) +
      Polynomial.C ν * ((28800 : K[X]) * e2 * w1 ^ 3) + Polynomial.C μ *
      ((11531520 : K[X]) * e1 ^ 3 * w1 ^ 2) - Polynomial.C μ * ((3548160 :
      K[X]) * e1 ^ 2 * e2 * w1) + Polynomial.C μ * ((215040 : K[X]) * e1 *
      e2 ^ 2) - Polynomial.C μ * ((182891520 : K[X]) * e1 * w1 ^ 2 * a2) +
      Polynomial.C μ * ((34836480 : K[X]) * e2 * w1 * a2) - Polynomial.C κ
      * ((35389440 : K[X]) * e1 ^ 4 * w1) + Polynomial.C κ * ((5898240 :
      K[X]) * e1 ^ 3 * e2) + Polynomial.C κ * ((1433272320 : K[X]) * e1 ^
      2 * w1 * a2) - Polynomial.C κ * ((191102976 : K[X]) * e1 * e2 * a2)
      - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) + h0 ^ 5 *
      ((1433272320 : K[X]) * e1 ^ 3 * a1 - (6449725440 : K[X]) * e1 * w1 ^
      3 * a0 - (58047528960 : K[X]) * e1 * a1 * a2 + (2149908480 : K[X]) *
      e2 * w1 ^ 2 * a0 - Polynomial.C ν₂ * ((54 : K[X]) * w1 ^ 4) +
      Polynomial.C κ₅ * ((36864 : K[X]) * e1 * w1 ^ 3) - Polynomial.C κ₅ *
      ((12288 : K[X]) * e2 * w1 ^ 2) + Polynomial.C ν * ((544320 : K[X]) *
      e1 ^ 2 * w1 ^ 2) - Polynomial.C ν * ((161280 : K[X]) * e1 * e2 * w1)
      + Polynomial.C ν * ((7680 : K[X]) * e2 ^ 2) - Polynomial.C ν *
      ((2799360 : K[X]) * w1 ^ 2 * a2) - Polynomial.C μ * ((887040 : K[X])
      * e1 ^ 4) + Polynomial.C μ * ((52254720 : K[X]) * e1 ^ 2 * a2) -
      Polynomial.C μ * ((15676416 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ
      * ((564350976 : K[X]) * a2 ^ 2) + Polynomial.C κ * ((2579890176 :
      K[X]) * e1 * w1 ^ 2 * a1) - Polynomial.C κ * ((573308928 : K[X]) *
      e2 * w1 * a1)) + h0 ^ 6 * ((12899450880 : K[X]) * e1 ^ 2 * w1 * a0 -
      (2149908480 : K[X]) * e1 * e2 * a0 - (174142586880 : K[X]) * w1 * a0
      * a2 - (87071293440 : K[X]) * w1 * a1 ^ 2 - Polynomial.C ν₂ * ((6480
      : K[X]) * e1 * w1 ^ 2) + Polynomial.C ν₂ * ((1728 : K[X]) * e2 * w1)
      - Polynomial.C κ₅ * ((73728 : K[X]) * e1 ^ 2 * w1) + Polynomial.C κ₅
      * ((12288 : K[X]) * e1 * e2) + Polynomial.C κ₅ * ((995328 : K[X]) *
      w1 * a2) - Polynomial.C ν * ((80640 : K[X]) * e1 ^ 3) + Polynomial.C
      ν * ((3732480 : K[X]) * e1 * a2) + Polynomial.C μ * ((313528320 :
      K[X]) * e1 * w1 * a1) - Polynomial.C μ * ((41803776 : K[X]) * e2 *
      a1) - Polynomial.C κ * ((859963392 : K[X]) * e1 ^ 2 * a1) +
      Polynomial.C κ * ((23219011584 : K[X]) * a1 * a2)) + h0 ^ 7 *
      (Polynomial.C μ₃ * ((4 : K[X]) * w1 ^ 2) + Polynomial.C κ₇ * ((2304
      : K[X]) * e1 * w1) - Polynomial.C κ₇ * ((384 : K[X]) * e2) +
      Polynomial.C ν₂ * ((2592 : K[X]) * e1 ^ 2) - Polynomial.C ν₂ *
      ((93312 : K[X]) * a2) + Polynomial.C ν * ((11197440 : K[X]) * w1 *
      a1) + Polynomial.C μ * ((94058496 : K[X]) * w1 ^ 2 * a0) -
      Polynomial.C κ * ((5159780352 : K[X]) * e1 * w1 * a0) + Polynomial.C
      κ * ((859963392 : K[X]) * e2 * a0)) + h0 ^ 8 * ((522427760640 :
      K[X]) * a0 * a1 - Polynomial.C μ₃ * ((16 : K[X]) * e1) -
      Polynomial.C κ₅ * ((2985984 : K[X]) * a1) - Polynomial.C μ *
      ((376233984 : K[X]) * e1 * a0)) + h0 ^ 9 * (-(Polynomial.C ν *
      ((67184640 : K[X]) * a0))) = Polynomial.C μ₄ * h0 ^ 9 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    linear_combination hcore + (-((61931520 : K[X]) * e1 ^ 4 * w1 * h0 ^ 4 - (423198720 : K[X]) * e1 ^
      3 * w1 ^ 3 * h0 ^ 3 + (185794560 : K[X]) * e1 ^ 3 * w1 * f2 * h0 ^ 3
      - (278691840 : K[X]) * e1 ^ 3 * a3 * h0 ^ 3 + (505774080 : K[X]) *
      e1 ^ 2 * w1 ^ 5 * h0 ^ 2 - (1455390720 : K[X]) * e1 ^ 2 * w1 ^ 3 *
      f2 * h0 ^ 2 + (4737761280 : K[X]) * e1 ^ 2 * w1 ^ 2 * a3 * h0 ^ 2 +
      (557383680 : K[X]) * e1 ^ 2 * w1 * f2 ^ 2 * h0 ^ 2 - (3344302080 :
      K[X]) * e1 ^ 2 * w1 * a2 * h0 ^ 4 - (836075520 : K[X]) * e1 ^ 2 * f2
      * a3 * h0 ^ 2 + (1433272320 : K[X]) * e1 ^ 2 * a1 * h0 ^ 6 -
      (384860160 : K[X]) * e1 * w1 ^ 7 * h0 + (2972712960 : K[X]) * e1 *
      w1 ^ 5 * f2 * h0 - (7803371520 : K[X]) * e1 * w1 ^ 4 * a3 * h0 -
      (4923555840 : K[X]) * e1 * w1 ^ 3 * f2 ^ 2 * h0 + (10032906240 :
      K[X]) * e1 * w1 ^ 3 * a2 * h0 ^ 3 + (15049359360 : K[X]) * e1 * w1 ^
      2 * f2 * a3 * h0 - (12182814720 : K[X]) * e1 * w1 ^ 2 * a1 * h0 ^ 5
      + (1672151040 : K[X]) * e1 * w1 * f2 ^ 3 * h0 - (10032906240 : K[X])
      * e1 * w1 * f2 * a2 * h0 ^ 3 - (15049359360 : K[X]) * e1 * w1 * a3 ^
      2 * h0 + (12899450880 : K[X]) * e1 * w1 * a0 * h0 ^ 7 - (2508226560
      : K[X]) * e1 * f2 ^ 2 * a3 * h0 + (4299816960 : K[X]) * e1 * f2 * a1
      * h0 ^ 5 + (12899450880 : K[X]) * e1 * a3 * a2 * h0 ^ 3 + (404848640
      : K[X]) * w1 ^ 9 - (4127293440 : K[X]) * w1 ^ 7 * f2 + (6502809600 :
      K[X]) * w1 ^ 6 * a3 + (13841694720 : K[X]) * w1 ^ 5 * f2 ^ 2 -
      (8360755200 : K[X]) * w1 ^ 5 * a2 * h0 ^ 2 - (38459473920 : K[X]) *
      w1 ^ 4 * f2 * a3 + (11466178560 : K[X]) * w1 ^ 4 * a1 * h0 ^ 4 -
      (16442818560 : K[X]) * w1 ^ 3 * f2 ^ 3 + (40131624960 : K[X]) * w1 ^
      3 * f2 * a2 * h0 ^ 2 + (35115171840 : K[X]) * w1 ^ 3 * a3 ^ 2 -
      (17199267840 : K[X]) * w1 ^ 3 * a0 * h0 ^ 6 + (47656304640 : K[X]) *
      w1 ^ 2 * f2 ^ 2 * a3 - (40848261120 : K[X]) * w1 ^ 2 * f2 * a1 * h0
      ^ 4 - (77396705280 : K[X]) * w1 ^ 2 * a3 * a2 * h0 ^ 2 + (5016453120
      : K[X]) * w1 * f2 ^ 4 - (30098718720 : K[X]) * w1 * f2 ^ 2 * a2 * h0
      ^ 2 - (45148078080 : K[X]) * w1 * f2 * a3 ^ 2 + (38698352640 : K[X])
      * w1 * f2 * a0 * h0 ^ 6 + (77396705280 : K[X]) * w1 * a3 * a1 * h0 ^
      4 + (38698352640 : K[X]) * w1 * a2 ^ 2 * h0 ^ 4 - (7524679680 :
      K[X]) * f2 ^ 3 * a3 + (12899450880 : K[X]) * f2 ^ 2 * a1 * h0 ^ 4 +
      (38698352640 : K[X]) * f2 * a3 * a2 * h0 ^ 2 + (12899450880 : K[X])
      * a3 ^ 3 - (58047528960 : K[X]) * a3 * a0 * h0 ^ 6 - (58047528960 :
      K[X]) * a1 * a2 * h0 ^ 6 - Polynomial.C μ₃ * ((16 : K[X]) * h0 ^ 9)
      + Polynomial.C κ₇ * ((2304 : K[X]) * w1 * h0 ^ 8) + Polynomial.C ν₂
      * ((2592 : K[X]) * e1 * h0 ^ 8) - Polynomial.C ν₂ * ((9072 : K[X]) *
      w1 ^ 2 * h0 ^ 7) + Polynomial.C ν₂ * ((7776 : K[X]) * f2 * h0 ^ 7) -
      Polynomial.C κ₅ * ((73728 : K[X]) * e1 * w1 * h0 ^ 7) + Polynomial.C
      κ₅ * ((98304 : K[X]) * w1 ^ 3 * h0 ^ 6) - Polynomial.C κ₅ * ((221184
      : K[X]) * w1 * f2 * h0 ^ 6) + Polynomial.C κ₅ * ((331776 : K[X]) *
      a3 * h0 ^ 6) - Polynomial.C ν * ((80640 : K[X]) * e1 ^ 2 * h0 ^ 7) +
      Polynomial.C ν * ((624960 : K[X]) * e1 * w1 ^ 2 * h0 ^ 6) -
      Polynomial.C ν * ((241920 : K[X]) * e1 * f2 * h0 ^ 6) - Polynomial.C
      ν * ((539280 : K[X]) * w1 ^ 4 * h0 ^ 5) + Polynomial.C ν * ((2116800
      : K[X]) * w1 ^ 2 * f2 * h0 ^ 5) - Polynomial.C ν * ((4354560 : K[X])
      * w1 * a3 * h0 ^ 5) - Polynomial.C ν * ((725760 : K[X]) * f2 ^ 2 *
      h0 ^ 5) + Polynomial.C ν * ((3732480 : K[X]) * a2 * h0 ^ 7) -
      Polynomial.C μ * ((887040 : K[X]) * e1 ^ 3 * h0 ^ 6) + Polynomial.C
      μ * ((12418560 : K[X]) * e1 ^ 2 * w1 ^ 2 * h0 ^ 5) - Polynomial.C μ
      * ((2661120 : K[X]) * e1 ^ 2 * f2 * h0 ^ 5) - Polynomial.C μ *
      ((15855840 : K[X]) * e1 * w1 ^ 4 * h0 ^ 4) + Polynomial.C μ *
      ((39916800 : K[X]) * e1 * w1 ^ 2 * f2 * h0 ^ 4) - Polynomial.C μ *
      ((95800320 : K[X]) * e1 * w1 * a3 * h0 ^ 4) - Polynomial.C μ *
      ((7983360 : K[X]) * e1 * f2 ^ 2 * h0 ^ 4) + Polynomial.C μ *
      ((52254720 : K[X]) * e1 * a2 * h0 ^ 6) + Polynomial.C μ * ((12747504
      : K[X]) * w1 ^ 6 * h0 ^ 3) - Polynomial.C μ * ((87484320 : K[X]) *
      w1 ^ 4 * f2 * h0 ^ 3) + Polynomial.C μ * ((175633920 : K[X]) * w1 ^
      3 * a3 * h0 ^ 3) + Polynomial.C μ * ((127733760 : K[X]) * w1 ^ 2 *
      f2 ^ 2 * h0 ^ 3) - Polynomial.C μ * ((235146240 : K[X]) * w1 ^ 2 *
      a2 * h0 ^ 5) - Polynomial.C μ * ((287400960 : K[X]) * w1 * f2 * a3 *
      h0 ^ 3) + Polynomial.C μ * ((313528320 : K[X]) * w1 * a1 * h0 ^ 7) -
      Polynomial.C μ * ((23950080 : K[X]) * f2 ^ 3 * h0 ^ 3) +
      Polynomial.C μ * ((156764160 : K[X]) * f2 * a2 * h0 ^ 5) +
      Polynomial.C μ * ((156764160 : K[X]) * a3 ^ 2 * h0 ^ 3) -
      Polynomial.C μ * ((376233984 : K[X]) * a0 * h0 ^ 9) - Polynomial.C κ
      * ((35389440 : K[X]) * e1 ^ 3 * w1 * h0 ^ 5) + Polynomial.C κ *
      ((153354240 : K[X]) * e1 ^ 2 * w1 ^ 3 * h0 ^ 4) - Polynomial.C κ *
      ((106168320 : K[X]) * e1 ^ 2 * w1 * f2 * h0 ^ 4) + Polynomial.C κ *
      ((159252480 : K[X]) * e1 ^ 2 * a3 * h0 ^ 4) - Polynomial.C κ *
      ((132120576 : K[X]) * e1 * w1 ^ 5 * h0 ^ 3) + Polynomial.C κ *
      ((566231040 : K[X]) * e1 * w1 ^ 3 * f2 * h0 ^ 3) - Polynomial.C κ *
      ((1592524800 : K[X]) * e1 * w1 ^ 2 * a3 * h0 ^ 3) - Polynomial.C κ *
      ((318504960 : K[X]) * e1 * w1 * f2 ^ 2 * h0 ^ 3) + Polynomial.C κ *
      ((1433272320 : K[X]) * e1 * w1 * a2 * h0 ^ 5) + Polynomial.C κ *
      ((477757440 : K[X]) * e1 * f2 * a3 * h0 ^ 3) - Polynomial.C κ *
      ((859963392 : K[X]) * e1 * a1 * h0 ^ 7) + Polynomial.C κ *
      ((120324096 : K[X]) * w1 ^ 7 * h0 ^ 2) - Polynomial.C κ *
      ((962592768 : K[X]) * w1 ^ 5 * f2 * h0 ^ 2) + Polynomial.C κ *
      ((1751777280 : K[X]) * w1 ^ 4 * a3 * h0 ^ 2) + Polynomial.C κ *
      ((2017198080 : K[X]) * w1 ^ 3 * f2 ^ 2 * h0 ^ 2) - Polynomial.C κ *
      ((2388787200 : K[X]) * w1 ^ 3 * a2 * h0 ^ 4) - Polynomial.C κ *
      ((5255331840 : K[X]) * w1 ^ 2 * f2 * a3 * h0 ^ 2) + Polynomial.C κ *
      ((3439853568 : K[X]) * w1 ^ 2 * a1 * h0 ^ 6) - Polynomial.C κ *
      ((955514880 : K[X]) * w1 * f2 ^ 3 * h0 ^ 2) + Polynomial.C κ *
      ((4299816960 : K[X]) * w1 * f2 * a2 * h0 ^ 4) + Polynomial.C κ *
      ((4299816960 : K[X]) * w1 * a3 ^ 2 * h0 ^ 2) - Polynomial.C κ *
      ((5159780352 : K[X]) * w1 * a0 * h0 ^ 8) + Polynomial.C κ *
      ((1433272320 : K[X]) * f2 ^ 2 * a3 * h0 ^ 2) - Polynomial.C κ *
      ((2579890176 : K[X]) * f2 * a1 * h0 ^ 6) - Polynomial.C κ *
      ((5159780352 : K[X]) * a3 * a2 * h0 ^ 4))) * he1 + (-(-((10321920 :
      K[X]) * e1 ^ 4 * h0 ^ 4) + (165150720 : K[X]) * e1 ^ 3 * w1 ^ 2 * h0
      ^ 3 - (20643840 : K[X]) * e1 ^ 2 * e2 * w1 * h0 ^ 3 - (134184960 :
      K[X]) * e1 ^ 2 * w1 ^ 4 * h0 ^ 2 - (557383680 : K[X]) * e1 ^ 2 * w1
      * a3 * h0 ^ 2 + (477757440 : K[X]) * e1 ^ 2 * a2 * h0 ^ 4 + (655360
      : K[X]) * e1 * e2 ^ 2 * h0 ^ 3 + (28835840 : K[X]) * e1 * e2 * w1 ^
      3 * h0 ^ 2 + (17694720 : K[X]) * e1 * e2 * a3 * h0 ^ 2 - (19988480 :
      K[X]) * e1 * w1 ^ 6 * h0 + (760872960 : K[X]) * e1 * w1 ^ 3 * a3 *
      h0 - (2388787200 : K[X]) * e1 * w1 ^ 2 * a2 * h0 ^ 3 + (2866544640 :
      K[X]) * e1 * w1 * a1 * h0 ^ 5 + (477757440 : K[X]) * e1 * a3 ^ 2 *
      h0 - (2149908480 : K[X]) * e1 * a0 * h0 ^ 7 - (1638400 : K[X]) * e2
      ^ 2 * w1 ^ 2 * h0 ^ 2 + (163840 : K[X]) * e2 * w1 ^ 5 * h0 -
      (44236800 : K[X]) * e2 * w1 ^ 2 * a3 * h0 + (159252480 : K[X]) * e2
      * w1 * a2 * h0 ^ 3 - (119439360 : K[X]) * e2 * a1 * h0 ^ 5 - (163840
      : K[X]) * w1 ^ 8 + (48660480 : K[X]) * w1 ^ 5 * a3 + (79626240 :
      K[X]) * w1 ^ 4 * a2 * h0 ^ 2 - (597196800 : K[X]) * w1 ^ 3 * a1 * h0
      ^ 4 - (1194393600 : K[X]) * w1 ^ 2 * a3 ^ 2 + (2149908480 : K[X]) *
      w1 ^ 2 * a0 * h0 ^ 6 + (4299816960 : K[X]) * w1 * a3 * a2 * h0 ^ 2 -
      (3224862720 : K[X]) * a3 * a1 * h0 ^ 4 - (3224862720 : K[X]) * a2 ^
      2 * h0 ^ 4 - Polynomial.C κ₇ * ((384 : K[X]) * h0 ^ 8) +
      Polynomial.C ν₂ * ((1728 : K[X]) * w1 * h0 ^ 7) + Polynomial.C κ₅ *
      ((12288 : K[X]) * e1 * h0 ^ 7) - Polynomial.C κ₅ * ((12288 : K[X]) *
      w1 ^ 2 * h0 ^ 6) - Polynomial.C ν * ((161280 : K[X]) * e1 * w1 * h0
      ^ 6) + Polynomial.C ν * ((7680 : K[X]) * e2 * h0 ^ 6) + Polynomial.C
      ν * ((21120 : K[X]) * w1 ^ 3 * h0 ^ 5) + Polynomial.C ν * ((207360 :
      K[X]) * a3 * h0 ^ 5) - Polynomial.C μ * ((3548160 : K[X]) * e1 ^ 2 *
      w1 * h0 ^ 5) + Polynomial.C μ * ((215040 : K[X]) * e1 * e2 * h0 ^ 5)
      + Polynomial.C μ * ((3171840 : K[X]) * e1 * w1 ^ 3 * h0 ^ 4) +
      Polynomial.C μ * ((5806080 : K[X]) * e1 * a3 * h0 ^ 4) -
      Polynomial.C μ * ((376320 : K[X]) * e2 * w1 ^ 2 * h0 ^ 4) +
      Polynomial.C μ * ((348096 : K[X]) * w1 ^ 5 * h0 ^ 3) - Polynomial.C
      μ * ((10160640 : K[X]) * w1 ^ 2 * a3 * h0 ^ 3) + Polynomial.C μ *
      ((34836480 : K[X]) * w1 * a2 * h0 ^ 5) - Polynomial.C μ * ((41803776
      : K[X]) * a1 * h0 ^ 7) + Polynomial.C κ * ((5898240 : K[X]) * e1 ^ 3
      * h0 ^ 5) - Polynomial.C κ * ((53084160 : K[X]) * e1 ^ 2 * w1 ^ 2 *
      h0 ^ 4) + Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 * w1 * h0 ^
      4) + Polynomial.C κ * ((11796480 : K[X]) * e1 * w1 ^ 4 * h0 ^ 3) +
      Polynomial.C κ * ((159252480 : K[X]) * e1 * w1 * a3 * h0 ^ 3) -
      Polynomial.C κ * ((191102976 : K[X]) * e1 * a2 * h0 ^ 5) -
      Polynomial.C κ * ((131072 : K[X]) * e2 ^ 2 * h0 ^ 4) - Polynomial.C
      κ * ((2228224 : K[X]) * e2 * w1 ^ 3 * h0 ^ 3) - Polynomial.C κ *
      ((3538944 : K[X]) * e2 * a3 * h0 ^ 3) + Polynomial.C κ * ((2228224 :
      K[X]) * w1 ^ 6 * h0 ^ 2) - Polynomial.C κ * ((56623104 : K[X]) * w1
      ^ 3 * a3 * h0 ^ 2) + Polynomial.C κ * ((286654464 : K[X]) * w1 ^ 2 *
      a2 * h0 ^ 4) - Polynomial.C κ * ((573308928 : K[X]) * w1 * a1 * h0 ^
      6) - Polynomial.C κ * ((95551488 : K[X]) * a3 ^ 2 * h0 ^ 2) +
      Polynomial.C κ * ((859963392 : K[X]) * a0 * h0 ^ 8))) * he2
  have hRq :
      ((4423680 : K[X]) * e1 ^ 3 * w1 ^ 5 - Polynomial.C μ * ((945 : K[X])
      * w1 ^ 8)) + h0 * (-((61931520 : K[X]) * e1 ^ 4 * w1 ^ 3) -
      (22118400 : K[X]) * e1 ^ 2 * u2 * w1 ^ 3 + (1433272320 : K[X]) * e1
      ^ 2 * w1 ^ 3 * a2 + (655360 : K[X]) * e1 * e2 ^ 3 - (1474560 : K[X])
      * u2 ^ 2 * w1 ^ 3 + (238878720 : K[X]) * u2 * w1 ^ 3 * a2 -
      (9674588160 : K[X]) * w1 ^ 3 * a2 ^ 2 - Polynomial.C μ * ((21168 :
      K[X]) * e1 * w1 ^ 6)) + h0 ^ 2 * ((61931520 : K[X]) * e1 ^ 5 * w1 -
      (10321920 : K[X]) * e1 ^ 4 * e2 + (103219200 : K[X]) * e1 ^ 3 * u2 *
      w1 - (3344302080 : K[X]) * e1 ^ 3 * w1 * a2 - (20643840 : K[X]) * e1
      ^ 2 * e2 * u2 + (477757440 : K[X]) * e1 ^ 2 * e2 * a2 + (19660800 :
      K[X]) * e1 * u2 ^ 2 * w1 - (1911029760 : K[X]) * e1 * u2 * w1 * a2 +
      (38698352640 : K[X]) * e1 * w1 * a2 ^ 2 - (1638400 : K[X]) * e2 * u2
      ^ 2 + (159252480 : K[X]) * e2 * u2 * a2 - (3224862720 : K[X]) * e2 *
      a2 ^ 2 + Polynomial.C ν * ((540 : K[X]) * w1 ^ 6) - Polynomial.C μ *
      ((211680 : K[X]) * e1 ^ 2 * w1 ^ 4) - Polynomial.C μ * ((28224 :
      K[X]) * u2 * w1 ^ 4) + Polynomial.C μ * ((3265920 : K[X]) * w1 ^ 4 *
      a2) + Polynomial.C κ * ((17694720 : K[X]) * e1 ^ 3 * w1 ^ 3) +
      Polynomial.C κ * ((3538944 : K[X]) * e1 * u2 * w1 ^ 3) -
      Polynomial.C κ * ((286654464 : K[X]) * e1 * w1 ^ 3 * a2) -
      Polynomial.C κ * ((131072 : K[X]) * e2 ^ 3)) + h0 ^ 3 *
      (-((2149908480 : K[X]) * e1 ^ 2 * w1 ^ 2 * a1) - (119439360 : K[X])
      * e2 ^ 2 * a1 - (716636160 : K[X]) * u2 * w1 ^ 2 * a1 + (58047528960
      : K[X]) * w1 ^ 2 * a1 * a2 + Polynomial.C ν * ((10800 : K[X]) * e1 *
      w1 ^ 4) + Polynomial.C μ * ((887040 : K[X]) * e1 ^ 3 * w1 ^ 2) +
      Polynomial.C μ * ((215040 : K[X]) * e1 * e2 ^ 2) + Polynomial.C μ *
      ((1128960 : K[X]) * e1 * u2 * w1 ^ 2) - Polynomial.C μ * ((78382080
      : K[X]) * e1 * w1 ^ 2 * a2) - Polynomial.C κ * ((35389440 : K[X]) *
      e1 ^ 4 * w1) + Polynomial.C κ * ((5898240 : K[X]) * e1 ^ 3 * e2) -
      Polynomial.C κ * ((35389440 : K[X]) * e1 ^ 2 * u2 * w1) +
      Polynomial.C κ * ((1433272320 : K[X]) * e1 ^ 2 * w1 * a2) +
      Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 * u2) - Polynomial.C κ
      * ((191102976 : K[X]) * e1 * e2 * a2) - Polynomial.C κ * ((2359296 :
      K[X]) * u2 ^ 2 * w1) + Polynomial.C κ * ((286654464 : K[X]) * u2 *
      w1 * a2) - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) +
      h0 ^ 4 * ((1433272320 : K[X]) * e1 ^ 3 * a1 + (2866544640 : K[X]) *
      e1 * u2 * a1 - (58047528960 : K[X]) * e1 * a1 * a2 - Polynomial.C ν₂
      * ((54 : K[X]) * w1 ^ 4) + Polynomial.C ν * ((60480 : K[X]) * e1 ^ 2
      * w1 ^ 2) + Polynomial.C ν * ((7680 : K[X]) * e2 ^ 2) + Polynomial.C
      ν * ((28800 : K[X]) * u2 * w1 ^ 2) - Polynomial.C ν * ((2799360 :
      K[X]) * w1 ^ 2 * a2) - Polynomial.C μ * ((887040 : K[X]) * e1 ^ 4) -
      Polynomial.C μ * ((3548160 : K[X]) * e1 ^ 2 * u2) + Polynomial.C μ *
      ((52254720 : K[X]) * e1 ^ 2 * a2) - Polynomial.C μ * ((376320 :
      K[X]) * u2 ^ 2) + Polynomial.C μ * ((34836480 : K[X]) * u2 * a2) -
      Polynomial.C μ * ((15676416 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ
      * ((564350976 : K[X]) * a2 ^ 2) + Polynomial.C κ * ((859963392 :
      K[X]) * e1 * w1 ^ 2 * a1)) + h0 ^ 5 * ((12899450880 : K[X]) * e1 ^ 2
      * w1 * a0 - (2149908480 : K[X]) * e1 * e2 * a0 + (2149908480 : K[X])
      * u2 * w1 * a0 - (174142586880 : K[X]) * w1 * a0 * a2 - (87071293440
      : K[X]) * w1 * a1 ^ 2 - Polynomial.C ν₂ * ((1296 : K[X]) * e1 * w1 ^
      2) - Polynomial.C κ₅ * ((73728 : K[X]) * e1 ^ 2 * w1) + Polynomial.C
      κ₅ * ((12288 : K[X]) * e1 * e2) - Polynomial.C κ₅ * ((12288 : K[X])
      * u2 * w1) + Polynomial.C κ₅ * ((995328 : K[X]) * w1 * a2) -
      Polynomial.C ν * ((80640 : K[X]) * e1 ^ 3) - Polynomial.C ν *
      ((161280 : K[X]) * e1 * u2) + Polynomial.C ν * ((3732480 : K[X]) *
      e1 * a2) + Polynomial.C μ * ((313528320 : K[X]) * e1 * w1 * a1) -
      Polynomial.C μ * ((41803776 : K[X]) * e2 * a1) - Polynomial.C κ *
      ((859963392 : K[X]) * e1 ^ 2 * a1) - Polynomial.C κ * ((573308928 :
      K[X]) * u2 * a1) + Polynomial.C κ * ((23219011584 : K[X]) * a1 *
      a2)) + h0 ^ 6 * (Polynomial.C μ₃ * ((4 : K[X]) * w1 ^ 2) +
      Polynomial.C κ₇ * ((2304 : K[X]) * e1 * w1) - Polynomial.C κ₇ *
      ((384 : K[X]) * e2) + Polynomial.C ν₂ * ((2592 : K[X]) * e1 ^ 2) +
      Polynomial.C ν₂ * ((1728 : K[X]) * u2) - Polynomial.C ν₂ * ((93312 :
      K[X]) * a2) + Polynomial.C ν * ((11197440 : K[X]) * w1 * a1) +
      Polynomial.C μ * ((94058496 : K[X]) * w1 ^ 2 * a0) - Polynomial.C κ
      * ((5159780352 : K[X]) * e1 * w1 * a0) + Polynomial.C κ *
      ((859963392 : K[X]) * e2 * a0)) + h0 ^ 7 * ((522427760640 : K[X]) *
      a0 * a1 - Polynomial.C μ₃ * ((16 : K[X]) * e1) - Polynomial.C κ₅ *
      ((2985984 : K[X]) * a1) - Polynomial.C μ * ((376233984 : K[X]) * e1
      * a0)) + h0 ^ 8 * (-(Polynomial.C ν * ((67184640 : K[X]) * a0))) =
      Polynomial.C μ₄ * h0 ^ 8 := by
    apply mul_left_cancel₀ hh0
    linear_combination hcs2 + (-((103219200 : K[X]) * e1 ^ 3 * w1 * h0 ^ 2 - (20643840 : K[X]) * e1 ^
      2 * e2 * h0 ^ 2 - (81100800 : K[X]) * e1 ^ 2 * w1 ^ 3 * h0 +
      (24576000 : K[X]) * e1 * e2 * w1 ^ 2 * h0 + (19660800 : K[X]) * e1 *
      u2 * w1 * h0 ^ 2 + (4423680 : K[X]) * e1 * w1 ^ 5 - (1911029760 :
      K[X]) * e1 * w1 * a2 * h0 ^ 2 + (2866544640 : K[X]) * e1 * a1 * h0 ^
      4 - (1638400 : K[X]) * e2 ^ 2 * w1 * h0 - (1638400 : K[X]) * e2 * u2
      * h0 ^ 2 - (1474560 : K[X]) * e2 * w1 ^ 4 + (159252480 : K[X]) * e2
      * a2 * h0 ^ 2 - (1474560 : K[X]) * u2 * w1 ^ 3 * h0 + (238878720 :
      K[X]) * w1 ^ 3 * a2 * h0 - (716636160 : K[X]) * w1 ^ 2 * a1 * h0 ^ 3
      + (2149908480 : K[X]) * w1 * a0 * h0 ^ 5 + Polynomial.C ν₂ * ((1728
      : K[X]) * h0 ^ 6) - Polynomial.C κ₅ * ((12288 : K[X]) * w1 * h0 ^ 5)
      - Polynomial.C ν * ((161280 : K[X]) * e1 * h0 ^ 5) + Polynomial.C ν
      * ((28800 : K[X]) * w1 ^ 2 * h0 ^ 4) - Polynomial.C μ * ((3548160 :
      K[X]) * e1 ^ 2 * h0 ^ 4) + Polynomial.C μ * ((2257920 : K[X]) * e1 *
      w1 ^ 2 * h0 ^ 3) - Polynomial.C μ * ((376320 : K[X]) * e2 * w1 * h0
      ^ 3) - Polynomial.C μ * ((376320 : K[X]) * u2 * h0 ^ 4) -
      Polynomial.C μ * ((28224 : K[X]) * w1 ^ 4 * h0 ^ 2) + Polynomial.C μ
      * ((34836480 : K[X]) * a2 * h0 ^ 4) - Polynomial.C κ * ((35389440 :
      K[X]) * e1 ^ 2 * w1 * h0 ^ 3) + Polynomial.C κ * ((5898240 : K[X]) *
      e1 * e2 * h0 ^ 3) + Polynomial.C κ * ((10616832 : K[X]) * e1 * w1 ^
      3 * h0 ^ 2) - Polynomial.C κ * ((2359296 : K[X]) * e2 * w1 ^ 2 * h0
      ^ 2) - Polynomial.C κ * ((2359296 : K[X]) * u2 * w1 * h0 ^ 3) +
      Polynomial.C κ * ((286654464 : K[X]) * w1 * a2 * h0 ^ 3) -
      Polynomial.C κ * ((573308928 : K[X]) * a1 * h0 ^ 5))) * hu2
  have hR2q :
      (Polynomial.C μ * ((1215 : K[X]) * w1 ^ 8)) + h0 * (-((61931520 :
      K[X]) * e1 ^ 4 * w1 ^ 3) - (22118400 : K[X]) * e1 ^ 2 * u2 * w1 ^ 3
      + (1433272320 : K[X]) * e1 ^ 2 * w1 ^ 3 * a2 + (655360 : K[X]) * e1
      * e2 ^ 3 - (1474560 : K[X]) * u2 ^ 2 * w1 ^ 3 + (238878720 : K[X]) *
      u2 * w1 ^ 3 * a2 + (2160 : K[X]) * s2 * w1 - (9674588160 : K[X]) *
      w1 ^ 3 * a2 ^ 2 - Polynomial.C μ * ((21168 : K[X]) * e1 * w1 ^ 6)) +
      h0 ^ 2 * ((61931520 : K[X]) * e1 ^ 5 * w1 - (10321920 : K[X]) * e1 ^
      4 * e2 + (103219200 : K[X]) * e1 ^ 3 * u2 * w1 - (3344302080 : K[X])
      * e1 ^ 3 * w1 * a2 - (20643840 : K[X]) * e1 ^ 2 * e2 * u2 +
      (477757440 : K[X]) * e1 ^ 2 * e2 * a2 + (19660800 : K[X]) * e1 * u2
      ^ 2 * w1 - (1911029760 : K[X]) * e1 * u2 * w1 * a2 + (38698352640 :
      K[X]) * e1 * w1 * a2 ^ 2 - (1638400 : K[X]) * e2 * u2 ^ 2 +
      (159252480 : K[X]) * e2 * u2 * a2 - (3224862720 : K[X]) * e2 * a2 ^
      2 + Polynomial.C ν * ((540 : K[X]) * w1 ^ 6) - Polynomial.C μ *
      ((211680 : K[X]) * e1 ^ 2 * w1 ^ 4) - Polynomial.C μ * ((28224 :
      K[X]) * u2 * w1 ^ 4) + Polynomial.C μ * ((3265920 : K[X]) * w1 ^ 4 *
      a2) + Polynomial.C κ * ((17694720 : K[X]) * e1 ^ 3 * w1 ^ 3) +
      Polynomial.C κ * ((3538944 : K[X]) * e1 * u2 * w1 ^ 3) -
      Polynomial.C κ * ((286654464 : K[X]) * e1 * w1 ^ 3 * a2) -
      Polynomial.C κ * ((131072 : K[X]) * e2 ^ 3)) + h0 ^ 3 *
      (-((2149908480 : K[X]) * e1 ^ 2 * w1 ^ 2 * a1) - (119439360 : K[X])
      * e2 ^ 2 * a1 - (716636160 : K[X]) * u2 * w1 ^ 2 * a1 + (58047528960
      : K[X]) * w1 ^ 2 * a1 * a2 + Polynomial.C ν * ((10800 : K[X]) * e1 *
      w1 ^ 4) + Polynomial.C μ * ((887040 : K[X]) * e1 ^ 3 * w1 ^ 2) +
      Polynomial.C μ * ((215040 : K[X]) * e1 * e2 ^ 2) + Polynomial.C μ *
      ((1128960 : K[X]) * e1 * u2 * w1 ^ 2) - Polynomial.C μ * ((78382080
      : K[X]) * e1 * w1 ^ 2 * a2) - Polynomial.C κ * ((35389440 : K[X]) *
      e1 ^ 4 * w1) + Polynomial.C κ * ((5898240 : K[X]) * e1 ^ 3 * e2) -
      Polynomial.C κ * ((35389440 : K[X]) * e1 ^ 2 * u2 * w1) +
      Polynomial.C κ * ((1433272320 : K[X]) * e1 ^ 2 * w1 * a2) +
      Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 * u2) - Polynomial.C κ
      * ((191102976 : K[X]) * e1 * e2 * a2) - Polynomial.C κ * ((2359296 :
      K[X]) * u2 ^ 2 * w1) + Polynomial.C κ * ((286654464 : K[X]) * u2 *
      w1 * a2) - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) +
      h0 ^ 4 * ((1433272320 : K[X]) * e1 ^ 3 * a1 + (2866544640 : K[X]) *
      e1 * u2 * a1 - (58047528960 : K[X]) * e1 * a1 * a2 - Polynomial.C ν₂
      * ((54 : K[X]) * w1 ^ 4) + Polynomial.C ν * ((60480 : K[X]) * e1 ^ 2
      * w1 ^ 2) + Polynomial.C ν * ((7680 : K[X]) * e2 ^ 2) + Polynomial.C
      ν * ((28800 : K[X]) * u2 * w1 ^ 2) - Polynomial.C ν * ((2799360 :
      K[X]) * w1 ^ 2 * a2) - Polynomial.C μ * ((887040 : K[X]) * e1 ^ 4) -
      Polynomial.C μ * ((3548160 : K[X]) * e1 ^ 2 * u2) + Polynomial.C μ *
      ((52254720 : K[X]) * e1 ^ 2 * a2) - Polynomial.C μ * ((376320 :
      K[X]) * u2 ^ 2) + Polynomial.C μ * ((34836480 : K[X]) * u2 * a2) -
      Polynomial.C μ * ((15676416 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ
      * ((564350976 : K[X]) * a2 ^ 2) + Polynomial.C κ * ((859963392 :
      K[X]) * e1 * w1 ^ 2 * a1)) + h0 ^ 5 * ((12899450880 : K[X]) * e1 ^ 2
      * w1 * a0 - (2149908480 : K[X]) * e1 * e2 * a0 + (2149908480 : K[X])
      * u2 * w1 * a0 - (174142586880 : K[X]) * w1 * a0 * a2 - (87071293440
      : K[X]) * w1 * a1 ^ 2 - Polynomial.C ν₂ * ((1296 : K[X]) * e1 * w1 ^
      2) - Polynomial.C κ₅ * ((73728 : K[X]) * e1 ^ 2 * w1) + Polynomial.C
      κ₅ * ((12288 : K[X]) * e1 * e2) - Polynomial.C κ₅ * ((12288 : K[X])
      * u2 * w1) + Polynomial.C κ₅ * ((995328 : K[X]) * w1 * a2) -
      Polynomial.C ν * ((80640 : K[X]) * e1 ^ 3) - Polynomial.C ν *
      ((161280 : K[X]) * e1 * u2) + Polynomial.C ν * ((3732480 : K[X]) *
      e1 * a2) + Polynomial.C μ * ((313528320 : K[X]) * e1 * w1 * a1) -
      Polynomial.C μ * ((41803776 : K[X]) * e2 * a1) - Polynomial.C κ *
      ((859963392 : K[X]) * e1 ^ 2 * a1) - Polynomial.C κ * ((573308928 :
      K[X]) * u2 * a1) + Polynomial.C κ * ((23219011584 : K[X]) * a1 *
      a2)) + h0 ^ 6 * (Polynomial.C μ₃ * ((4 : K[X]) * w1 ^ 2) +
      Polynomial.C κ₇ * ((2304 : K[X]) * e1 * w1) - Polynomial.C κ₇ *
      ((384 : K[X]) * e2) + Polynomial.C ν₂ * ((2592 : K[X]) * e1 ^ 2) +
      Polynomial.C ν₂ * ((1728 : K[X]) * u2) - Polynomial.C ν₂ * ((93312 :
      K[X]) * a2) + Polynomial.C ν * ((11197440 : K[X]) * w1 * a1) +
      Polynomial.C μ * ((94058496 : K[X]) * w1 ^ 2 * a0) - Polynomial.C κ
      * ((5159780352 : K[X]) * e1 * w1 * a0) + Polynomial.C κ *
      ((859963392 : K[X]) * e2 * a0)) + h0 ^ 7 * ((522427760640 : K[X]) *
      a0 * a1 - Polynomial.C μ₃ * ((16 : K[X]) * e1) - Polynomial.C κ₅ *
      ((2985984 : K[X]) * a1) - Polynomial.C μ * ((376233984 : K[X]) * e1
      * a0)) + h0 ^ 8 * (-(Polynomial.C ν * ((67184640 : K[X]) * a0))) =
      Polynomial.C μ₄ * h0 ^ 8 := by
    linear_combination hRq + (-((2160 : K[X]) * w1)) * hs2
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have hev := congrArg (fun t : K[X] => t.eval (-(d / c))) hR2q
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hev
  rw [hroot] at hev
  have hzero :
      (Polynomial.C μ * w1 ^ 8).eval (-(d / c)) = 0 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C]
    linear_combination ((1215 : K)⁻¹) * hev
  obtain ⟨s4, hs4⟩ := linearPolynomial_dvd_of_eval_eq_zero_810 h0
    (Polynomial.C μ * w1 ^ 8) (-(d / c)) hdeg1 hroot hzero
  have hR3q :
      (-((61931520 : K[X]) * e1 ^ 4 * w1 ^ 3) - (22118400 : K[X]) * e1 ^ 2
      * u2 * w1 ^ 3 + (1433272320 : K[X]) * e1 ^ 2 * w1 ^ 3 * a2 + (655360
      : K[X]) * e1 * e2 ^ 3 - (1474560 : K[X]) * u2 ^ 2 * w1 ^ 3 +
      (238878720 : K[X]) * u2 * w1 ^ 3 * a2 + (2160 : K[X]) * s2 * w1 +
      (1215 : K[X]) * s4 - (9674588160 : K[X]) * w1 ^ 3 * a2 ^ 2 -
      Polynomial.C μ * ((21168 : K[X]) * e1 * w1 ^ 6)) + h0 * ((61931520 :
      K[X]) * e1 ^ 5 * w1 - (10321920 : K[X]) * e1 ^ 4 * e2 + (103219200 :
      K[X]) * e1 ^ 3 * u2 * w1 - (3344302080 : K[X]) * e1 ^ 3 * w1 * a2 -
      (20643840 : K[X]) * e1 ^ 2 * e2 * u2 + (477757440 : K[X]) * e1 ^ 2 *
      e2 * a2 + (19660800 : K[X]) * e1 * u2 ^ 2 * w1 - (1911029760 : K[X])
      * e1 * u2 * w1 * a2 + (38698352640 : K[X]) * e1 * w1 * a2 ^ 2 -
      (1638400 : K[X]) * e2 * u2 ^ 2 + (159252480 : K[X]) * e2 * u2 * a2 -
      (3224862720 : K[X]) * e2 * a2 ^ 2 + Polynomial.C ν * ((540 : K[X]) *
      w1 ^ 6) - Polynomial.C μ * ((211680 : K[X]) * e1 ^ 2 * w1 ^ 4) -
      Polynomial.C μ * ((28224 : K[X]) * u2 * w1 ^ 4) + Polynomial.C μ *
      ((3265920 : K[X]) * w1 ^ 4 * a2) + Polynomial.C κ * ((17694720 :
      K[X]) * e1 ^ 3 * w1 ^ 3) + Polynomial.C κ * ((3538944 : K[X]) * e1 *
      u2 * w1 ^ 3) - Polynomial.C κ * ((286654464 : K[X]) * e1 * w1 ^ 3 *
      a2) - Polynomial.C κ * ((131072 : K[X]) * e2 ^ 3)) + h0 ^ 2 *
      (-((2149908480 : K[X]) * e1 ^ 2 * w1 ^ 2 * a1) - (119439360 : K[X])
      * e2 ^ 2 * a1 - (716636160 : K[X]) * u2 * w1 ^ 2 * a1 + (58047528960
      : K[X]) * w1 ^ 2 * a1 * a2 + Polynomial.C ν * ((10800 : K[X]) * e1 *
      w1 ^ 4) + Polynomial.C μ * ((887040 : K[X]) * e1 ^ 3 * w1 ^ 2) +
      Polynomial.C μ * ((215040 : K[X]) * e1 * e2 ^ 2) + Polynomial.C μ *
      ((1128960 : K[X]) * e1 * u2 * w1 ^ 2) - Polynomial.C μ * ((78382080
      : K[X]) * e1 * w1 ^ 2 * a2) - Polynomial.C κ * ((35389440 : K[X]) *
      e1 ^ 4 * w1) + Polynomial.C κ * ((5898240 : K[X]) * e1 ^ 3 * e2) -
      Polynomial.C κ * ((35389440 : K[X]) * e1 ^ 2 * u2 * w1) +
      Polynomial.C κ * ((1433272320 : K[X]) * e1 ^ 2 * w1 * a2) +
      Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 * u2) - Polynomial.C κ
      * ((191102976 : K[X]) * e1 * e2 * a2) - Polynomial.C κ * ((2359296 :
      K[X]) * u2 ^ 2 * w1) + Polynomial.C κ * ((286654464 : K[X]) * u2 *
      w1 * a2) - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) +
      h0 ^ 3 * ((1433272320 : K[X]) * e1 ^ 3 * a1 + (2866544640 : K[X]) *
      e1 * u2 * a1 - (58047528960 : K[X]) * e1 * a1 * a2 - Polynomial.C ν₂
      * ((54 : K[X]) * w1 ^ 4) + Polynomial.C ν * ((60480 : K[X]) * e1 ^ 2
      * w1 ^ 2) + Polynomial.C ν * ((7680 : K[X]) * e2 ^ 2) + Polynomial.C
      ν * ((28800 : K[X]) * u2 * w1 ^ 2) - Polynomial.C ν * ((2799360 :
      K[X]) * w1 ^ 2 * a2) - Polynomial.C μ * ((887040 : K[X]) * e1 ^ 4) -
      Polynomial.C μ * ((3548160 : K[X]) * e1 ^ 2 * u2) + Polynomial.C μ *
      ((52254720 : K[X]) * e1 ^ 2 * a2) - Polynomial.C μ * ((376320 :
      K[X]) * u2 ^ 2) + Polynomial.C μ * ((34836480 : K[X]) * u2 * a2) -
      Polynomial.C μ * ((15676416 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ
      * ((564350976 : K[X]) * a2 ^ 2) + Polynomial.C κ * ((859963392 :
      K[X]) * e1 * w1 ^ 2 * a1)) + h0 ^ 4 * ((12899450880 : K[X]) * e1 ^ 2
      * w1 * a0 - (2149908480 : K[X]) * e1 * e2 * a0 + (2149908480 : K[X])
      * u2 * w1 * a0 - (174142586880 : K[X]) * w1 * a0 * a2 - (87071293440
      : K[X]) * w1 * a1 ^ 2 - Polynomial.C ν₂ * ((1296 : K[X]) * e1 * w1 ^
      2) - Polynomial.C κ₅ * ((73728 : K[X]) * e1 ^ 2 * w1) + Polynomial.C
      κ₅ * ((12288 : K[X]) * e1 * e2) - Polynomial.C κ₅ * ((12288 : K[X])
      * u2 * w1) + Polynomial.C κ₅ * ((995328 : K[X]) * w1 * a2) -
      Polynomial.C ν * ((80640 : K[X]) * e1 ^ 3) - Polynomial.C ν *
      ((161280 : K[X]) * e1 * u2) + Polynomial.C ν * ((3732480 : K[X]) *
      e1 * a2) + Polynomial.C μ * ((313528320 : K[X]) * e1 * w1 * a1) -
      Polynomial.C μ * ((41803776 : K[X]) * e2 * a1) - Polynomial.C κ *
      ((859963392 : K[X]) * e1 ^ 2 * a1) - Polynomial.C κ * ((573308928 :
      K[X]) * u2 * a1) + Polynomial.C κ * ((23219011584 : K[X]) * a1 *
      a2)) + h0 ^ 5 * (Polynomial.C μ₃ * ((4 : K[X]) * w1 ^ 2) +
      Polynomial.C κ₇ * ((2304 : K[X]) * e1 * w1) - Polynomial.C κ₇ *
      ((384 : K[X]) * e2) + Polynomial.C ν₂ * ((2592 : K[X]) * e1 ^ 2) +
      Polynomial.C ν₂ * ((1728 : K[X]) * u2) - Polynomial.C ν₂ * ((93312 :
      K[X]) * a2) + Polynomial.C ν * ((11197440 : K[X]) * w1 * a1) +
      Polynomial.C μ * ((94058496 : K[X]) * w1 ^ 2 * a0) - Polynomial.C κ
      * ((5159780352 : K[X]) * e1 * w1 * a0) + Polynomial.C κ *
      ((859963392 : K[X]) * e2 * a0)) + h0 ^ 6 * ((522427760640 : K[X]) *
      a0 * a1 - Polynomial.C μ₃ * ((16 : K[X]) * e1) - Polynomial.C κ₅ *
      ((2985984 : K[X]) * a1) - Polynomial.C μ * ((376233984 : K[X]) * e1
      * a0)) + h0 ^ 7 * (-(Polynomial.C ν * ((67184640 : K[X]) * a0))) =
      Polynomial.C μ₄ * h0 ^ 7 := by
    apply mul_left_cancel₀ hh0
    linear_combination hR2q + (-((1215 : K[X]))) * hs4
  have h1ev := congrArg (fun t : K[X] => t.eval (-(d / c))) hu2
  simp only [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_ofNat] at h1ev
  rw [hroot, zero_mul] at h1ev
  have h1 : w1.eval (-(d / c)) *
      (e2.eval (-(d / c)) - 3 * e1.eval (-(d / c)) * w1.eval (-(d / c)))
      = 0 := by
    linear_combination h1ev
  have hv0 : e2.eval (-(d / c)) = 0 := by
    have hev3 := congrArg (fun t : K[X] => t.eval (-(d / c))) he3
    simp only [Polynomial.eval_mul] at hev3
    rw [hroot, zero_mul] at hev3
    exact hev3
  have hevR10 := congrArg (fun t : K[X] => t.eval (-(d / c))) hR10
  simp only [alignedTenthSquarePeeledRow610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hevR10
  rw [hroot] at hevR10
  have hhead10 :
      184320 * e1.eval (-(d / c)) ^ 2 * e2.eval (-(d / c)) ^ 2 - 44789760
      * e1.eval (-(d / c)) ^ 2 * a2.eval (-(d / c)) * w1.eval (-(d / c)) ^
      2 + 737280 * e1.eval (-(d / c)) ^ 2 * u2.eval (-(d / c)) * w1.eval
      (-(d / c)) ^ 2 + 2268 * e1.eval (-(d / c)) * μ * w1.eval (-(d / c))
      ^ 5 - 2488320 * e2.eval (-(d / c)) ^ 2 * a2.eval (-(d / c)) + 40960
      * e2.eval (-(d / c)) ^ 2 * u2.eval (-(d / c)) + 604661760 * a2.eval
      (-(d / c)) ^ 2 * w1.eval (-(d / c)) ^ 2 - 14929920 * a2.eval (-(d /
      c)) * u2.eval (-(d / c)) * w1.eval (-(d / c)) ^ 2 - 135 * s2.eval
      (-(d / c)) + 92160 * u2.eval (-(d / c)) ^ 2 * w1.eval (-(d / c)) ^ 2
      = 0 := by
    linear_combination hevR10
  have htie := alignedTenthSquareTieResolve_610 h1 hv0 hhead10
  have hevR3 := congrArg (fun t : K[X] => t.eval (-(d / c))) hR3q
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hevR3
  rw [hroot] at hevR3
  have hhead11 :
      -61931520 * e1.eval (-(d / c)) ^ 4 * w1.eval (-(d / c)) ^ 3 +
      1433272320 * e1.eval (-(d / c)) ^ 2 * a2.eval (-(d / c)) * w1.eval
      (-(d / c)) ^ 3 - 22118400 * e1.eval (-(d / c)) ^ 2 * u2.eval (-(d /
      c)) * w1.eval (-(d / c)) ^ 3 + 655360 * e1.eval (-(d / c)) * e2.eval
      (-(d / c)) ^ 3 - 21168 * e1.eval (-(d / c)) * μ * w1.eval (-(d / c))
      ^ 6 - 9674588160 * a2.eval (-(d / c)) ^ 2 * w1.eval (-(d / c)) ^ 3 +
      238878720 * a2.eval (-(d / c)) * u2.eval (-(d / c)) * w1.eval (-(d /
      c)) ^ 3 + 2160 * s2.eval (-(d / c)) * w1.eval (-(d / c)) + 1215 *
      s4.eval (-(d / c)) - 1474560 * u2.eval (-(d / c)) ^ 2 * w1.eval (-(d
      / c)) ^ 3 = 0 := by
    linear_combination hevR3
  have hs4a : s4.eval (-(d / c)) = 0 :=
    alignedEleventhSquareTieResolve_610 h1 hv0 htie hhead11
  obtain ⟨s5, hs5⟩ := linearPolynomial_dvd_of_eval_eq_zero_810 h0
    s4 (-(d / c)) hdeg1 hroot hs4a
  have hmu8 : Polynomial.C μ * w1 ^ 8 = h0 ^ 2 * s5 := by
    rw [hs4, hs5]
    ring
  refine ⟨s4, s5, hs4, ?_, hs5, hmu8⟩
  unfold alignedEleventhSquarePeeledRow610
  linear_combination hR3q

end Max11DegreeRoutes
