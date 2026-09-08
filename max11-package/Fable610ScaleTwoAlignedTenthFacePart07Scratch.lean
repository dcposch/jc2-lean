import Fable610ScaleTwoAlignedTenthFacePart02Scratch
import Fable610ScaleTwoAlignedTenthFacePart06Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 6400000000 in
/-- Descent of the consumed degree-`5` row in the square chamber: the
`h₀⁴⁰`-peeled core absorbs the decic head through the seventh-face
divisibilities and the eighth-face product divisor `u₂`, cancelling
`h₀³` onto the μ-loaded head `-135 (2048 e₁³ w₁⁴ - μ w₁⁷)` with `q₀`
tied at `h₀⁷`; at the root of `h₀` the head transfers to the NEW
divisibility `2048 e₁³ w₁⁴ - μ w₁⁷ = h₀ s₂`, and substituting `s₂`
peels one more `h₀` into the peeled row `= κ₉ h₀⁶`. -/
theorem alignedSquareTenth_descent_610 {K : Type*} [Field K]
    [CharZero K]
    {H h0 w1 f2 e1 e2 u2 a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7 :
      K[X]}
    {κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ κ₉ : K}
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1) (hHsq : H = h0 ^ 2)
    (hp5 : a5 = h0 ^ 4 * w1) (hp4 : a4 = h0 ^ 2 * f2)
    (hD : alignedThirdDefect610 H a3 a4 a5 b7 κ =
      Polynomial.C μ * h0 ^ 15)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10)
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
    (hO : alignedTenthDefect610 H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5
        b6 b7 κ = Polynomial.C κ₉ * H ^ 25)
    (he1 : (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1)
    (he2 : (27 : K[X]) * a3 - w1 ^ 3 = h0 * e2)
    (hu2 : w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2) :
    ∃ s2 : K[X],
      (2048 : K[X]) * e1 ^ 3 * w1 ^ 4 - Polynomial.C μ * w1 ^ 7 =
        h0 * s2 ∧
      alignedTenthSquarePeeledRow610 h0 w1 e1 e2 u2 s2 a0 a1 a2 b0
          κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ = Polynomial.C κ₉ * h0 ^ 6 := by
  have hO' := hO
  unfold alignedTenthDefect610 at hO'
  rw [hD, hE, hF, hG, hI, hJ, hL, hHsq, hp5, hp4] at hO'
  have hcore :
      (-((94058496 : K[X]) * f2 ^ 5) + (783820800 : K[X]) * f2 ^ 4 * w1
        ^ 2 - (1881169920 : K[X]) * f2 ^ 3 * a3 * w1 - (1132185600 : K[X])
        * f2 ^ 3 * w1 ^ 4 + (1209323520 : K[X]) * f2 ^ 2 * a3 ^ 2 +
        (3135283200 : K[X]) * f2 ^ 2 * a3 * w1 ^ 3 + (603832320 : K[X]) *
        f2 ^ 2 * w1 ^ 6 - (2821754880 : K[X]) * f2 * a3 ^ 2 * w1 ^ 2 -
        (1358622720 : K[X]) * f2 * a3 * w1 ^ 5 - (136581120 : K[X]) * f2 *
        w1 ^ 8 + (806215680 : K[X]) * a3 ^ 3 * w1 + (783820800 : K[X]) *
        a3 ^ 2 * w1 ^ 4 + (172523520 : K[X]) * a3 * w1 ^ 7 + (11128832 :
        K[X]) * w1 ^ 10) + h0 ^ 2 * ((806215680 : K[X]) * f2 ^ 3 * a2 -
        (2821754880 : K[X]) * f2 ^ 2 * w1 ^ 2 * a2 + (4837294080 : K[X]) *
        f2 * a3 * w1 * a2 + (1567641600 : K[X]) * f2 * w1 ^ 4 * a2 -
        (1813985280 : K[X]) * a3 ^ 2 * a2 - (1881169920 : K[X]) * a3 * w1
        ^ 3 * a2 - (226437120 : K[X]) * w1 ^ 6 * a2 + Polynomial.C κ *
        ((22394880 : K[X]) * f2 ^ 4) - Polynomial.C κ * ((119439360 :
        K[X]) * f2 ^ 3 * w1 ^ 2) + Polynomial.C κ * ((268738560 : K[X]) *
        f2 ^ 2 * a3 * w1) + Polynomial.C κ * ((109486080 : K[X]) * f2 ^ 2
        * w1 ^ 4) - Polynomial.C κ * ((161243136 : K[X]) * f2 * a3 ^ 2) -
        Polynomial.C κ * ((238878720 : K[X]) * f2 * a3 * w1 ^ 3) -
        Polynomial.C κ * ((34062336 : K[X]) * f2 * w1 ^ 6) + Polynomial.C
        κ * ((134369280 : K[X]) * a3 ^ 2 * w1 ^ 2) + Polynomial.C κ *
        ((43794432 : K[X]) * a3 * w1 ^ 5) + Polynomial.C κ * ((3446784 :
        K[X]) * w1 ^ 8)) + h0 ^ 3 * (-(Polynomial.C μ * ((5987520 : K[X])
        * f2 ^ 3 * w1)) + Polynomial.C μ * ((9797760 : K[X]) * f2 ^ 2 *
        a3) + Polynomial.C μ * ((8482320 : K[X]) * f2 ^ 2 * w1 ^ 3) -
        Polynomial.C μ * ((17962560 : K[X]) * f2 * a3 * w1 ^ 2) -
        Polynomial.C μ * ((3251556 : K[X]) * f2 * w1 ^ 5) + Polynomial.C μ
        * ((9797760 : K[X]) * a3 ^ 2 * w1) + Polynomial.C μ * ((4241160 :
        K[X]) * a3 * w1 ^ 4) + Polynomial.C μ * ((374187 : K[X]) * w1 ^
        7)) + h0 ^ 4 * ((2418647040 : K[X]) * f2 ^ 2 * w1 * a1 -
        (3627970560 : K[X]) * f2 * a3 * a1 - (1881169920 : K[X]) * f2 * w1
        ^ 3 * a1 - (1813985280 : K[X]) * f2 * a2 ^ 2 + (2418647040 : K[X])
        * a3 * w1 ^ 2 * a1 + (313528320 : K[X]) * w1 ^ 5 * a1 +
        (1209323520 : K[X]) * w1 ^ 2 * a2 ^ 2 - Polynomial.C κ *
        ((161243136 : K[X]) * f2 ^ 2 * a2) + Polynomial.C κ * ((268738560
        : K[X]) * f2 * w1 ^ 2 * a2) - Polynomial.C κ * ((322486272 : K[X])
        * a3 * w1 * a2) - Polynomial.C κ * ((59719680 : K[X]) * w1 ^ 4 *
        a2)) + h0 ^ 5 * (-(Polynomial.C ν * ((136080 : K[X]) * f2 ^ 2 *
        w1)) + Polynomial.C ν * ((233280 : K[X]) * f2 * a3) + Polynomial.C
        ν * ((98280 : K[X]) * f2 * w1 ^ 3) - Polynomial.C ν * ((136080 :
        K[X]) * a3 * w1 ^ 2) - Polynomial.C ν * ((15561 : K[X]) * w1 ^ 5)
        + Polynomial.C μ * ((19595520 : K[X]) * f2 * w1 * a2) -
        Polynomial.C μ * ((23514624 : K[X]) * a3 * a2) - Polynomial.C μ *
        ((5987520 : K[X]) * w1 ^ 3 * a2)) + h0 ^ 6 * (-((1813985280 :
        K[X]) * f2 ^ 2 * a0) + (2418647040 : K[X]) * f2 * w1 ^ 2 * a0 -
        (3627970560 : K[X]) * a3 * w1 * a0 - (470292480 : K[X]) * w1 ^ 4 *
        a0 - (3627970560 : K[X]) * w1 * a1 * a2 + Polynomial.C κ₅ *
        ((10368 : K[X]) * f2 ^ 2) - Polynomial.C κ₅ * ((13824 : K[X]) * f2
        * w1 ^ 2) + Polynomial.C κ₅ * ((20736 : K[X]) * a3 * w1) +
        Polynomial.C κ₅ * ((2688 : K[X]) * w1 ^ 4) - Polynomial.C κ *
        ((322486272 : K[X]) * f2 * w1 * a1) + Polynomial.C κ * ((483729408
        : K[X]) * a3 * a1) + Polynomial.C κ * ((89579520 : K[X]) * w1 ^ 3
        * a1) + Polynomial.C κ * ((241864704 : K[X]) * a2 ^ 2)) + h0 ^ 7 *
        (Polynomial.C ν₂ * ((972 : K[X]) * f2 * w1) - Polynomial.C ν₂ *
        ((1944 : K[X]) * a3) - Polynomial.C ν₂ * ((243 : K[X]) * w1 ^ 3) +
        Polynomial.C ν * ((233280 : K[X]) * w1 * a2) - Polynomial.C μ *
        ((23514624 : K[X]) * f2 * a1) + Polynomial.C μ * ((9797760 : K[X])
        * w1 ^ 2 * a1)) + h0 ^ 8 * ((10883911680 : K[X]) * a0 * a2 +
        (5441955840 : K[X]) * a1 ^ 2 - Polynomial.C κ₇ * ((216 : K[X]) *
        f2) + Polynomial.C κ₇ * ((72 : K[X]) * w1 ^ 2) - Polynomial.C κ₅ *
        ((62208 : K[X]) * a2) + Polynomial.C κ * ((483729408 : K[X]) * f2
        * a0) - Polynomial.C κ * ((161243136 : K[X]) * w1 ^ 2 * a0)) + h0
        ^ 9 * (-(Polynomial.C μ₃ * (w1)) - Polynomial.C ν * ((1399680 :
        K[X]) * a1) - Polynomial.C μ * ((23514624 : K[X]) * w1 * a0)) + h0
        ^ 10 * (-((9795520512 : K[X]) * b0) - Polynomial.C κ₃ * ((20155392
        : K[X]) * a0)) = Polynomial.C κ₉ * h0 ^ 10 := by
    apply mul_left_cancel₀ (pow_ne_zero 40 hh0)
    linear_combination hO'
  have hR10 :
      (-((276480 : K[X]) * e1 ^ 3 * w1 ^ 4) + Polynomial.C μ * ((135 :
        K[X]) * w1 ^ 7)) + h0 * ((184320 : K[X]) * e1 ^ 2 * e2 ^ 2 +
        (737280 : K[X]) * e1 ^ 2 * u2 * w1 ^ 2 - (44789760 : K[X]) * e1 ^
        2 * w1 ^ 2 * a2 + (40960 : K[X]) * e2 ^ 2 * u2 - (2488320 : K[X])
        * e2 ^ 2 * a2 + (92160 : K[X]) * u2 ^ 2 * w1 ^ 2 - (14929920 :
        K[X]) * u2 * w1 ^ 2 * a2 + (604661760 : K[X]) * w1 ^ 2 * a2 ^ 2 +
        Polynomial.C μ * ((2268 : K[X]) * e1 * w1 ^ 5)) + h0 ^ 2 *
        (-((387072 : K[X]) * e1 ^ 5) - (2580480 : K[X]) * e1 ^ 3 * u2 +
        (29859840 : K[X]) * e1 ^ 3 * a2 - (798720 : K[X]) * e1 * u2 ^ 2 +
        (59719680 : K[X]) * e1 * u2 * a2 - (604661760 : K[X]) * e1 * a2 ^
        2 - Polynomial.C ν * ((81 : K[X]) * w1 ^ 5) + Polynomial.C μ *
        ((15120 : K[X]) * e1 ^ 2 * w1 ^ 3) + Polynomial.C μ * ((2520 :
        K[X]) * u2 * w1 ^ 3) - Polynomial.C μ * ((326592 : K[X]) * w1 ^ 3
        * a2) - Polynomial.C κ * ((73728 : K[X]) * e1 * e2 ^ 2) -
        Polynomial.C κ * ((221184 : K[X]) * e1 * u2 * w1 ^ 2) +
        Polynomial.C κ * ((17915904 : K[X]) * e1 * w1 ^ 2 * a2)) + h0 ^ 3
        * ((268738560 : K[X]) * e1 ^ 2 * w1 * a1 - (44789760 : K[X]) * e1
        * e2 * a1 + (44789760 : K[X]) * u2 * w1 * a1 - (3627970560 : K[X])
        * w1 * a1 * a2 - Polynomial.C ν * ((1080 : K[X]) * e1 * w1 ^ 3) -
        Polynomial.C μ * ((221760 : K[X]) * e1 ^ 3 * w1) + Polynomial.C μ
        * ((40320 : K[X]) * e1 ^ 2 * e2) - Polynomial.C μ * ((100800 :
        K[X]) * e1 * u2 * w1) + Polynomial.C μ * ((6531840 : K[X]) * e1 *
        w1 * a2) + Polynomial.C μ * ((13440 : K[X]) * e2 * u2) -
        Polynomial.C μ * ((870912 : K[X]) * e2 * a2) + Polynomial.C κ *
        ((276480 : K[X]) * e1 ^ 4) + Polynomial.C κ * ((1105920 : K[X]) *
        e1 ^ 2 * u2) - Polynomial.C κ * ((17915904 : K[X]) * e1 ^ 2 * a2)
        + Polynomial.C κ * ((110592 : K[X]) * u2 ^ 2) - Polynomial.C κ *
        ((11943936 : K[X]) * u2 * a2) + Polynomial.C κ * ((241864704 :
        K[X]) * a2 ^ 2)) + h0 ^ 4 * (Polynomial.C ν₂ * ((9 : K[X]) * w1 ^
        3) - Polynomial.C ν * ((15120 : K[X]) * e1 ^ 2 * w1) +
        Polynomial.C ν * ((2880 : K[X]) * e1 * e2) - Polynomial.C ν *
        ((2160 : K[X]) * u2 * w1) + Polynomial.C ν * ((233280 : K[X]) * w1
        * a2) + Polynomial.C μ * ((1959552 : K[X]) * w1 ^ 2 * a1) -
        Polynomial.C κ * ((107495424 : K[X]) * e1 * w1 * a1) +
        Polynomial.C κ * ((17915904 : K[X]) * e2 * a1)) + h0 ^ 5 *
        (-((201553920 : K[X]) * e1 ^ 2 * a0) - (134369280 : K[X]) * u2 *
        a0 + (10883911680 : K[X]) * a0 * a2 + (5441955840 : K[X]) * a1 ^ 2
        + Polynomial.C ν₂ * ((324 : K[X]) * e1 * w1) - Polynomial.C ν₂ *
        ((72 : K[X]) * e2) + Polynomial.C κ₅ * ((1152 : K[X]) * e1 ^ 2) +
        Polynomial.C κ₅ * ((768 : K[X]) * u2) - Polynomial.C κ₅ * ((62208
        : K[X]) * a2) - Polynomial.C μ * ((7838208 : K[X]) * e1 * a1)) +
        h0 ^ 6 * (-(Polynomial.C μ₃ * (w1)) - Polynomial.C κ₇ * ((72 :
        K[X]) * e1) - Polynomial.C ν * ((1399680 : K[X]) * a1) -
        Polynomial.C μ * ((23514624 : K[X]) * w1 * a0) + Polynomial.C κ *
        ((161243136 : K[X]) * e1 * a0)) + h0 ^ 7 * (-((9795520512 : K[X])
        * b0) - Polynomial.C κ₃ * ((20155392 : K[X]) * a0)) = Polynomial.C
        κ₉ * h0 ^ 7 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    linear_combination hcore + (-(-((387072 : K[X]) * e1 ^ 4 * h0 ^ 4) + (8128512 : K[X]) * e1 ^ 3
      * w1 ^ 2 * h0 ^ 3 - (1161216 : K[X]) * e1 ^ 3 * f2 * h0 ^ 3 -
      (15224832 : K[X]) * e1 ^ 2 * w1 ^ 4 * h0 ^ 2 + (25546752 : K[X]) *
      e1 ^ 2 * w1 ^ 2 * f2 * h0 ^ 2 - (69672960 : K[X]) * e1 ^ 2 * w1 * a3
      * h0 ^ 2 - (3483648 : K[X]) * e1 ^ 2 * f2 ^ 2 * h0 ^ 2 + (29859840 :
      K[X]) * e1 ^ 2 * a2 * h0 ^ 4 + (10708992 : K[X]) * e1 * w1 ^ 6 * h0
      - (71221248 : K[X]) * e1 * w1 ^ 4 * f2 * h0 + (209018880 : K[X]) *
      e1 * w1 ^ 3 * a3 * h0 + (80123904 : K[X]) * e1 * w1 ^ 2 * f2 ^ 2 *
      h0 - (253808640 : K[X]) * e1 * w1 ^ 2 * a2 * h0 ^ 3 - (209018880 :
      K[X]) * e1 * w1 * f2 * a3 * h0 + (268738560 : K[X]) * e1 * w1 * a1 *
      h0 ^ 5 - (10450944 : K[X]) * e1 * f2 ^ 3 * h0 + (89579520 : K[X]) *
      e1 * f2 * a2 * h0 ^ 3 + (134369280 : K[X]) * e1 * a3 ^ 2 * h0 -
      (201553920 : K[X]) * e1 * a0 * h0 ^ 7 - (11077632 : K[X]) * w1 ^ 8 +
      (103348224 : K[X]) * w1 ^ 6 * f2 - (174182400 : K[X]) * w1 ^ 5 * a3
      - (293787648 : K[X]) * w1 ^ 4 * f2 ^ 2 + (238878720 : K[X]) * w1 ^ 4
      * a2 * h0 ^ 2 + (836075520 : K[X]) * w1 ^ 3 * f2 * a3 - (358318080 :
      K[X]) * w1 ^ 3 * a1 * h0 ^ 4 + (250822656 : K[X]) * w1 ^ 2 * f2 ^ 3
      - (851005440 : K[X]) * w1 ^ 2 * f2 * a2 * h0 ^ 2 - (806215680 :
      K[X]) * w1 ^ 2 * a3 ^ 2 + (604661760 : K[X]) * w1 ^ 2 * a0 * h0 ^ 6
      - (627056640 : K[X]) * w1 * f2 ^ 2 * a3 + (806215680 : K[X]) * w1 *
      f2 * a1 * h0 ^ 4 + (1612431360 : K[X]) * w1 * a3 * a2 * h0 ^ 2 -
      (31352832 : K[X]) * f2 ^ 4 + (268738560 : K[X]) * f2 ^ 2 * a2 * h0 ^
      2 + (403107840 : K[X]) * f2 * a3 ^ 2 - (604661760 : K[X]) * f2 * a0
      * h0 ^ 6 - (1209323520 : K[X]) * a3 * a1 * h0 ^ 4 - (604661760 :
      K[X]) * a2 ^ 2 * h0 ^ 4 - Polynomial.C κ₇ * ((72 : K[X]) * h0 ^ 8) +
      Polynomial.C ν₂ * ((324 : K[X]) * w1 * h0 ^ 7) + Polynomial.C κ₅ *
      ((1152 : K[X]) * e1 * h0 ^ 7) - Polynomial.C κ₅ * ((3456 : K[X]) *
      w1 ^ 2 * h0 ^ 6) + Polynomial.C κ₅ * ((3456 : K[X]) * f2 * h0 ^ 6) -
      Polynomial.C ν * ((15120 : K[X]) * e1 * w1 * h0 ^ 6) + Polynomial.C
      ν * ((17640 : K[X]) * w1 ^ 3 * h0 ^ 5) - Polynomial.C ν * ((45360 :
      K[X]) * w1 * f2 * h0 ^ 5) + Polynomial.C ν * ((77760 : K[X]) * a3 *
      h0 ^ 5) - Polynomial.C μ * ((221760 : K[X]) * e1 ^ 2 * w1 * h0 ^ 5)
      + Polynomial.C μ * ((498960 : K[X]) * e1 * w1 ^ 3 * h0 ^ 4) -
      Polynomial.C μ * ((665280 : K[X]) * e1 * w1 * f2 * h0 ^ 4) +
      Polynomial.C μ * ((1088640 : K[X]) * e1 * a3 * h0 ^ 4) -
      Polynomial.C μ * ((363132 : K[X]) * w1 ^ 5 * h0 ^ 3) + Polynomial.C
      μ * ((2162160 : K[X]) * w1 ^ 3 * f2 * h0 ^ 3) - Polynomial.C μ *
      ((4898880 : K[X]) * w1 ^ 2 * a3 * h0 ^ 3) - Polynomial.C μ *
      ((1995840 : K[X]) * w1 * f2 ^ 2 * h0 ^ 3) + Polynomial.C μ *
      ((6531840 : K[X]) * w1 * a2 * h0 ^ 5) + Polynomial.C μ * ((3265920 :
      K[X]) * f2 * a3 * h0 ^ 3) - Polynomial.C μ * ((7838208 : K[X]) * a1
      * h0 ^ 7) + Polynomial.C κ * ((276480 : K[X]) * e1 ^ 3 * h0 ^ 5) -
      Polynomial.C κ * ((3594240 : K[X]) * e1 ^ 2 * w1 ^ 2 * h0 ^ 4) +
      Polynomial.C κ * ((829440 : K[X]) * e1 ^ 2 * f2 * h0 ^ 4) +
      Polynomial.C κ * ((4147200 : K[X]) * e1 * w1 ^ 4 * h0 ^ 3) -
      Polynomial.C κ * ((11612160 : K[X]) * e1 * w1 ^ 2 * f2 * h0 ^ 3) +
      Polynomial.C κ * ((29859840 : K[X]) * e1 * w1 * a3 * h0 ^ 3) +
      Polynomial.C κ * ((2488320 : K[X]) * e1 * f2 ^ 2 * h0 ^ 3) -
      Polynomial.C κ * ((17915904 : K[X]) * e1 * a2 * h0 ^ 5) -
      Polynomial.C κ * ((3336192 : K[X]) * w1 ^ 6 * h0 ^ 2) + Polynomial.C
      κ * ((24053760 : K[X]) * w1 ^ 4 * f2 * h0 ^ 2) - Polynomial.C κ *
      ((49766400 : K[X]) * w1 ^ 3 * a3 * h0 ^ 2) - Polynomial.C κ *
      ((37324800 : K[X]) * w1 ^ 2 * f2 ^ 2 * h0 ^ 2) + Polynomial.C κ *
      ((71663616 : K[X]) * w1 ^ 2 * a2 * h0 ^ 4) + Polynomial.C κ *
      ((89579520 : K[X]) * w1 * f2 * a3 * h0 ^ 2) - Polynomial.C κ *
      ((107495424 : K[X]) * w1 * a1 * h0 ^ 6) + Polynomial.C κ * ((7464960
      : K[X]) * f2 ^ 3 * h0 ^ 2) - Polynomial.C κ * ((53747712 : K[X]) *
      f2 * a2 * h0 ^ 4) - Polynomial.C κ * ((53747712 : K[X]) * a3 ^ 2 *
      h0 ^ 2) + Polynomial.C κ * ((161243136 : K[X]) * a0 * h0 ^ 8))) *
      he1 + (-(-((2580480 : K[X]) * e1 ^ 3 * w1 * h0 ^ 3) + (184320 :
      K[X]) * e1 ^ 2 * e2 * h0 ^ 3 + (5345280 : K[X]) * e1 ^ 2 * w1 ^ 3 *
      h0 ^ 2 + (4976640 : K[X]) * e1 ^ 2 * a3 * h0 ^ 2 - (921600 : K[X]) *
      e1 * e2 * w1 ^ 2 * h0 ^ 2 + (368640 : K[X]) * e1 * w1 ^ 5 * h0 -
      (24883200 : K[X]) * e1 * w1 ^ 2 * a3 * h0 + (59719680 : K[X]) * e1 *
      w1 * a2 * h0 ^ 3 - (44789760 : K[X]) * e1 * a1 * h0 ^ 5 + (40960 :
      K[X]) * e2 ^ 2 * w1 * h0 ^ 2 + (51200 : K[X]) * e2 * w1 ^ 4 * h0 +
      (1105920 : K[X]) * e2 * w1 * a3 * h0 - (2488320 : K[X]) * e2 * a2 *
      h0 ^ 3 - (51200 : K[X]) * w1 ^ 7 + (276480 : K[X]) * w1 ^ 4 * a3 -
      (12441600 : K[X]) * w1 ^ 3 * a2 * h0 ^ 2 + (44789760 : K[X]) * w1 ^
      2 * a1 * h0 ^ 4 + (29859840 : K[X]) * w1 * a3 ^ 2 - (134369280 :
      K[X]) * w1 * a0 * h0 ^ 6 - (67184640 : K[X]) * a3 * a2 * h0 ^ 2 -
      Polynomial.C ν₂ * ((72 : K[X]) * h0 ^ 7) + Polynomial.C κ₅ * ((768 :
      K[X]) * w1 * h0 ^ 6) + Polynomial.C ν * ((2880 : K[X]) * e1 * h0 ^
      6) - Polynomial.C ν * ((2160 : K[X]) * w1 ^ 2 * h0 ^ 5) +
      Polynomial.C μ * ((40320 : K[X]) * e1 ^ 2 * h0 ^ 5) - Polynomial.C μ
      * ((141120 : K[X]) * e1 * w1 ^ 2 * h0 ^ 4) + Polynomial.C μ *
      ((13440 : K[X]) * e2 * w1 * h0 ^ 4) - Polynomial.C μ * ((10920 :
      K[X]) * w1 ^ 4 * h0 ^ 3) + Polynomial.C μ * ((362880 : K[X]) * w1 *
      a3 * h0 ^ 3) - Polynomial.C μ * ((870912 : K[X]) * a2 * h0 ^ 5) +
      Polynomial.C κ * ((1105920 : K[X]) * e1 ^ 2 * w1 * h0 ^ 4) -
      Polynomial.C κ * ((73728 : K[X]) * e1 * e2 * h0 ^ 4) - Polynomial.C
      κ * ((811008 : K[X]) * e1 * w1 ^ 3 * h0 ^ 3) - Polynomial.C κ *
      ((1990656 : K[X]) * e1 * a3 * h0 ^ 3) + Polynomial.C κ * ((110592 :
      K[X]) * e2 * w1 ^ 2 * h0 ^ 3) - Polynomial.C κ * ((110592 : K[X]) *
      w1 ^ 5 * h0 ^ 2) + Polynomial.C κ * ((2985984 : K[X]) * w1 ^ 2 * a3
      * h0 ^ 2) - Polynomial.C κ * ((11943936 : K[X]) * w1 * a2 * h0 ^ 4)
      + Polynomial.C κ * ((17915904 : K[X]) * a1 * h0 ^ 6))) * he2 +
      (-(-((2580480 : K[X]) * e1 ^ 3 * h0 ^ 4) + (3133440 : K[X]) * e1 ^ 2
      * w1 ^ 2 * h0 ^ 3 - (798720 : K[X]) * e1 * e2 * w1 * h0 ^ 3 -
      (798720 : K[X]) * e1 * u2 * h0 ^ 4 - (276480 : K[X]) * e1 * w1 ^ 4 *
      h0 ^ 2 + (59719680 : K[X]) * e1 * a2 * h0 ^ 4 + (40960 : K[X]) * e2
      ^ 2 * h0 ^ 3 + (92160 : K[X]) * e2 * w1 ^ 3 * h0 ^ 2 + (92160 :
      K[X]) * u2 * w1 ^ 2 * h0 ^ 3 - (14929920 : K[X]) * w1 ^ 2 * a2 * h0
      ^ 3 + (44789760 : K[X]) * w1 * a1 * h0 ^ 5 - (134369280 : K[X]) * a0
      * h0 ^ 7 + Polynomial.C κ₅ * ((768 : K[X]) * h0 ^ 7) - Polynomial.C
      ν * ((2160 : K[X]) * w1 * h0 ^ 6) - Polynomial.C μ * ((100800 :
      K[X]) * e1 * w1 * h0 ^ 5) + Polynomial.C μ * ((13440 : K[X]) * e2 *
      h0 ^ 5) + Polynomial.C μ * ((2520 : K[X]) * w1 ^ 3 * h0 ^ 4) +
      Polynomial.C κ * ((1105920 : K[X]) * e1 ^ 2 * h0 ^ 5) - Polynomial.C
      κ * ((552960 : K[X]) * e1 * w1 ^ 2 * h0 ^ 4) + Polynomial.C κ *
      ((110592 : K[X]) * e2 * w1 * h0 ^ 4) + Polynomial.C κ * ((110592 :
      K[X]) * u2 * h0 ^ 5) - Polynomial.C κ * ((11943936 : K[X]) * a2 * h0
      ^ 5))) * hu2
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have hev := congrArg (fun t : K[X] => t.eval (-(d / c))) hR10
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hev
  rw [hroot] at hev
  have hzero :
      ((2048 : K[X]) * e1 ^ 3 * w1 ^ 4 -
        Polynomial.C μ * w1 ^ 7).eval (-(d / c)) = 0 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
    linear_combination (-(135 : K)⁻¹) * hev
  obtain ⟨s2, hs2⟩ := linearPolynomial_dvd_of_eval_eq_zero_810 h0
    ((2048 : K[X]) * e1 ^ 3 * w1 ^ 4 - Polynomial.C μ * w1 ^ 7)
    (-(d / c)) hdeg1 hroot hzero
  have hR11 :
      ((184320 : K[X]) * e1 ^ 2 * e2 ^ 2 + (737280 : K[X]) * e1 ^ 2 * u2
        * w1 ^ 2 - (44789760 : K[X]) * e1 ^ 2 * w1 ^ 2 * a2 + (40960 :
        K[X]) * e2 ^ 2 * u2 - (2488320 : K[X]) * e2 ^ 2 * a2 + (92160 :
        K[X]) * u2 ^ 2 * w1 ^ 2 - (14929920 : K[X]) * u2 * w1 ^ 2 * a2 -
        (135 : K[X]) * s2 + (604661760 : K[X]) * w1 ^ 2 * a2 ^ 2 +
        Polynomial.C μ * ((2268 : K[X]) * e1 * w1 ^ 5)) + h0 * (-((387072
        : K[X]) * e1 ^ 5) - (2580480 : K[X]) * e1 ^ 3 * u2 + (29859840 :
        K[X]) * e1 ^ 3 * a2 - (798720 : K[X]) * e1 * u2 ^ 2 + (59719680 :
        K[X]) * e1 * u2 * a2 - (604661760 : K[X]) * e1 * a2 ^ 2 -
        Polynomial.C ν * ((81 : K[X]) * w1 ^ 5) + Polynomial.C μ * ((15120
        : K[X]) * e1 ^ 2 * w1 ^ 3) + Polynomial.C μ * ((2520 : K[X]) * u2
        * w1 ^ 3) - Polynomial.C μ * ((326592 : K[X]) * w1 ^ 3 * a2) -
        Polynomial.C κ * ((73728 : K[X]) * e1 * e2 ^ 2) - Polynomial.C κ *
        ((221184 : K[X]) * e1 * u2 * w1 ^ 2) + Polynomial.C κ * ((17915904
        : K[X]) * e1 * w1 ^ 2 * a2)) + h0 ^ 2 * ((268738560 : K[X]) * e1 ^
        2 * w1 * a1 - (44789760 : K[X]) * e1 * e2 * a1 + (44789760 : K[X])
        * u2 * w1 * a1 - (3627970560 : K[X]) * w1 * a1 * a2 - Polynomial.C
        ν * ((1080 : K[X]) * e1 * w1 ^ 3) - Polynomial.C μ * ((221760 :
        K[X]) * e1 ^ 3 * w1) + Polynomial.C μ * ((40320 : K[X]) * e1 ^ 2 *
        e2) - Polynomial.C μ * ((100800 : K[X]) * e1 * u2 * w1) +
        Polynomial.C μ * ((6531840 : K[X]) * e1 * w1 * a2) + Polynomial.C
        μ * ((13440 : K[X]) * e2 * u2) - Polynomial.C μ * ((870912 : K[X])
        * e2 * a2) + Polynomial.C κ * ((276480 : K[X]) * e1 ^ 4) +
        Polynomial.C κ * ((1105920 : K[X]) * e1 ^ 2 * u2) - Polynomial.C κ
        * ((17915904 : K[X]) * e1 ^ 2 * a2) + Polynomial.C κ * ((110592 :
        K[X]) * u2 ^ 2) - Polynomial.C κ * ((11943936 : K[X]) * u2 * a2) +
        Polynomial.C κ * ((241864704 : K[X]) * a2 ^ 2)) + h0 ^ 3 *
        (Polynomial.C ν₂ * ((9 : K[X]) * w1 ^ 3) - Polynomial.C ν *
        ((15120 : K[X]) * e1 ^ 2 * w1) + Polynomial.C ν * ((2880 : K[X]) *
        e1 * e2) - Polynomial.C ν * ((2160 : K[X]) * u2 * w1) +
        Polynomial.C ν * ((233280 : K[X]) * w1 * a2) + Polynomial.C μ *
        ((1959552 : K[X]) * w1 ^ 2 * a1) - Polynomial.C κ * ((107495424 :
        K[X]) * e1 * w1 * a1) + Polynomial.C κ * ((17915904 : K[X]) * e2 *
        a1)) + h0 ^ 4 * (-((201553920 : K[X]) * e1 ^ 2 * a0) - (134369280
        : K[X]) * u2 * a0 + (10883911680 : K[X]) * a0 * a2 + (5441955840 :
        K[X]) * a1 ^ 2 + Polynomial.C ν₂ * ((324 : K[X]) * e1 * w1) -
        Polynomial.C ν₂ * ((72 : K[X]) * e2) + Polynomial.C κ₅ * ((1152 :
        K[X]) * e1 ^ 2) + Polynomial.C κ₅ * ((768 : K[X]) * u2) -
        Polynomial.C κ₅ * ((62208 : K[X]) * a2) - Polynomial.C μ *
        ((7838208 : K[X]) * e1 * a1)) + h0 ^ 5 * (-(Polynomial.C μ₃ *
        (w1)) - Polynomial.C κ₇ * ((72 : K[X]) * e1) - Polynomial.C ν *
        ((1399680 : K[X]) * a1) - Polynomial.C μ * ((23514624 : K[X]) * w1
        * a0) + Polynomial.C κ * ((161243136 : K[X]) * e1 * a0)) + h0 ^ 6
        * (-((9795520512 : K[X]) * b0) - Polynomial.C κ₃ * ((20155392 :
        K[X]) * a0)) = Polynomial.C κ₉ * h0 ^ 6 := by
    apply mul_left_cancel₀ hh0
    linear_combination hR10 + (135 : K[X]) * hs2
  refine ⟨s2, hs2, ?_⟩
  simp only [alignedTenthSquarePeeledRow610]
  linear_combination hR11

end Max11DegreeRoutes
