import Fable610ScaleTwoAlignedTenthFacePart101Scratch
import Fable610ScaleTwoAlignedNinthFacePart102Scratch

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
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 6400000000 in
/-- Descent of the consumed degree-`5` row in the nonsquare chamber:
the `H²⁰`-peeled core `= κ₉ H⁵` absorbs the decic head through the
seventh-face divisibilities, peeling `H²` onto the head
`92160 g₁² (81 p₂ + 3 g₁² t₁ - g₁ t₂)²` — the CARRIED eighth-face `p₂`
divisor squared — so substituting `u` peels one more `H` onto the
cubic head `-10240 g₁ (6 g₁ t₁ - t₂)³` — the CARRIED ninth-face `t₃`
divisor cubed — so substituting `t₃` peels one more `H` onto the
PERFECT-SQUARE head `92160 (243 p₁ - g₁ u)²`, which vanishes at BOTH
simple roots and transfers to the NEW divisibility
`243 p₁ - g₁ u = H v`; substituting `v` peels the last `H` and solves
`q₀` OUTRIGHT with `κ₉` at level ZERO. -/
theorem alignedNonsquareTenth_descent_610 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    {H g1 f t1 t2 u t3 a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7 :
      K[X]}
    {κ κ₃ κ₅ κ₇ κ₉ : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hg1 : a5 = H ^ 2 * g1) (hf : a4 = H * f)
    (hD0 : alignedThirdDefect610 H a3 a4 a5 b7 κ = 0)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10)
    (hF0 : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ = 0)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15)
    (hI0 :
      alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ = 0)
    (hJ : alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₇ * H ^ 20)
    (hL0 : alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6
        b7 κ = 0)
    (hO : alignedTenthDefect610 H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5
        b6 b7 κ = Polynomial.C κ₉ * H ^ 25)
    (ht1 : (3 : K[X]) * f - g1 ^ 2 = H * t1)
    (ht2 : (27 : K[X]) * a3 - g1 ^ 3 = H * t2)
    (hu : (81 : K[X]) * a2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
      H * u)
    (ht3 : t2 - (6 : K[X]) * g1 * t1 = H * t3) :
    ∃ v : K[X],
      (243 : K[X]) * a1 - g1 * u = H * v ∧
      (9795520512 : K[X]) * b0 =
        alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ -
          Polynomial.C κ₉ := by
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hO' := hO
  unfold alignedTenthDefect610 at hO'
  rw [hD0, hE, hF0, hG, hI0, hJ, hL0, hg1, hf] at hO'
  have hcore :
      (-((94058496 : K[X]) * f ^ 5) + (783820800 : K[X]) * f ^ 4 * g1 ^
        2 - (1881169920 : K[X]) * f ^ 3 * a3 * g1 - (1132185600 : K[X]) *
        f ^ 3 * g1 ^ 4 + (1209323520 : K[X]) * f ^ 2 * a3 ^ 2 +
        (3135283200 : K[X]) * f ^ 2 * a3 * g1 ^ 3 + (603832320 : K[X]) * f
        ^ 2 * g1 ^ 6 - (2821754880 : K[X]) * f * a3 ^ 2 * g1 ^ 2 -
        (1358622720 : K[X]) * f * a3 * g1 ^ 5 - (136581120 : K[X]) * f *
        g1 ^ 8 + (806215680 : K[X]) * a3 ^ 3 * g1 + (783820800 : K[X]) *
        a3 ^ 2 * g1 ^ 4 + (172523520 : K[X]) * a3 * g1 ^ 7 + (11128832 :
        K[X]) * g1 ^ 10) + H * ((806215680 : K[X]) * f ^ 3 * a2 -
        (2821754880 : K[X]) * f ^ 2 * g1 ^ 2 * a2 + (4837294080 : K[X]) *
        f * a3 * g1 * a2 + (1567641600 : K[X]) * f * g1 ^ 4 * a2 -
        (1813985280 : K[X]) * a3 ^ 2 * a2 - (1881169920 : K[X]) * a3 * g1
        ^ 3 * a2 - (226437120 : K[X]) * g1 ^ 6 * a2 + Polynomial.C κ *
        ((22394880 : K[X]) * f ^ 4) - Polynomial.C κ * ((119439360 : K[X])
        * f ^ 3 * g1 ^ 2) + Polynomial.C κ * ((268738560 : K[X]) * f ^ 2 *
        a3 * g1) + Polynomial.C κ * ((109486080 : K[X]) * f ^ 2 * g1 ^ 4)
        - Polynomial.C κ * ((161243136 : K[X]) * f * a3 ^ 2) -
        Polynomial.C κ * ((238878720 : K[X]) * f * a3 * g1 ^ 3) -
        Polynomial.C κ * ((34062336 : K[X]) * f * g1 ^ 6) + Polynomial.C κ
        * ((134369280 : K[X]) * a3 ^ 2 * g1 ^ 2) + Polynomial.C κ *
        ((43794432 : K[X]) * a3 * g1 ^ 5) + Polynomial.C κ * ((3446784 :
        K[X]) * g1 ^ 8)) + H ^ 2 * ((2418647040 : K[X]) * f ^ 2 * g1 * a1
        - (3627970560 : K[X]) * f * a3 * a1 - (1881169920 : K[X]) * f * g1
        ^ 3 * a1 - (1813985280 : K[X]) * f * a2 ^ 2 + (2418647040 : K[X])
        * a3 * g1 ^ 2 * a1 + (313528320 : K[X]) * g1 ^ 5 * a1 +
        (1209323520 : K[X]) * g1 ^ 2 * a2 ^ 2 - Polynomial.C κ *
        ((161243136 : K[X]) * f ^ 2 * a2) + Polynomial.C κ * ((268738560 :
        K[X]) * f * g1 ^ 2 * a2) - Polynomial.C κ * ((322486272 : K[X]) *
        a3 * g1 * a2) - Polynomial.C κ * ((59719680 : K[X]) * g1 ^ 4 *
        a2)) + H ^ 3 * (-((1813985280 : K[X]) * f ^ 2 * a0) + (2418647040
        : K[X]) * f * g1 ^ 2 * a0 - (3627970560 : K[X]) * a3 * g1 * a0 -
        (470292480 : K[X]) * g1 ^ 4 * a0 - (3627970560 : K[X]) * g1 * a1 *
        a2 + Polynomial.C κ₅ * ((10368 : K[X]) * f ^ 2) - Polynomial.C κ₅
        * ((13824 : K[X]) * f * g1 ^ 2) + Polynomial.C κ₅ * ((20736 :
        K[X]) * a3 * g1) + Polynomial.C κ₅ * ((2688 : K[X]) * g1 ^ 4) -
        Polynomial.C κ * ((322486272 : K[X]) * f * g1 * a1) + Polynomial.C
        κ * ((483729408 : K[X]) * a3 * a1) + Polynomial.C κ * ((89579520 :
        K[X]) * g1 ^ 3 * a1) + Polynomial.C κ * ((241864704 : K[X]) * a2 ^
        2)) + H ^ 4 * ((10883911680 : K[X]) * a0 * a2 + (5441955840 :
        K[X]) * a1 ^ 2 - Polynomial.C κ₇ * ((216 : K[X]) * f) +
        Polynomial.C κ₇ * ((72 : K[X]) * g1 ^ 2) - Polynomial.C κ₅ *
        ((62208 : K[X]) * a2) + Polynomial.C κ * ((483729408 : K[X]) * f *
        a0) - Polynomial.C κ * ((161243136 : K[X]) * g1 ^ 2 * a0)) + H ^ 5
        * (-((9795520512 : K[X]) * b0) - Polynomial.C κ₃ * ((20155392 :
        K[X]) * a0)) = Polynomial.C κ₉ * H ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero 20 hH)
    linear_combination hO'
  have hR2 :
      ((829440 : K[X]) * t1 ^ 2 * g1 ^ 6 - (552960 : K[X]) * t1 * t2 *
        g1 ^ 5 + (44789760 : K[X]) * t1 * g1 ^ 4 * a2 + (92160 : K[X]) *
        t2 ^ 2 * g1 ^ 4 - (14929920 : K[X]) * t2 * g1 ^ 3 * a2 +
        (604661760 : K[X]) * g1 ^ 2 * a2 ^ 2) + H * (-((9676800 : K[X]) *
        t1 ^ 3 * g1 ^ 4) + (5529600 : K[X]) * t1 ^ 2 * t2 * g1 ^ 3 -
        (223948800 : K[X]) * t1 ^ 2 * g1 ^ 2 * a2 - (921600 : K[X]) * t1 *
        t2 ^ 2 * g1 ^ 2 + (59719680 : K[X]) * t1 * t2 * g1 * a2 -
        (134369280 : K[X]) * t1 * g1 ^ 3 * a1 - (604661760 : K[X]) * t1 *
        a2 ^ 2 + (40960 : K[X]) * t2 ^ 3 * g1 - (2488320 : K[X]) * t2 ^ 2
        * a2 + (44789760 : K[X]) * t2 * g1 ^ 2 * a1 - (3627970560 : K[X])
        * g1 * a1 * a2 + Polynomial.C κ * ((1658880 : K[X]) * t1 ^ 2 * g1
        ^ 4) - Polynomial.C κ * ((884736 : K[X]) * t1 * t2 * g1 ^ 3) +
        Polynomial.C κ * ((53747712 : K[X]) * t1 * g1 ^ 2 * a2) +
        Polynomial.C κ * ((110592 : K[X]) * t2 ^ 2 * g1 ^ 2) -
        Polynomial.C κ * ((11943936 : K[X]) * t2 * g1 * a2) + Polynomial.C
        κ * ((241864704 : K[X]) * a2 ^ 2)) + H ^ 2 * ((7741440 : K[X]) *
        t1 ^ 4 * g1 ^ 2 - (2580480 : K[X]) * t1 ^ 3 * t2 * g1 + (29859840
        : K[X]) * t1 ^ 3 * a2 + (184320 : K[X]) * t1 ^ 2 * t2 ^ 2 +
        (268738560 : K[X]) * t1 ^ 2 * g1 * a1 - (44789760 : K[X]) * t1 *
        t2 * a1 + (403107840 : K[X]) * t1 * g1 ^ 2 * a0 - (134369280 :
        K[X]) * t2 * g1 * a0 + (10883911680 : K[X]) * a0 * a2 +
        (5441955840 : K[X]) * a1 ^ 2 - Polynomial.C κ₅ * ((2304 : K[X]) *
        t1 * g1 ^ 2) + Polynomial.C κ₅ * ((768 : K[X]) * t2 * g1) -
        Polynomial.C κ₅ * ((62208 : K[X]) * a2) - Polynomial.C κ *
        ((3317760 : K[X]) * t1 ^ 3 * g1 ^ 2) + Polynomial.C κ * ((1105920
        : K[X]) * t1 ^ 2 * t2 * g1) - Polynomial.C κ * ((17915904 : K[X])
        * t1 ^ 2 * a2) - Polynomial.C κ * ((73728 : K[X]) * t1 * t2 ^ 2) -
        Polynomial.C κ * ((107495424 : K[X]) * t1 * g1 * a1) +
        Polynomial.C κ * ((17915904 : K[X]) * t2 * a1)) + H ^ 3 *
        (-((387072 : K[X]) * t1 ^ 5) - (201553920 : K[X]) * t1 ^ 2 * a0 -
        (9795520512 : K[X]) * b0 - Polynomial.C κ₇ * ((72 : K[X]) * t1) +
        Polynomial.C κ₅ * ((1152 : K[X]) * t1 ^ 2) - Polynomial.C κ₃ *
        ((20155392 : K[X]) * a0) + Polynomial.C κ * ((276480 : K[X]) * t1
        ^ 4) + Polynomial.C κ * ((161243136 : K[X]) * t1 * a0)) =
        Polynomial.C κ₉ * H ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    linear_combination hcore + (-(-((387072 : K[X]) * t1 ^ 4 * H ^ 4) + (8128512 : K[X]) * t1 ^ 3 *
      g1 ^ 2 * H ^ 3 - (1161216 : K[X]) * t1 ^ 3 * f * H ^ 3 - (15224832 :
      K[X]) * t1 ^ 2 * g1 ^ 4 * H ^ 2 + (25546752 : K[X]) * t1 ^ 2 * g1 ^
      2 * f * H ^ 2 - (69672960 : K[X]) * t1 ^ 2 * g1 * a3 * H ^ 2 -
      (3483648 : K[X]) * t1 ^ 2 * f ^ 2 * H ^ 2 + (29859840 : K[X]) * t1 ^
      2 * a2 * H ^ 3 + (10708992 : K[X]) * t1 * g1 ^ 6 * H - (71221248 :
      K[X]) * t1 * g1 ^ 4 * f * H + (209018880 : K[X]) * t1 * g1 ^ 3 * a3
      * H + (80123904 : K[X]) * t1 * g1 ^ 2 * f ^ 2 * H - (253808640 :
      K[X]) * t1 * g1 ^ 2 * a2 * H ^ 2 - (209018880 : K[X]) * t1 * g1 * f
      * a3 * H + (268738560 : K[X]) * t1 * g1 * a1 * H ^ 3 - (10450944 :
      K[X]) * t1 * f ^ 3 * H + (89579520 : K[X]) * t1 * f * a2 * H ^ 2 +
      (134369280 : K[X]) * t1 * a3 ^ 2 * H - (201553920 : K[X]) * t1 * a0
      * H ^ 4 - (11077632 : K[X]) * g1 ^ 8 + (103348224 : K[X]) * g1 ^ 6 *
      f - (174182400 : K[X]) * g1 ^ 5 * a3 - (293787648 : K[X]) * g1 ^ 4 *
      f ^ 2 + (238878720 : K[X]) * g1 ^ 4 * a2 * H + (836075520 : K[X]) *
      g1 ^ 3 * f * a3 - (358318080 : K[X]) * g1 ^ 3 * a1 * H ^ 2 +
      (250822656 : K[X]) * g1 ^ 2 * f ^ 3 - (851005440 : K[X]) * g1 ^ 2 *
      f * a2 * H - (806215680 : K[X]) * g1 ^ 2 * a3 ^ 2 + (604661760 :
      K[X]) * g1 ^ 2 * a0 * H ^ 3 - (627056640 : K[X]) * g1 * f ^ 2 * a3 +
      (806215680 : K[X]) * g1 * f * a1 * H ^ 2 + (1612431360 : K[X]) * g1
      * a3 * a2 * H - (31352832 : K[X]) * f ^ 4 + (268738560 : K[X]) * f ^
      2 * a2 * H + (403107840 : K[X]) * f * a3 ^ 2 - (604661760 : K[X]) *
      f * a0 * H ^ 3 - (1209323520 : K[X]) * a3 * a1 * H ^ 2 - (604661760
      : K[X]) * a2 ^ 2 * H ^ 2 - Polynomial.C κ₇ * ((72 : K[X]) * H ^ 4) +
      Polynomial.C κ₅ * ((1152 : K[X]) * t1 * H ^ 4) - Polynomial.C κ₅ *
      ((3456 : K[X]) * g1 ^ 2 * H ^ 3) + Polynomial.C κ₅ * ((3456 : K[X])
      * f * H ^ 3) + Polynomial.C κ * ((276480 : K[X]) * t1 ^ 3 * H ^ 4) -
      Polynomial.C κ * ((3594240 : K[X]) * t1 ^ 2 * g1 ^ 2 * H ^ 3) +
      Polynomial.C κ * ((829440 : K[X]) * t1 ^ 2 * f * H ^ 3) +
      Polynomial.C κ * ((4147200 : K[X]) * t1 * g1 ^ 4 * H ^ 2) -
      Polynomial.C κ * ((11612160 : K[X]) * t1 * g1 ^ 2 * f * H ^ 2) +
      Polynomial.C κ * ((29859840 : K[X]) * t1 * g1 * a3 * H ^ 2) +
      Polynomial.C κ * ((2488320 : K[X]) * t1 * f ^ 2 * H ^ 2) -
      Polynomial.C κ * ((17915904 : K[X]) * t1 * a2 * H ^ 3) -
      Polynomial.C κ * ((3336192 : K[X]) * g1 ^ 6 * H) + Polynomial.C κ *
      ((24053760 : K[X]) * g1 ^ 4 * f * H) - Polynomial.C κ * ((49766400 :
      K[X]) * g1 ^ 3 * a3 * H) - Polynomial.C κ * ((37324800 : K[X]) * g1
      ^ 2 * f ^ 2 * H) + Polynomial.C κ * ((71663616 : K[X]) * g1 ^ 2 * a2
      * H ^ 2) + Polynomial.C κ * ((89579520 : K[X]) * g1 * f * a3 * H) -
      Polynomial.C κ * ((107495424 : K[X]) * g1 * a1 * H ^ 3) +
      Polynomial.C κ * ((7464960 : K[X]) * f ^ 3 * H) - Polynomial.C κ *
      ((53747712 : K[X]) * f * a2 * H ^ 2) - Polynomial.C κ * ((53747712 :
      K[X]) * a3 ^ 2 * H) + Polynomial.C κ * ((161243136 : K[X]) * a0 * H
      ^ 4))) * ht1 + (-(-((2580480 : K[X]) * t1 ^ 3 * g1 * H ^ 3) +
      (184320 : K[X]) * t1 ^ 2 * t2 * H ^ 3 + (5345280 : K[X]) * t1 ^ 2 *
      g1 ^ 3 * H ^ 2 + (4976640 : K[X]) * t1 ^ 2 * a3 * H ^ 2 - (921600 :
      K[X]) * t1 * t2 * g1 ^ 2 * H ^ 2 + (368640 : K[X]) * t1 * g1 ^ 5 * H
      - (24883200 : K[X]) * t1 * g1 ^ 2 * a3 * H + (59719680 : K[X]) * t1
      * g1 * a2 * H ^ 2 - (44789760 : K[X]) * t1 * a1 * H ^ 3 + (40960 :
      K[X]) * t2 ^ 2 * g1 * H ^ 2 + (51200 : K[X]) * t2 * g1 ^ 4 * H +
      (1105920 : K[X]) * t2 * g1 * a3 * H - (2488320 : K[X]) * t2 * a2 * H
      ^ 2 - (51200 : K[X]) * g1 ^ 7 + (276480 : K[X]) * g1 ^ 4 * a3 -
      (12441600 : K[X]) * g1 ^ 3 * a2 * H + (44789760 : K[X]) * g1 ^ 2 *
      a1 * H ^ 2 + (29859840 : K[X]) * g1 * a3 ^ 2 - (134369280 : K[X]) *
      g1 * a0 * H ^ 3 - (67184640 : K[X]) * a3 * a2 * H + Polynomial.C κ₅
      * ((768 : K[X]) * g1 * H ^ 3) + Polynomial.C κ * ((1105920 : K[X]) *
      t1 ^ 2 * g1 * H ^ 3) - Polynomial.C κ * ((73728 : K[X]) * t1 * t2 *
      H ^ 3) - Polynomial.C κ * ((811008 : K[X]) * t1 * g1 ^ 3 * H ^ 2) -
      Polynomial.C κ * ((1990656 : K[X]) * t1 * a3 * H ^ 2) + Polynomial.C
      κ * ((110592 : K[X]) * t2 * g1 ^ 2 * H ^ 2) - Polynomial.C κ *
      ((110592 : K[X]) * g1 ^ 5 * H) + Polynomial.C κ * ((2985984 : K[X])
      * g1 ^ 2 * a3 * H) - Polynomial.C κ * ((11943936 : K[X]) * g1 * a2 *
      H ^ 2) + Polynomial.C κ * ((17915904 : K[X]) * a1 * H ^ 3))) * ht2
  have hR3 :
      (-((2211840 : K[X]) * t1 ^ 3 * g1 ^ 4) + (1105920 : K[X]) * t1 ^ 2
        * t2 * g1 ^ 3 - (184320 : K[X]) * t1 * t2 ^ 2 * g1 ^ 2 + (10240 :
        K[X]) * t2 ^ 3 * g1) + H * ((6635520 : K[X]) * t1 ^ 4 * g1 ^ 2 -
        (2211840 : K[X]) * t1 ^ 3 * t2 * g1 + (184320 : K[X]) * t1 ^ 2 *
        t2 ^ 2 - (2211840 : K[X]) * t1 ^ 2 * u * g1 ^ 2 + (268738560 :
        K[X]) * t1 ^ 2 * g1 * a1 + (552960 : K[X]) * t1 * t2 * u * g1 -
        (44789760 : K[X]) * t1 * t2 * a1 - (30720 : K[X]) * t2 ^ 2 * u +
        (92160 : K[X]) * u ^ 2 * g1 ^ 2 - (44789760 : K[X]) * u * g1 * a1
        + (5441955840 : K[X]) * a1 ^ 2 - Polynomial.C κ * ((2654208 :
        K[X]) * t1 ^ 3 * g1 ^ 2) + Polynomial.C κ * ((884736 : K[X]) * t1
        ^ 2 * t2 * g1) - Polynomial.C κ * ((73728 : K[X]) * t1 * t2 ^ 2) +
        Polynomial.C κ * ((442368 : K[X]) * t1 * u * g1 ^ 2) -
        Polynomial.C κ * ((107495424 : K[X]) * t1 * g1 * a1) -
        Polynomial.C κ * ((73728 : K[X]) * t2 * u * g1) + Polynomial.C κ *
        ((17915904 : K[X]) * t2 * a1)) + H ^ 2 * (-((387072 : K[X]) * t1 ^
        5) + (368640 : K[X]) * t1 ^ 3 * u - (201553920 : K[X]) * t1 ^ 2 *
        a0 - (92160 : K[X]) * t1 * u ^ 2 + (134369280 : K[X]) * u * a0 -
        (9795520512 : K[X]) * b0 - Polynomial.C κ₇ * ((72 : K[X]) * t1) +
        Polynomial.C κ₅ * ((1152 : K[X]) * t1 ^ 2) - Polynomial.C κ₅ *
        ((768 : K[X]) * u) - Polynomial.C κ₃ * ((20155392 : K[X]) * a0) +
        Polynomial.C κ * ((276480 : K[X]) * t1 ^ 4) - Polynomial.C κ *
        ((221184 : K[X]) * t1 ^ 2 * u) + Polynomial.C κ * ((161243136 :
        K[X]) * t1 * a0) + Polynomial.C κ * ((36864 : K[X]) * u ^ 2)) =
        Polynomial.C κ₉ * H ^ 2 := by
    apply mul_left_cancel₀ hH
    linear_combination hR2 + (-((368640 : K[X]) * t1 ^ 3 * H ^ 2 - (2488320 : K[X]) * t1 ^ 2 * g1
      ^ 2 * H + (645120 : K[X]) * t1 * t2 * g1 * H - (92160 : K[X]) * t1 *
      u * H ^ 2 + (276480 : K[X]) * t1 * g1 ^ 4 - (7464960 : K[X]) * t1 *
      a2 * H - (30720 : K[X]) * t2 ^ 2 * H - (92160 : K[X]) * t2 * g1 ^ 3
      + (92160 : K[X]) * u * g1 ^ 2 * H + (7464960 : K[X]) * g1 ^ 2 * a2 -
      (44789760 : K[X]) * g1 * a1 * H + (134369280 : K[X]) * a0 * H ^ 2 -
      Polynomial.C κ₅ * ((768 : K[X]) * H ^ 2) - Polynomial.C κ * ((221184
      : K[X]) * t1 ^ 2 * H ^ 2) + Polynomial.C κ * ((552960 : K[X]) * t1 *
      g1 ^ 2 * H) - Polynomial.C κ * ((110592 : K[X]) * t2 * g1 * H) +
      Polynomial.C κ * ((36864 : K[X]) * u * H ^ 2) + Polynomial.C κ *
      ((2985984 : K[X]) * a2 * H))) * hu
  have hR4 :
      ((92160 : K[X]) * u ^ 2 * g1 ^ 2 - (44789760 : K[X]) * u * g1 * a1
        + (5441955840 : K[X]) * a1 ^ 2) + H * (-((387072 : K[X]) * t1 ^ 5)
        + (368640 : K[X]) * t1 ^ 3 * u - (201553920 : K[X]) * t1 ^ 2 * a0
        - (92160 : K[X]) * t1 * u ^ 2 + (184320 : K[X]) * t1 * u * t3 * g1
        - (44789760 : K[X]) * t1 * t3 * a1 + (134369280 : K[X]) * u * a0 -
        (9795520512 : K[X]) * b0 - Polynomial.C κ₇ * ((72 : K[X]) * t1) +
        Polynomial.C κ₅ * ((1152 : K[X]) * t1 ^ 2) - Polynomial.C κ₅ *
        ((768 : K[X]) * u) - Polynomial.C κ₃ * ((20155392 : K[X]) * a0) +
        Polynomial.C κ * ((276480 : K[X]) * t1 ^ 4) - Polynomial.C κ *
        ((221184 : K[X]) * t1 ^ 2 * u) + Polynomial.C κ * ((161243136 :
        K[X]) * t1 * a0) + Polynomial.C κ * ((36864 : K[X]) * u ^ 2) -
        Polynomial.C κ * ((73728 : K[X]) * u * t3 * g1) + Polynomial.C κ *
        ((17915904 : K[X]) * t3 * a1)) + H ^ 2 * ((184320 : K[X]) * t1 ^ 2
        * t3 ^ 2 - (30720 : K[X]) * u * t3 ^ 2 + (10240 : K[X]) * t3 ^ 3 *
        g1 - Polynomial.C κ * ((73728 : K[X]) * t1 * t3 ^ 2)) =
        Polynomial.C κ₉ * H := by
    apply mul_left_cancel₀ hH
    linear_combination hR3 + (-(-((1105920 : K[X]) * t1 ^ 3 * g1 * H) + (184320 : K[X]) * t1 ^ 2
      * t2 * H + (184320 : K[X]) * t1 ^ 2 * t3 * H ^ 2 + (368640 : K[X]) *
      t1 ^ 2 * g1 ^ 3 - (122880 : K[X]) * t1 * t2 * g1 ^ 2 + (368640 :
      K[X]) * t1 * u * g1 * H - (61440 : K[X]) * t1 * t3 * g1 ^ 2 * H -
      (44789760 : K[X]) * t1 * a1 * H + (10240 : K[X]) * t2 ^ 2 * g1 -
      (30720 : K[X]) * t2 * u * H + (10240 : K[X]) * t2 * t3 * g1 * H -
      (30720 : K[X]) * u * t3 * H ^ 2 + (10240 : K[X]) * t3 ^ 2 * g1 * H ^
      2 + Polynomial.C κ * ((442368 : K[X]) * t1 ^ 2 * g1 * H) -
      Polynomial.C κ * ((73728 : K[X]) * t1 * t2 * H) - Polynomial.C κ *
      ((73728 : K[X]) * t1 * t3 * H ^ 2) - Polynomial.C κ * ((73728 :
      K[X]) * u * g1 * H) + Polynomial.C κ * ((17915904 : K[X]) * a1 *
      H))) * ht3
  have hkey : ∀ a : K, H.eval a = 0 →
      ((243 : K[X]) * a1 - g1 * u).eval a = 0 := by
    intro a ha
    have hev := congrArg (fun t : K[X] => t.eval a) hR4
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_ofNat, Polynomial.eval_zero] at hev
    rw [ha] at hev
    have hsq2 : (((243 : K[X]) * a1 - g1 * u).eval a) ^ 2 = 0 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat]
      linear_combination ((92160 : K)⁻¹) * hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq2
  obtain ⟨v, hv⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hkey
  have hq0 :
      (9795520512 : K[X]) * b0 =
        (-((387072 : K[X]) * t1 ^ 5) + (368640 : K[X]) * t1 ^ 3 * u -
        (201553920 : K[X]) * t1 ^ 2 * a0 - (92160 : K[X]) * t1 * u ^ 2 +
        (134369280 : K[X]) * u * a0 - Polynomial.C κ₇ * ((72 : K[X]) * t1)
        + Polynomial.C κ₅ * ((1152 : K[X]) * t1 ^ 2) - Polynomial.C κ₅ *
        ((768 : K[X]) * u) - Polynomial.C κ₃ * ((20155392 : K[X]) * a0) +
        Polynomial.C κ * ((276480 : K[X]) * t1 ^ 4) - Polynomial.C κ *
        ((221184 : K[X]) * t1 ^ 2 * u) + Polynomial.C κ * ((161243136 :
        K[X]) * t1 * a0) + Polynomial.C κ * ((36864 : K[X]) * u ^ 2)) + H
        * ((184320 : K[X]) * t1 ^ 2 * t3 ^ 2 - (184320 : K[X]) * t1 * t3 *
        v - (30720 : K[X]) * u * t3 ^ 2 + (10240 : K[X]) * t3 ^ 3 * g1 +
        (92160 : K[X]) * v ^ 2 - Polynomial.C κ * ((73728 : K[X]) * t1 *
        t3 ^ 2) + Polynomial.C κ * ((73728 : K[X]) * t3 * v)) -
        Polynomial.C κ₉ := by
    apply mul_left_cancel₀ hH
    linear_combination -hR4 + (-((184320 : K[X]) * t1 * t3 * H) - (92160 : K[X]) * u * g1 + (92160
      : K[X]) * v * H + (22394880 : K[X]) * a1 + Polynomial.C κ * ((73728
      : K[X]) * t3 * H)) * hv
  refine ⟨v, hv, ?_⟩
  simp only [alignedTenthNonsquareSolved610]
  linear_combination hq0

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 3200000000 in
/-- On the aligned face, with the consumed degree-`13` through
degree-`6` rows, the degree-`5` row is the weighted derivative
`H Ω' - 25 Ω H' = 0`. -/
theorem alignedTenthDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    H * (alignedTenthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 0) (q.coeff 1) (q.coeff
      2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
      κ).derivative - (25 : K[X]) * alignedTenthDefect610 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedTenthCoefficientJacobianRow_610 hp hq hjac
  rw [hp6] at hrow
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5, hC6] at hrow
  have hDrow :=
    alignedThirdDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hErow :=
    alignedFourthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hFrow :=
    alignedFifthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hGrow :=
    alignedSixthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hIrow :=
    alignedSeventhDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hJrow :=
    alignedEighthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hLrow :=
    alignedNinthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hid := alignedTenthDefect_weightedDerivative_identity_610
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
    (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hDrow, hErow, hFrow, hGrow, hIrow, hJrow, hLrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Weight-`25` polynomial first integral of the aligned `(6,10)`
tenth defect: `Ω = κ₉ H²⁵`.  The even exponent makes the integral
chamber-free — no square root of `H` is required and `κ₉` is preserved
in both chambers. -/
theorem alignedTenthDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₉ : K,
      alignedTenthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 0) (q.coeff 1)
        (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
        (q.coeff 7) κ = Polynomial.C κ₉ * H ^ 25 := by
  let O : K[X] :=
    alignedTenthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff
    3) (p.coeff 4) (p.coeff 5) (q.coeff 0) (q.coeff 1) (q.coeff 2)
    (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow : H * O.derivative - (25 : K[X]) * O * H.derivative = 0 := by
    simpa only [O] using
      alignedTenthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC25 : Polynomial.C (25 : K) = (25 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian O (H ^ 25) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      O * (Polynomial.C (25 : K) * H ^ (25 - 1) * H.derivative) -
          O.derivative * H ^ 25 =
          H ^ 24 *
            (Polynomial.C (25 : K) * O * H.derivative -
              H * O.derivative) := by
        ring
      _ = 0 := by
        rw [hC25]
        have hfac :
            (25 : K[X]) * O * H.derivative - H * O.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 25 hH) hW

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Exact square-chamber tenth packet of a normalized aligned
scale-two `(6,10)` source: everything from the ninth packet, plus the
NEW μ-loaded divisibility `2048 e₁³ w₁⁴ - μ w₁⁷ = h₀ s₂`, the peeled
tenth row `= κ₉ h₀⁶` with `q₀` tied at `h₀⁶`, and the chamber-free
integral `Ω = κ₉ H²⁵`. -/
theorem normalized610ScaleTwo_alignedTenthFace_squareChamber_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ μ κ₃ ν κ₅ ν₂ κ₇ κ₈ μ₃ κ₉ : K)
      (w1 f2 e1 e2 u2 e3 s2 : K[X]),
      μ₃ ^ 2 = κ₈ ∧
        alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        p.coeff 5 = h0 ^ 4 * w1 ∧
        p.coeff 4 = h0 ^ 2 * f2 ∧
        (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
        (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
        w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
        alignedEighthSquarePeeledRow610 h0 w1 e1 e2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 2) κ μ κ₃ ν κ₅ ν₂ =
          Polynomial.C κ₇ * h0 ^ 6 ∧
        e2 = h0 * e3 ∧
        (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 ^ 2 * e3 ∧
        alignedNinthSquarePeeledRow610 h0 w1 e1 e2 u2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ κ₃ ν κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 ∧
        (2048 : K[X]) * e1 ^ 3 * w1 ^ 4 - Polynomial.C μ * w1 ^ 7 =
          h0 * s2 ∧
        alignedTenthSquarePeeledRow610 h0 w1 e1 e2 u2 s2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 0)
            κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ =
          Polynomial.C κ₉ * h0 ^ 6 ∧
        alignedEighthSquareCombinedRow610 h0 w1 e1 e2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 2) (q.coeff 3)
            κ μ κ₃ ν κ₅ ν₂ =
          Polynomial.C κ₇ * h0 ^ 5 +
            Polynomial.C ν₂ * ((2 : K[X]) * w1 * h0 ^ 4) ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ =
          Polynomial.C μ * h0 ^ 15 ∧
        alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 10 ∧
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ =
          Polynomial.C ν * h0 ^ 25 ∧
        alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₅ * H ^ 15 ∧
        alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C ν₂ * h0 ^ 35 ∧
        alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₇ * H ^ 20 ∧
        alignedNinthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2)
            (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ =
          Polynomial.C μ₃ * h0 ^ 45 ∧
        alignedTenthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 0) (q.coeff 1)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 25 := by
  dsimp only at haligned ⊢
  have hsrc := hsource
  rcases hsrc with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hpacket9 :=
    normalized610ScaleTwo_alignedNinthFace_squareChamber_packet
      hsource hh0 hHsq haligned
  dsimp only at hpacket9
  obtain ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, κ₈, μ₃, w1, f2, e1, e2, u2, e3, hμ₃,
    hM, hp5w1, hp4f2, he1, he2, hu2, hR8, he3, h27, hR9, hQ9, hD, hE,
    hF, hG, hI, hJ, hL⟩ := hpacket9
  obtain ⟨κ₉, hO⟩ :=
    alignedTenthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  have hdeg1 : h0.natDegree = 1 := by
    have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨s2, hs2, hR10x⟩ :=
    alignedSquareTenth_descent_610 hh0 hdeg1 hHsq hp5w1 hp4f2 hD hE hF
      hG hI hJ hL hO he1 he2 hu2
  exact ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, κ₈, μ₃, κ₉, w1, f2, e1, e2, u2, e3,
    s2, hμ₃, hM, hp5w1, hp4f2, he1, he2, hu2, hR8, he3, h27, hR9, hs2,
    hR10x, hQ9, hD, hE, hF, hG, hI, hJ, hL, hO⟩

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Exact nonsquare-chamber tenth packet of a normalized aligned
scale-two `(6,10)` source: the chamber-free integral `Ω = κ₉ H²⁵`
survives, the carried divisors peel the head cascade (the `p₂` divisor
squared, then the `t₃` divisor cubed), the NEW divisibility
`243 p₁ - g₁ u = H v` transfers the perfect-square head — the FIRST
`p₁` constraint of the aligned tower — and `q₀` is solved OUTRIGHT
with `κ₉` at level ZERO on top of the carried solved `q₁, q₂`. -/
theorem normalized610ScaleTwo_alignedTenthFace_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g1 f t1 t2 u t3 v : K[X]),
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        p.coeff 5 = H ^ 2 * g1 ∧
        p.coeff 4 = H * f ∧
        (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
        (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
        (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
          H * u ∧
        t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
        (243 : K[X]) * p.coeff 1 - g1 * u = H * v ∧
        (9795520512 : K[X]) * q.coeff 0 =
          alignedTenthNonsquareSolved610 H g1 t1 u t3 v (p.coeff 0)
              κ κ₃ κ₅ κ₇ -
            Polynomial.C κ₉ ∧
        (1632586752 : K[X]) * q.coeff 1 =
          alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 (p.coeff 0)
            (p.coeff 1) κ κ₃ κ₅ κ₇ ∧
        (15116544 : K[X]) * q.coeff 2 =
          alignedEighthNonsquareSolved610 H g1 t1 t2 u (p.coeff 0)
              (p.coeff 1) κ κ₃ κ₅ -
            Polynomial.C κ₇ * H ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = 0 ∧
        alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 10 ∧
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = 0 ∧
        alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₅ * H ^ 15 ∧
        alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₇ * H ^ 20 ∧
        alignedNinthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2)
            (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = 0 ∧
        alignedTenthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 0) (q.coeff 1)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 25 := by
  dsimp only at haligned ⊢
  have hsrc := hsource
  rcases hsrc with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hpacket9 :=
    normalized610ScaleTwo_alignedNinthFace_nonsquareChamber_packet
      hsource hnsq haligned
  dsimp only at hpacket9
  obtain ⟨κ, κ₃, κ₅, κ₇, g1, f, t1, t2, u, t3, hM, hp5, hf, ht1, ht2,
    hu, ht3, hq1, hq2, hD0, hE, hF0, hG, hI0, hJ, hL0⟩ := hpacket9
  obtain ⟨κ₉, hO⟩ :=
    alignedTenthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨v, hv, hq0⟩ :=
    alignedNonsquareTenth_descent_610 hH hHdegree hnsq hp5 hf hD0 hE
      hF0 hG hI0 hJ hL0 hO ht1 ht2 hu ht3
  exact ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, hM, hp5, hf, ht1,
    ht2, hu, ht3, hv, hq0, hq1, hq2, hD0, hE, hF0, hG, hI0, hJ, hL0,
    hO⟩

end Max11DegreeRoutes
