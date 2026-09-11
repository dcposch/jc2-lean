import Fable610ScaleTwoAlignedNinthFacePart02Scratch
import Fable610ScaleTwoAlignedNinthFacePart08Scratch
import Fable610ScaleTwoAlignedNinthFacePart07Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 6400000000 in
/-- Descent of the consumed degree-`6` row in the square chamber: the
`h₀³⁶`-peeled core absorbs the nonic head through the seventh-face
divisibilities and the eighth-face product divisor `u₂`, cancelling
`h₀³` into the peeled row `= μ₃ h₀⁶` with head
`27 w₁³ (10240 e₁³ - 7 μ w₁³) - 5120 e₂³` and `q₁` tied at `h₀⁵`; at
the root of `h₀` the head, the `u₂` root product, and the eighth-face
combined-row cubic force `e₂(a) = 0`, and the linear-root transfer
DEEPENS the seventh-face divisor to `27 p₃ - w₁³ = h₀² e₃`. -/
theorem alignedSquareNinth_descent_610 {K : Type*} [Field K]
    [CharZero K]
    {H h0 w1 f2 e1 e2 u2 a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 :
      K[X]}
    {κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K}
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
    (he1 : (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1)
    (he2 : (27 : K[X]) * a3 - w1 ^ 3 = h0 * e2)
    (hu2 : w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2)
    (hQ9 : alignedEighthSquareCombinedRow610 h0 w1 e1 e2 a0 a1 a2 b2 b3
        κ μ κ₃ ν κ₅ ν₂ =
      Polynomial.C κ₇ * h0 ^ 5 +
        Polynomial.C ν₂ * ((2 : K[X]) * w1 * h0 ^ 4)) :
    ∃ e3 : K[X],
      e2 = h0 * e3 ∧
      (27 : K[X]) * a3 - w1 ^ 3 = h0 ^ 2 * e3 ∧
      alignedNinthSquarePeeledRow610 h0 w1 e1 e2 u2 a0 a1 a2 b1
          κ μ κ₃ ν κ₅ ν₂ κ₇ = Polynomial.C μ₃ * h0 ^ 6 := by
  have hL' := hL
  simp only [alignedNinthDefect610] at hL'
  rw [hD, hE, hF, hG, hI, hJ, hHsq, hp5, hp4] at hL'
  have hcore :
      (-((78382080 : K[X]) * f2 ^ 4 * w1) + (134369280 : K[X]) * f2 ^ 3 * a3
        + (174182400 : K[X]) * f2 ^ 3 * w1 ^ 3 - (470292480 : K[X]) * f2 ^ 2
        * a3 * w1 ^ 2 - (113218560 : K[X]) * f2 ^ 2 * w1 ^ 5 + (403107840 :
        K[X]) * f2 * a3 ^ 2 * w1 + (261273600 : K[X]) * f2 * a3 * w1 ^ 4 +
        (28753920 : K[X]) * f2 * w1 ^ 7 - (100776960 : K[X]) * a3 ^ 3 -
        (156764160 : K[X]) * a3 ^ 2 * w1 ^ 3 - (37739520 : K[X]) * a3 * w1 ^
        6 - (2529280 : K[X]) * w1 ^ 9) + h0 ^ 2 * ((403107840 : K[X]) * f2 ^
        2 * w1 * a2 - (604661760 : K[X]) * f2 * a3 * a2 - (313528320 : K[X])
        * f2 * w1 ^ 3 * a2 + (403107840 : K[X]) * a3 * w1 ^ 2 * a2 +
        (52254720 : K[X]) * w1 ^ 5 * a2 + Polynomial.C κ * ((14929920 :
        K[X]) * f2 ^ 3 * w1) - Polynomial.C κ * ((26873856 : K[X]) * f2 ^ 2
        * a3) - Polynomial.C κ * ((19906560 : K[X]) * f2 ^ 2 * w1 ^ 3) +
        Polynomial.C κ * ((44789760 : K[X]) * f2 * a3 * w1 ^ 2) +
        Polynomial.C κ * ((7299072 : K[X]) * f2 * w1 ^ 5) - Polynomial.C κ *
        ((26873856 : K[X]) * a3 ^ 2 * w1) - Polynomial.C κ * ((9953280 :
        K[X]) * a3 * w1 ^ 4) - Polynomial.C κ * ((811008 : K[X]) * w1 ^ 7))
        + h0 ^ 3 * (Polynomial.C μ * ((544320 : K[X]) * f2 ^ 3) -
        Polynomial.C μ * ((1496880 : K[X]) * f2 ^ 2 * w1 ^ 2) + Polynomial.C
        μ * ((3265920 : K[X]) * f2 * a3 * w1) + Polynomial.C μ * ((706860 :
        K[X]) * f2 * w1 ^ 4) - Polynomial.C μ * ((1959552 : K[X]) * a3 ^ 2)
        - Polynomial.C μ * ((997920 : K[X]) * a3 * w1 ^ 3) - Polynomial.C μ
        * ((90321 : K[X]) * w1 ^ 6)) + h0 ^ 4 * (-((302330880 : K[X]) * f2 ^
        2 * a1) + (403107840 : K[X]) * f2 * w1 ^ 2 * a1 - (604661760 : K[X])
        * a3 * w1 * a1 - (78382080 : K[X]) * w1 ^ 4 * a1 - (302330880 :
        K[X]) * w1 * a2 ^ 2 - Polynomial.C κ * ((53747712 : K[X]) * f2 * w1
        * a2) + Polynomial.C κ * ((80621568 : K[X]) * a3 * a2) +
        Polynomial.C κ * ((14929920 : K[X]) * w1 ^ 3 * a2)) + h0 ^ 5 *
        (Polynomial.C ν * ((19440 : K[X]) * f2 ^ 2) - Polynomial.C ν *
        ((22680 : K[X]) * f2 * w1 ^ 2) + Polynomial.C ν * ((38880 : K[X]) *
        a3 * w1) + Polynomial.C ν * ((4095 : K[X]) * w1 ^ 4) - Polynomial.C
        μ * ((3919104 : K[X]) * f2 * a2) + Polynomial.C μ * ((1632960 :
        K[X]) * w1 ^ 2 * a2)) + h0 ^ 6 * (-((604661760 : K[X]) * f2 * w1 *
        a0) + (1813985280 : K[X]) * a3 * a0 + (134369280 : K[X]) * w1 ^ 3 *
        a0 + (1813985280 : K[X]) * a1 * a2 + Polynomial.C κ₅ * ((3456 :
        K[X]) * f2 * w1) - Polynomial.C κ₅ * ((10368 : K[X]) * a3) -
        Polynomial.C κ₅ * ((768 : K[X]) * w1 ^ 3) + Polynomial.C κ *
        ((80621568 : K[X]) * f2 * a1) - Polynomial.C κ * ((26873856 : K[X])
        * w1 ^ 2 * a1)) + h0 ^ 7 * (-(Polynomial.C ν₂ * ((324 : K[X]) * f2))
        + Polynomial.C ν₂ * ((81 : K[X]) * w1 ^ 2) - Polynomial.C ν *
        ((233280 : K[X]) * a2) - Polynomial.C μ * ((3919104 : K[X]) * w1 *
        a1)) + h0 ^ 8 * (-((1632586752 : K[X]) * b1) - Polynomial.C κ₇ *
        ((36 : K[X]) * w1) - Polynomial.C κ₃ * ((3359232 : K[X]) * a1) +
        Polynomial.C κ * ((80621568 : K[X]) * w1 * a0)) + h0 ^ 9 *
        (-(Polynomial.C μ * ((23514624 : K[X]) * a0))) = Polynomial.C μ₃ *
        h0 ^ 9 := by
    apply mul_left_cancel₀ (pow_ne_zero 36 hh0)
    linear_combination hL'
  have hR9 :
      ((276480 : K[X]) * e1 ^ 3 * w1 ^ 3 - (5120 : K[X]) * e2 ^ 3 -
        Polynomial.C μ * ((189 : K[X]) * w1 ^ 6)) + h0 * (-((967680 : K[X])
        * e1 ^ 4 * w1) + (184320 : K[X]) * e1 ^ 3 * e2 - (829440 : K[X]) *
        e1 ^ 2 * u2 * w1 + (44789760 : K[X]) * e1 ^ 2 * w1 * a2 + (184320 :
        K[X]) * e1 * e2 * u2 - (7464960 : K[X]) * e1 * e2 * a2 - (46080 :
        K[X]) * u2 ^ 2 * w1 + (7464960 : K[X]) * u2 * w1 * a2 - (302330880 :
        K[X]) * w1 * a2 ^ 2 - Polynomial.C μ * ((2268 : K[X]) * e1 * w1 ^
        4)) + h0 ^ 2 * (Polynomial.C ν * ((135 : K[X]) * w1 ^ 4) +
        Polynomial.C μ * ((15120 : K[X]) * e1 ^ 2 * w1 ^ 2) - Polynomial.C μ
        * ((2688 : K[X]) * e2 ^ 2) - Polynomial.C μ * ((2016 : K[X]) * u2 *
        w1 ^ 2) + Polynomial.C μ * ((326592 : K[X]) * w1 ^ 2 * a2) +
        Polynomial.C κ * ((552960 : K[X]) * e1 ^ 3 * w1) - Polynomial.C κ *
        ((110592 : K[X]) * e1 ^ 2 * e2) + Polynomial.C κ * ((221184 : K[X])
        * e1 * u2 * w1) - Polynomial.C κ * ((17915904 : K[X]) * e1 * w1 *
        a2) - Polynomial.C κ * ((36864 : K[X]) * e2 * u2) + Polynomial.C κ *
        ((2985984 : K[X]) * e2 * a2)) + h0 ^ 3 * (-((33592320 : K[X]) * e1 ^
        2 * a1) - (22394880 : K[X]) * u2 * a1 + (1813985280 : K[X]) * a1 *
        a2 + Polynomial.C ν * ((1080 : K[X]) * e1 * w1 ^ 2) + Polynomial.C μ
        * ((20160 : K[X]) * e1 ^ 3) + Polynomial.C μ * ((40320 : K[X]) * e1
        * u2) - Polynomial.C μ * ((1306368 : K[X]) * e1 * a2)) + h0 ^ 4 *
        (-((201553920 : K[X]) * e1 * w1 * a0) + (67184640 : K[X]) * e2 * a0
        - Polynomial.C ν₂ * ((27 : K[X]) * w1 ^ 2) + Polynomial.C κ₅ *
        ((1152 : K[X]) * e1 * w1) - Polynomial.C κ₅ * ((384 : K[X]) * e2) +
        Polynomial.C ν * ((2160 : K[X]) * e1 ^ 2) + Polynomial.C ν * ((1440
        : K[X]) * u2) - Polynomial.C ν * ((233280 : K[X]) * a2) -
        Polynomial.C μ * ((3919104 : K[X]) * w1 * a1) + Polynomial.C κ *
        ((26873856 : K[X]) * e1 * a1)) + h0 ^ 5 * (-((1632586752 : K[X]) *
        b1) - Polynomial.C κ₇ * ((36 : K[X]) * w1) - Polynomial.C ν₂ * ((108
        : K[X]) * e1) - Polynomial.C κ₃ * ((3359232 : K[X]) * a1) +
        Polynomial.C κ * ((80621568 : K[X]) * w1 * a0)) + h0 ^ 6 *
        (-(Polynomial.C μ * ((23514624 : K[X]) * a0))) = Polynomial.C μ₃ *
        h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    linear_combination hcore + (-(-((967680 : K[X]) * e1 ^ 3 * w1 * h0 ^ 3)
      + (3548160 : K[X]) * e1 ^ 2 * w1 ^ 3 * h0 ^ 2 - (2903040 : K[X]) * e1
      ^ 2 * w1 * f2 * h0 ^ 2 + (4976640 : K[X]) * e1 ^ 2 * a3 * h0 ^ 2 -
      (2580480 : K[X]) * e1 * w1 ^ 5 * h0 + (13547520 : K[X]) * e1 * w1 ^ 3
      * f2 * h0 - (42301440 : K[X]) * e1 * w1 ^ 2 * a3 * h0 - (8709120 :
      K[X]) * e1 * w1 * f2 ^ 2 * h0 + (44789760 : K[X]) * e1 * w1 * a2 * h0
      ^ 3 + (14929920 : K[X]) * e1 * f2 * a3 * h0 - (33592320 : K[X]) * e1 *
      a1 * h0 ^ 5 + (2488320 : K[X]) * w1 ^ 7 - (21288960 : K[X]) * w1 ^ 5 *
      f2 + (39813120 : K[X]) * w1 ^ 4 * a3 + (49351680 : K[X]) * w1 ^ 3 * f2
      ^ 2 - (59719680 : K[X]) * w1 ^ 3 * a2 * h0 ^ 2 - (141834240 : K[X]) *
      w1 ^ 2 * f2 * a3 + (100776960 : K[X]) * w1 ^ 2 * a1 * h0 ^ 4 -
      (26127360 : K[X]) * w1 * f2 ^ 3 + (134369280 : K[X]) * w1 * f2 * a2 *
      h0 ^ 2 + (134369280 : K[X]) * w1 * a3 ^ 2 - (201553920 : K[X]) * w1 *
      a0 * h0 ^ 6 + (44789760 : K[X]) * f2 ^ 2 * a3 - (100776960 : K[X]) *
      f2 * a1 * h0 ^ 4 - (201553920 : K[X]) * a3 * a2 * h0 ^ 2 -
      Polynomial.C ν₂ * ((108 : K[X]) * h0 ^ 7) + Polynomial.C κ₅ * ((1152 :
      K[X]) * w1 * h0 ^ 6) + Polynomial.C ν * ((2160 : K[X]) * e1 * h0 ^ 6)
      - Polynomial.C ν * ((5400 : K[X]) * w1 ^ 2 * h0 ^ 5) + Polynomial.C ν
      * ((6480 : K[X]) * f2 * h0 ^ 5) + Polynomial.C μ * ((20160 : K[X]) *
      e1 ^ 2 * h0 ^ 5) - Polynomial.C μ * ((126000 : K[X]) * e1 * w1 ^ 2 *
      h0 ^ 4) + Polynomial.C μ * ((60480 : K[X]) * e1 * f2 * h0 ^ 4) +
      Polynomial.C μ * ((89460 : K[X]) * w1 ^ 4 * h0 ^ 3) - Polynomial.C μ *
      ((438480 : K[X]) * w1 ^ 2 * f2 * h0 ^ 3) + Polynomial.C μ * ((1088640
      : K[X]) * w1 * a3 * h0 ^ 3) + Polynomial.C μ * ((181440 : K[X]) * f2 ^
      2 * h0 ^ 3) - Polynomial.C μ * ((1306368 : K[X]) * a2 * h0 ^ 5) +
      Polynomial.C κ * ((552960 : K[X]) * e1 ^ 2 * w1 * h0 ^ 4) -
      Polynomial.C κ * ((1105920 : K[X]) * e1 * w1 ^ 3 * h0 ^ 3) +
      Polynomial.C κ * ((1658880 : K[X]) * e1 * w1 * f2 * h0 ^ 3) -
      Polynomial.C κ * ((2985984 : K[X]) * e1 * a3 * h0 ^ 3) + Polynomial.C
      κ * ((774144 : K[X]) * w1 ^ 5 * h0 ^ 2) - Polynomial.C κ * ((4976640 :
      K[X]) * w1 ^ 3 * f2 * h0 ^ 2) + Polynomial.C κ * ((11943936 : K[X]) *
      w1 ^ 2 * a3 * h0 ^ 2) + Polynomial.C κ * ((4976640 : K[X]) * w1 * f2 ^
      2 * h0 ^ 2) - Polynomial.C κ * ((17915904 : K[X]) * w1 * a2 * h0 ^ 4)
      - Polynomial.C κ * ((8957952 : K[X]) * f2 * a3 * h0 ^ 2) +
      Polynomial.C κ * ((26873856 : K[X]) * a1 * h0 ^ 6))) * he1 +
      (-((184320 : K[X]) * e1 ^ 3 * h0 ^ 3 - (1382400 : K[X]) * e1 ^ 2 * w1
      ^ 2 * h0 ^ 2 + (184320 : K[X]) * e1 * e2 * w1 * h0 ^ 2 + (92160 :
      K[X]) * e1 * w1 ^ 4 * h0 + (4976640 : K[X]) * e1 * w1 * a3 * h0 -
      (7464960 : K[X]) * e1 * a2 * h0 ^ 3 - (5120 : K[X]) * e2 ^ 2 * h0 ^ 2
      - (40960 : K[X]) * e2 * w1 ^ 3 * h0 - (138240 : K[X]) * e2 * a3 * h0 +
      (40960 : K[X]) * w1 ^ 6 - (967680 : K[X]) * w1 ^ 3 * a3 + (7464960 :
      K[X]) * w1 ^ 2 * a2 * h0 ^ 2 - (22394880 : K[X]) * w1 * a1 * h0 ^ 4 -
      (3732480 : K[X]) * a3 ^ 2 + (67184640 : K[X]) * a0 * h0 ^ 6 -
      Polynomial.C κ₅ * ((384 : K[X]) * h0 ^ 6) + Polynomial.C ν * ((1440 :
      K[X]) * w1 * h0 ^ 5) + Polynomial.C μ * ((40320 : K[X]) * e1 * w1 * h0
      ^ 4) - Polynomial.C μ * ((2688 : K[X]) * e2 * h0 ^ 4) + Polynomial.C μ
      * ((672 : K[X]) * w1 ^ 3 * h0 ^ 3) - Polynomial.C μ * ((72576 : K[X])
      * a3 * h0 ^ 3) - Polynomial.C κ * ((110592 : K[X]) * e1 ^ 2 * h0 ^ 4)
      + Polynomial.C κ * ((331776 : K[X]) * e1 * w1 ^ 2 * h0 ^ 3) -
      Polynomial.C κ * ((36864 : K[X]) * e2 * w1 * h0 ^ 3) + Polynomial.C κ
      * ((36864 : K[X]) * w1 ^ 4 * h0 ^ 2) - Polynomial.C κ * ((995328 :
      K[X]) * w1 * a3 * h0 ^ 2) + Polynomial.C κ * ((2985984 : K[X]) * a2 *
      h0 ^ 4))) * he2 + (-(-((829440 : K[X]) * e1 ^ 2 * w1 * h0 ^ 3) +
      (184320 : K[X]) * e1 * e2 * h0 ^ 3 + (138240 : K[X]) * e1 * w1 ^ 3 *
      h0 ^ 2 - (46080 : K[X]) * e2 * w1 ^ 2 * h0 ^ 2 - (46080 : K[X]) * u2 *
      w1 * h0 ^ 3 + (7464960 : K[X]) * w1 * a2 * h0 ^ 3 - (22394880 : K[X])
      * a1 * h0 ^ 5 + Polynomial.C ν * ((1440 : K[X]) * h0 ^ 6) +
      Polynomial.C μ * ((40320 : K[X]) * e1 * h0 ^ 5) - Polynomial.C μ *
      ((2016 : K[X]) * w1 ^ 2 * h0 ^ 4) + Polynomial.C κ * ((221184 : K[X])
      * e1 * w1 * h0 ^ 4) - Polynomial.C κ * ((36864 : K[X]) * e2 * h0 ^
      4))) * hu2
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have hev1 := congrArg (fun t : K[X] => t.eval (-(d / c))) hu2
  simp only [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_ofNat] at hev1
  rw [hroot, zero_mul] at hev1
  have h1 : w1.eval (-(d / c)) *
      (e2.eval (-(d / c)) -
        3 * e1.eval (-(d / c)) * w1.eval (-(d / c))) = 0 := by
    linear_combination hev1
  have hevQ9 := congrArg (fun t : K[X] => t.eval (-(d / c))) hQ9
  simp only [alignedEighthSquareCombinedRow610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hevQ9
  rw [hroot] at hevQ9
  have h2 : 1280 * e1.eval (-(d / c)) *
      (3 * e1.eval (-(d / c)) * w1.eval (-(d / c)) -
        e2.eval (-(d / c))) *
      (6 * e1.eval (-(d / c)) * w1.eval (-(d / c)) -
        e2.eval (-(d / c))) +
      189 * μ * w1.eval (-(d / c)) ^ 5 = 0 := by
    linear_combination -hevQ9
  have hevR9 := congrArg (fun t : K[X] => t.eval (-(d / c))) hR9
  simp only [Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_neg, Polynomial.eval_ofNat] at hevR9
  rw [hroot] at hevR9
  have h9 : 276480 * e1.eval (-(d / c)) ^ 3 * w1.eval (-(d / c)) ^ 3 -
      5120 * e2.eval (-(d / c)) ^ 3 -
      189 * μ * w1.eval (-(d / c)) ^ 6 = 0 := by
    linear_combination hevR9
  obtain ⟨hv0, _hbranch⟩ := alignedNinthSquareResolve_610 h1 h2 h9
  obtain ⟨e3, he3⟩ := linearPolynomial_dvd_of_eval_eq_zero_810 h0 e2
    (-(d / c)) hdeg1 hroot hv0
  refine ⟨e3, he3, ?_, ?_⟩
  · rw [he2, he3]
    ring
  · simp only [alignedNinthSquarePeeledRow610]
    linear_combination hR9

end Max11DegreeRoutes
