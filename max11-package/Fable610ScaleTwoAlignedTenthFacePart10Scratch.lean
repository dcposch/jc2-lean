import Fable610ScaleTwoAlignedTenthFacePart02Scratch
import Fable610ScaleTwoAlignedTenthFacePart09Scratch

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
