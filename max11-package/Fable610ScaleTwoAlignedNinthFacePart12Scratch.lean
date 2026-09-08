import Fable610ScaleTwoAlignedNinthFacePart02Scratch
import Fable610ScaleTwoAlignedNinthFacePart11Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 6400000000 in
/-- Descent of the consumed degree-`6` row in the nonsquare chamber:
the `H¹⁸`-peeled core (the ninth defect vanishes identically) absorbs
the nonic head through the seventh-face divisibilities, peeling `H²`
onto the head `-46080 g₁ (81 p₂ + 3 g₁² t₁ - g₁ t₂)²` — the CARRIED
eighth-face `p₂` divisor squared — so substituting `u` peels one more
`H` onto the cubic head `-5120 (t₂ - 6 g₁ t₁)³`, which vanishes at
BOTH simple roots and transfers to the NEW divisibility
`t₂ - 6 g₁ t₁ = H t₃`; substituting `t₃` peels the last `H` and
solves `q₁` OUTRIGHT. -/
theorem alignedNonsquareNinth_descent_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H g1 f t1 t2 u a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : k[X]}
    {κ κ₃ κ₅ κ₇ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
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
    (ht1 : (3 : k[X]) * f - g1 ^ 2 = H * t1)
    (ht2 : (27 : k[X]) * a3 - g1 ^ 3 = H * t2)
    (hu : (81 : k[X]) * a2 + (3 : k[X]) * g1 ^ 2 * t1 - g1 * t2 =
      H * u) :
    ∃ t3 : k[X],
      t2 - (6 : k[X]) * g1 * t1 = H * t3 ∧
      (1632586752 : k[X]) * b1 =
        alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1
          κ κ₃ κ₅ κ₇ := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hL' := hL0
  simp only [alignedNinthDefect610] at hL'
  rw [hD0, hE, hF0, hG, hI0, hJ, hg1, hf] at hL'
  have hcore :
      (-((78382080 : k[X]) * f ^ 4 * g1) + (134369280 : k[X]) * f ^ 3 * a3 +
        (174182400 : k[X]) * f ^ 3 * g1 ^ 3 - (470292480 : k[X]) * f ^ 2 *
        a3 * g1 ^ 2 - (113218560 : k[X]) * f ^ 2 * g1 ^ 5 + (403107840 :
        k[X]) * f * a3 ^ 2 * g1 + (261273600 : k[X]) * f * a3 * g1 ^ 4 +
        (28753920 : k[X]) * f * g1 ^ 7 - (100776960 : k[X]) * a3 ^ 3 -
        (156764160 : k[X]) * a3 ^ 2 * g1 ^ 3 - (37739520 : k[X]) * a3 * g1 ^
        6 - (2529280 : k[X]) * g1 ^ 9) + H * ((403107840 : k[X]) * f ^ 2 *
        g1 * a2 - (604661760 : k[X]) * f * a3 * a2 - (313528320 : k[X]) * f
        * g1 ^ 3 * a2 + (403107840 : k[X]) * a3 * g1 ^ 2 * a2 + (52254720 :
        k[X]) * g1 ^ 5 * a2 + Polynomial.C κ * ((14929920 : k[X]) * f ^ 3 *
        g1) - Polynomial.C κ * ((26873856 : k[X]) * f ^ 2 * a3) -
        Polynomial.C κ * ((19906560 : k[X]) * f ^ 2 * g1 ^ 3) + Polynomial.C
        κ * ((44789760 : k[X]) * f * a3 * g1 ^ 2) + Polynomial.C κ *
        ((7299072 : k[X]) * f * g1 ^ 5) - Polynomial.C κ * ((26873856 :
        k[X]) * a3 ^ 2 * g1) - Polynomial.C κ * ((9953280 : k[X]) * a3 * g1
        ^ 4) - Polynomial.C κ * ((811008 : k[X]) * g1 ^ 7)) + H ^ 2 *
        (-((302330880 : k[X]) * f ^ 2 * a1) + (403107840 : k[X]) * f * g1 ^
        2 * a1 - (604661760 : k[X]) * a3 * g1 * a1 - (78382080 : k[X]) * g1
        ^ 4 * a1 - (302330880 : k[X]) * g1 * a2 ^ 2 - Polynomial.C κ *
        ((53747712 : k[X]) * f * g1 * a2) + Polynomial.C κ * ((80621568 :
        k[X]) * a3 * a2) + Polynomial.C κ * ((14929920 : k[X]) * g1 ^ 3 *
        a2)) + H ^ 3 * (-((604661760 : k[X]) * f * g1 * a0) + (1813985280 :
        k[X]) * a3 * a0 + (134369280 : k[X]) * g1 ^ 3 * a0 + (1813985280 :
        k[X]) * a1 * a2 + Polynomial.C κ₅ * ((3456 : k[X]) * f * g1) -
        Polynomial.C κ₅ * ((10368 : k[X]) * a3) - Polynomial.C κ₅ * ((768 :
        k[X]) * g1 ^ 3) + Polynomial.C κ * ((80621568 : k[X]) * f * a1) -
        Polynomial.C κ * ((26873856 : k[X]) * g1 ^ 2 * a1)) + H ^ 4 *
        (-((1632586752 : k[X]) * b1) - Polynomial.C κ₇ * ((36 : k[X]) * g1)
        - Polynomial.C κ₃ * ((3359232 : k[X]) * a1) + Polynomial.C κ *
        ((80621568 : k[X]) * g1 * a0)) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 18 hH)
    linear_combination hL'
  have hR2 :
      (-((414720 : k[X]) * t1 ^ 2 * g1 ^ 5) + (276480 : k[X]) * t1 * t2 * g1
        ^ 4 - (22394880 : k[X]) * t1 * g1 ^ 3 * a2 - (46080 : k[X]) * t2 ^ 2
        * g1 ^ 3 + (7464960 : k[X]) * t2 * g1 ^ 2 * a2 - (302330880 : k[X])
        * g1 * a2 ^ 2) + H * ((2764800 : k[X]) * t1 ^ 3 * g1 ^ 3 - (1382400
        : k[X]) * t1 ^ 2 * t2 * g1 ^ 2 + (44789760 : k[X]) * t1 ^ 2 * g1 *
        a2 + (184320 : k[X]) * t1 * t2 ^ 2 * g1 - (7464960 : k[X]) * t1 * t2
        * a2 + (67184640 : k[X]) * t1 * g1 ^ 2 * a1 - (5120 : k[X]) * t2 ^ 3
        - (22394880 : k[X]) * t2 * g1 * a1 + (1813985280 : k[X]) * a1 * a2 -
        Polynomial.C κ * ((663552 : k[X]) * t1 ^ 2 * g1 ^ 3) + Polynomial.C
        κ * ((331776 : k[X]) * t1 * t2 * g1 ^ 2) - Polynomial.C κ *
        ((17915904 : k[X]) * t1 * g1 * a2) - Polynomial.C κ * ((36864 :
        k[X]) * t2 ^ 2 * g1) + Polynomial.C κ * ((2985984 : k[X]) * t2 *
        a2)) + H ^ 2 * (-((967680 : k[X]) * t1 ^ 4 * g1) + (184320 : k[X]) *
        t1 ^ 3 * t2 - (33592320 : k[X]) * t1 ^ 2 * a1 - (201553920 : k[X]) *
        t1 * g1 * a0 + (67184640 : k[X]) * t2 * a0 - (1632586752 : k[X]) *
        b1 - Polynomial.C κ₇ * ((36 : k[X]) * g1) + Polynomial.C κ₅ * ((1152
        : k[X]) * t1 * g1) - Polynomial.C κ₅ * ((384 : k[X]) * t2) -
        Polynomial.C κ₃ * ((3359232 : k[X]) * a1) + Polynomial.C κ *
        ((552960 : k[X]) * t1 ^ 3 * g1) - Polynomial.C κ * ((110592 : k[X])
        * t1 ^ 2 * t2) + Polynomial.C κ * ((26873856 : k[X]) * t1 * a1) +
        Polynomial.C κ * ((80621568 : k[X]) * g1 * a0)) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    linear_combination hcore + (-(-((967680 : k[X]) * t1 ^ 3 * g1 * H ^ 3) +
      (3548160 : k[X]) * t1 ^ 2 * g1 ^ 3 * H ^ 2 - (2903040 : k[X]) * t1 ^ 2
      * g1 * f * H ^ 2 + (4976640 : k[X]) * t1 ^ 2 * a3 * H ^ 2 - (2580480 :
      k[X]) * t1 * g1 ^ 5 * H + (13547520 : k[X]) * t1 * g1 ^ 3 * f * H -
      (42301440 : k[X]) * t1 * g1 ^ 2 * a3 * H - (8709120 : k[X]) * t1 * g1
      * f ^ 2 * H + (44789760 : k[X]) * t1 * g1 * a2 * H ^ 2 + (14929920 :
      k[X]) * t1 * f * a3 * H - (33592320 : k[X]) * t1 * a1 * H ^ 3 +
      (2488320 : k[X]) * g1 ^ 7 - (21288960 : k[X]) * g1 ^ 5 * f + (39813120
      : k[X]) * g1 ^ 4 * a3 + (49351680 : k[X]) * g1 ^ 3 * f ^ 2 - (59719680
      : k[X]) * g1 ^ 3 * a2 * H - (141834240 : k[X]) * g1 ^ 2 * f * a3 +
      (100776960 : k[X]) * g1 ^ 2 * a1 * H ^ 2 - (26127360 : k[X]) * g1 * f
      ^ 3 + (134369280 : k[X]) * g1 * f * a2 * H + (134369280 : k[X]) * g1 *
      a3 ^ 2 - (201553920 : k[X]) * g1 * a0 * H ^ 3 + (44789760 : k[X]) * f
      ^ 2 * a3 - (100776960 : k[X]) * f * a1 * H ^ 2 - (201553920 : k[X]) *
      a3 * a2 * H + Polynomial.C κ₅ * ((1152 : k[X]) * g1 * H ^ 3) +
      Polynomial.C κ * ((552960 : k[X]) * t1 ^ 2 * g1 * H ^ 3) -
      Polynomial.C κ * ((1105920 : k[X]) * t1 * g1 ^ 3 * H ^ 2) +
      Polynomial.C κ * ((1658880 : k[X]) * t1 * g1 * f * H ^ 2) -
      Polynomial.C κ * ((2985984 : k[X]) * t1 * a3 * H ^ 2) + Polynomial.C κ
      * ((774144 : k[X]) * g1 ^ 5 * H) - Polynomial.C κ * ((4976640 : k[X])
      * g1 ^ 3 * f * H) + Polynomial.C κ * ((11943936 : k[X]) * g1 ^ 2 * a3
      * H) + Polynomial.C κ * ((4976640 : k[X]) * g1 * f ^ 2 * H) -
      Polynomial.C κ * ((17915904 : k[X]) * g1 * a2 * H ^ 2) - Polynomial.C
      κ * ((8957952 : k[X]) * f * a3 * H) + Polynomial.C κ * ((26873856 :
      k[X]) * a1 * H ^ 3))) * ht1 + (-((184320 : k[X]) * t1 ^ 3 * H ^ 3 -
      (1382400 : k[X]) * t1 ^ 2 * g1 ^ 2 * H ^ 2 + (184320 : k[X]) * t1 * t2
      * g1 * H ^ 2 + (92160 : k[X]) * t1 * g1 ^ 4 * H + (4976640 : k[X]) *
      t1 * g1 * a3 * H - (7464960 : k[X]) * t1 * a2 * H ^ 2 - (5120 : k[X])
      * t2 ^ 2 * H ^ 2 - (40960 : k[X]) * t2 * g1 ^ 3 * H - (138240 : k[X])
      * t2 * a3 * H + (40960 : k[X]) * g1 ^ 6 - (967680 : k[X]) * g1 ^ 3 *
      a3 + (7464960 : k[X]) * g1 ^ 2 * a2 * H - (22394880 : k[X]) * g1 * a1
      * H ^ 2 - (3732480 : k[X]) * a3 ^ 2 + (67184640 : k[X]) * a0 * H ^ 3 -
      Polynomial.C κ₅ * ((384 : k[X]) * H ^ 3) - Polynomial.C κ * ((110592 :
      k[X]) * t1 ^ 2 * H ^ 3) + Polynomial.C κ * ((331776 : k[X]) * t1 * g1
      ^ 2 * H ^ 2) - Polynomial.C κ * ((36864 : k[X]) * t2 * g1 * H ^ 2) +
      Polynomial.C κ * ((36864 : k[X]) * g1 ^ 4 * H) - Polynomial.C κ *
      ((995328 : k[X]) * g1 * a3 * H) + Polynomial.C κ * ((2985984 : k[X]) *
      a2 * H ^ 2))) * ht2
  have hR3 :
      ((1105920 : k[X]) * t1 ^ 3 * g1 ^ 3 - (552960 : k[X]) * t1 ^ 2 * t2 *
        g1 ^ 2 + (92160 : k[X]) * t1 * t2 ^ 2 * g1 - (5120 : k[X]) * t2 ^ 3)
        + H * (-((967680 : k[X]) * t1 ^ 4 * g1) + (184320 : k[X]) * t1 ^ 3 *
        t2 + (552960 : k[X]) * t1 ^ 2 * u * g1 - (33592320 : k[X]) * t1 ^ 2
        * a1 - (92160 : k[X]) * t1 * t2 * u - (201553920 : k[X]) * t1 * g1 *
        a0 + (67184640 : k[X]) * t2 * a0 - (46080 : k[X]) * u ^ 2 * g1 +
        (22394880 : k[X]) * u * a1 - (1632586752 : k[X]) * b1 - Polynomial.C
        κ₇ * ((36 : k[X]) * g1) + Polynomial.C κ₅ * ((1152 : k[X]) * t1 *
        g1) - Polynomial.C κ₅ * ((384 : k[X]) * t2) - Polynomial.C κ₃ *
        ((3359232 : k[X]) * a1) + Polynomial.C κ * ((552960 : k[X]) * t1 ^ 3
        * g1) - Polynomial.C κ * ((110592 : k[X]) * t1 ^ 2 * t2) -
        Polynomial.C κ * ((221184 : k[X]) * t1 * u * g1) + Polynomial.C κ *
        ((26873856 : k[X]) * t1 * a1) + Polynomial.C κ * ((36864 : k[X]) *
        t2 * u) + Polynomial.C κ * ((80621568 : k[X]) * g1 * a0)) = 0 := by
    apply mul_left_cancel₀ hH
    linear_combination hR2 + (-((552960 : k[X]) * t1 ^ 2 * g1 * H - (92160 :
      k[X]) * t1 * t2 * H - (138240 : k[X]) * t1 * g1 ^ 3 + (46080 : k[X]) *
      t2 * g1 ^ 2 - (46080 : k[X]) * u * g1 * H - (3732480 : k[X]) * g1 * a2
      + (22394880 : k[X]) * a1 * H - Polynomial.C κ * ((221184 : k[X]) * t1
      * g1 * H) + Polynomial.C κ * ((36864 : k[X]) * t2 * H))) * hu
  have hkey : ∀ a : k, H.eval a = 0 →
      (t2 - (6 : k[X]) * g1 * t1).eval a = 0 := by
    intro a ha
    have hev := congrArg (fun t : k[X] => t.eval a) hR3
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_ofNat, Polynomial.eval_zero] at hev
    rw [ha] at hev
    have hcube : ((t2 - (6 : k[X]) * g1 * t1).eval a) ^ 3 = 0 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat]
      linear_combination (-(5120 : k)⁻¹) * hev
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hcube
  obtain ⟨t3, ht3⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hkey
  have hq1 :
      (1632586752 : k[X]) * b1 =
        (-((967680 : k[X]) * t1 ^ 4 * g1) + (184320 : k[X]) * t1 ^ 3 * t2 +
          (552960 : k[X]) * t1 ^ 2 * u * g1 - (33592320 : k[X]) * t1 ^ 2 *
          a1 - (92160 : k[X]) * t1 * t2 * u - (201553920 : k[X]) * t1 * g1 *
          a0 + (67184640 : k[X]) * t2 * a0 - (46080 : k[X]) * u ^ 2 * g1 +
          (22394880 : k[X]) * u * a1 - Polynomial.C κ₇ * ((36 : k[X]) * g1)
          + Polynomial.C κ₅ * ((1152 : k[X]) * t1 * g1) - Polynomial.C κ₅ *
          ((384 : k[X]) * t2) - Polynomial.C κ₃ * ((3359232 : k[X]) * a1) +
          Polynomial.C κ * ((552960 : k[X]) * t1 ^ 3 * g1) - Polynomial.C κ
          * ((110592 : k[X]) * t1 ^ 2 * t2) - Polynomial.C κ * ((221184 :
          k[X]) * t1 * u * g1) + Polynomial.C κ * ((26873856 : k[X]) * t1 *
          a1) + Polynomial.C κ * ((36864 : k[X]) * t2 * u) + Polynomial.C κ
          * ((80621568 : k[X]) * g1 * a0)) + H ^ 2 * (-((5120 : k[X]) * t3 ^
          3)) := by
    apply mul_left_cancel₀ hH
    linear_combination -hR3 + (-((184320 : k[X]) * t1 ^ 2 * g1 ^ 2) + (61440
      : k[X]) * t1 * t2 * g1 + (30720 : k[X]) * t1 * t3 * g1 * H - (5120 :
      k[X]) * t2 ^ 2 - (5120 : k[X]) * t2 * t3 * H - (5120 : k[X]) * t3 ^ 2
      * H ^ 2) * ht3
  refine ⟨t3, ht3, ?_⟩
  simp only [alignedNinthNonsquareSolved610]
  linear_combination hq1

end Max11DegreeRoutes
