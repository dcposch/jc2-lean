import Fable410ScaleTwoAlignedFlatDefectPart10Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory410_flatThirdDefect from Fable410ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory410_flatFourthDefect from Fable410ScaleTwoAlignedFlatDefectPart02Scratch in
open private memory410_flatFifthDefect from Fable410ScaleTwoAlignedFlatDefectPart03Scratch in
open private memory410_flatSixthDefect from Fable410ScaleTwoAlignedFlatDefectPart04Scratch in
open private memory410_flatSeventhDefect from Fable410ScaleTwoAlignedFlatDefectPart05Scratch in
open private memory410_flatEighthDefect from Fable410ScaleTwoAlignedFlatDefectPart06Scratch in
open private memory410_flatNinthDefect from Fable410ScaleTwoAlignedFlatDefectPart07Scratch in
open private memory410_flatTenthDefect from Fable410ScaleTwoAlignedFlatDefectPart08Scratch in
open private memory410_flatEleventhDefect from Fable410ScaleTwoAlignedFlatDefectPart09Scratch in
open private memory410_flatTwelfthDefect from Fable410ScaleTwoAlignedFlatDefectPart10Scratch in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- Exact combination of the degree-`1` Jacobian expression with the
weight-`18` bracket of `M₂₀`.  The corrections are the consumed
degree-`10` through degree-`2` brackets of `M₂` through `M₁₈`: neither
the aligned-face residual `N` nor the degree-`11` relation `R`
appears — the correction module is empty for the sixth row in a row —
and the `M₁₆` bracket carries the row's entire `q₀'`-content with
cofactor `320 p₂ H²`.  Every correction vanishes on the aligned
face. -/
theorem alignedTwelfthDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (671088640 : K[X]) * H ^ 18 *
        (a1.derivative * b1 +
          a0.derivative * (b2 * (2 : K[X])) -
        ((a2 * (2 : K[X])) * b0.derivative +
          a1 * b1.derivative)) =
      (H * (alignedTwelfthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
          κ).derivative -
        (18 : K[X]) *
          alignedTwelfthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
          H.derivative) +
        ((5 : K[X]) * a3) *
          ((2 : K[X]) * H *
              (alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
                κ).derivative -
            (33 : K[X]) *
              alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((320 : K[X]) * H ^ 2 * a2) *
          (H * (alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6
              b7 κ).derivative -
            (15 : K[X]) *
              alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7
                κ * H.derivative) +
        ((640 : K[X]) * H ^ 4 * a1 +
            (160 : K[X]) * H ^ 2 * a2 * a3 -
            (20 : K[X]) * a3 ^ 3) *
          ((2 : K[X]) * H *
              (alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
                κ).derivative -
            (27 : K[X]) *
              alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((10240 : K[X]) * H ^ 6 * a0 +
            (2560 : K[X]) * H ^ 4 * a2 ^ 2 +
            (5120 : K[X]) * H ^ 4 * a1 * a3 -
            (1280 : K[X]) * H ^ 2 * a2 * a3 ^ 2 +
            (160 : K[X]) * a3 ^ 4) *
          (H * (alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7
              κ).derivative -
            (12 : K[X]) *
              alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((15360 : K[X]) * H ^ 6 * a1 * a2 +
            (15360 : K[X]) * H ^ 6 * a0 * a3 -
            (1920 : K[X]) * H ^ 4 * a2 ^ 2 * a3 -
            (1920 : K[X]) * H ^ 4 * a1 * a3 ^ 2 +
            (800 : K[X]) * H ^ 2 * a2 * a3 ^ 3 -
            (90 : K[X]) * a3 ^ 5) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) *
              alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((327680 : K[X]) * H ^ 8 * a1 ^ 2 +
            (655360 : K[X]) * H ^ 8 * a0 * a2) *
          (H * (alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6
              b7 κ).derivative -
            (9 : K[X]) * alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((1638400 : K[X]) * H ^ 10 * a0 * a1 +
            (204800 : K[X]) * H ^ 8 * a1 * a2 ^ 2 +
            (204800 : K[X]) * H ^ 8 * a1 ^ 2 * a3 +
            (409600 : K[X]) * H ^ 8 * a0 * a2 * a3 -
            (51200 : K[X]) * H ^ 6 * a2 ^ 3 * a3 -
            (153600 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 2 -
            (51200 : K[X]) * H ^ 6 * a0 * a3 ^ 3 +
            (44800 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 3 +
            (22400 : K[X]) * H ^ 4 * a1 * a3 ^ 4 -
            (12320 : K[X]) * H ^ 2 * a2 * a3 ^ 5 +
            (1100 : K[X]) * a3 ^ 7) *
          ((2 : K[X]) * H *
              (alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ).derivative -
            (15 : K[X]) * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ *
              H.derivative) +
        ((7864320 : K[X]) * H ^ 12 * a0 ^ 2 +
            (3932160 : K[X]) * H ^ 10 * a1 ^ 2 * a2 +
            (3932160 : K[X]) * H ^ 10 * a0 * a2 ^ 2 +
            (7864320 : K[X]) * H ^ 10 * a0 * a1 * a3 -
            (163840 : K[X]) * H ^ 8 * a2 ^ 4 -
            (1966080 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 -
            (983040 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 2 -
            (1966080 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 2 +
            (491520 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 2 +
            (983040 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 3 +
            (245760 : K[X]) * H ^ 6 * a0 * a3 ^ 4 -
            (307200 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 4 -
            (122880 : K[X]) * H ^ 4 * a1 * a3 ^ 5 +
            (71680 : K[X]) * H ^ 2 * a2 * a3 ^ 6 -
            (5760 : K[X]) * a3 ^ 8) *
          (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
            (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
              H.derivative) +
        ((9175040 : K[X]) * H ^ 12 * a1 ^ 3 +
            (55050240 : K[X]) * H ^ 12 * a0 * a1 * a2 +
            (27525120 : K[X]) * H ^ 12 * a0 ^ 2 * a3 -
            (2293760 : K[X]) * H ^ 10 * a1 * a2 ^ 3 -
            (6881280 : K[X]) * H ^ 10 * a1 ^ 2 * a2 * a3 -
            (6881280 : K[X]) * H ^ 10 * a0 * a2 ^ 2 * a3 -
            (6881280 : K[X]) * H ^ 10 * a0 * a1 * a3 ^ 2 +
            (716800 : K[X]) * H ^ 8 * a2 ^ 4 * a3 +
            (4300800 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 ^ 2 +
            (1433600 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 3 +
            (2867200 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 3 -
            (1075200 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 3 -
            (1612800 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 4 -
            (322560 : K[X]) * H ^ 6 * a0 * a3 ^ 5 +
            (524160 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 5 +
            (174720 : K[X]) * H ^ 4 * a1 * a3 ^ 6 -
            (106080 : K[X]) * H ^ 2 * a2 * a3 ^ 7 +
            (7735 : K[X]) * a3 ^ 9) *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) *
              alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) := by
  simp only [memory410_flatTwelfthDefect, memory410_flatEleventhDefect, memory410_flatTenthDefect, memory410_flatNinthDefect, memory410_flatEighthDefect, memory410_flatSeventhDefect, memory410_flatSixthDefect, memory410_flatFifthDefect, memory410_flatFourthDefect, memory410_flatThirdDefect,
    Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left,
    Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons,
    Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right,
    pow_zero, pow_one, one_mul, mul_one,
    Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_neg,
    Polynomial.derivative_ofNat, Polynomial.derivative_C, nsmul_eq_mul,
    zero_mul, mul_zero, zero_add, add_zero, neg_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat, Polynomial.eval_zero]
  ring

end Max11DegreeRoutes
