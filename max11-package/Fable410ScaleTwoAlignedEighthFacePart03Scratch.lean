import Fable410ScaleTwoAlignedFlatDefectPart07Scratch

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
set_option maxHeartbeats 64000000 in
/-- Exact combination of the degree-`4` Jacobian expression with the
weight-`27/2` bracket of `M₁₄`.  The only corrections are the consumed
degree-`10` through degree-`5` brackets of `M₂`, `M₄`, `M₆`, `M₈`,
`M₁₀`, and `M₁₂`: neither the aligned-face residual `N` nor the
degree-`11` relation `R` appears at all — the correction module is
empty for the third row in a row.  Every correction vanishes on the
aligned face. -/
theorem alignedNinthDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (524288 : K[X]) * H ^ 12 *
        ((H ^ 2).derivative * b1 +
          a3.derivative * (b2 * (2 : K[X])) +
          a2.derivative * (b3 * (3 : K[X])) +
          a1.derivative * (b4 * (4 : K[X])) +
          a0.derivative * (b5 * (5 : K[X])) -
        ((H ^ 2 * (4 : K[X])) * b1.derivative +
          (a3 * (3 : K[X])) * b2.derivative +
          (a2 * (2 : K[X])) * b3.derivative +
          a1 * b4.derivative)) =
      ((2 : K[X]) * H *
          (alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
            κ).derivative -
        (27 : K[X]) *
          alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
          H.derivative) +
        (20 : K[X]) * a3 *
          (H * (alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7
              κ).derivative -
            (12 : K[X]) *
              alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((40 : K[X]) * a2 * H ^ 2 + (15 : K[X]) * a3 ^ 2) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) *
              alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((1280 : K[X]) * a1 * H ^ 4 + (1280 : K[X]) * a2 * a3 * H ^ 2) *
          (H * (alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7
              κ).derivative -
            (9 : K[X]) * alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((2560 : K[X]) * a0 * H ^ 6 + (3200 : K[X]) * a1 * a3 * H ^ 4 +
            (1600 : K[X]) * a2 ^ 2 * H ^ 4 +
            (400 : K[X]) * a2 * a3 ^ 2 * H ^ 2 -
            (25 : K[X]) * a3 ^ 4) *
          ((2 : K[X]) * H *
              (alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ).derivative -
            (15 : K[X]) * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ *
              H.derivative) +
        ((30720 : K[X]) * a0 * a3 * H ^ 6 + (30720 : K[X]) * a1 * a2 * H ^ 6 +
            (7680 : K[X]) * a1 * a3 ^ 2 * H ^ 4 +
            (7680 : K[X]) * a2 ^ 2 * a3 * H ^ 4 -
            (1280 : K[X]) * a2 * a3 ^ 3 * H ^ 2 + (96 : K[X]) * a3 ^ 5) *
          (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
            (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
              H.derivative) +
        ((143360 : K[X]) * a0 * a2 * H ^ 8 + (71680 : K[X]) * a1 ^ 2 * H ^ 8 +
            (53760 : K[X]) * a0 * a3 ^ 2 * H ^ 6 +
            (107520 : K[X]) * a1 * a2 * a3 * H ^ 6 +
            (17920 : K[X]) * a2 ^ 3 * H ^ 6 -
            (4480 : K[X]) * a1 * a3 ^ 3 * H ^ 4 -
            (6720 : K[X]) * a2 ^ 2 * a3 ^ 2 * H ^ 4 +
            (1400 : K[X]) * a2 * a3 ^ 4 * H ^ 2 -
            (105 : K[X]) * a3 ^ 6) *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) * alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) := by
  simp only [memory410_flatNinthDefect, memory410_flatEighthDefect, memory410_flatSeventhDefect,
    memory410_flatSixthDefect, memory410_flatFifthDefect, memory410_flatFourthDefect,
    memory410_flatThirdDefect,
    Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left,
    Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons,
    Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right,
    pow_zero, pow_one, one_mul, mul_one,
    Polynomial.derivative_neg, Polynomial.derivative_zero,
    Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_ofNat, Polynomial.derivative_C, nsmul_eq_mul,
    zero_mul, mul_zero, zero_add, add_zero, neg_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_neg, Polynomial.eval_zero, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

end Max11DegreeRoutes
