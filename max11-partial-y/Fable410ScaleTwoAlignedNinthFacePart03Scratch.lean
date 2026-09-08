import Fable410ScaleTwoAlignedFlatDefectPart08Scratch

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
set_option maxHeartbeats 64000000 in
/-- Exact combination of the degree-`3` Jacobian expression with the
weight-`15` bracket of `M₁₆`.  The only corrections are the consumed
degree-`10` through degree-`4` brackets of `M₂`, `M₄`, `M₆`, `M₈`,
`M₁₀`, `M₁₂`, and `M₁₄`: neither the aligned-face residual `N` nor the
degree-`11` relation `R` appears at all — the correction module is
empty for the fourth row in a row.  Every correction vanishes on the
aligned face. -/
theorem alignedTenthDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (1048576 : K[X]) * H ^ 14 *
        (a3.derivative * b1 +
          a2.derivative * (b2 * (2 : K[X])) +
          a1.derivative * (b3 * (3 : K[X])) +
          a0.derivative * (b4 * (4 : K[X])) -
        ((H ^ 2 * (4 : K[X])) * b0.derivative +
          (a3 * (3 : K[X])) * b1.derivative +
          (a2 * (2 : K[X])) * b2.derivative +
          a1 * b3.derivative)) =
      (H *
          (alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7
            κ).derivative -
        (15 : K[X]) *
          alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 κ *
          H.derivative) +
        (2 : K[X]) * a3 *
          ((2 : K[X]) * H *
              (alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
                κ).derivative -
            (27 : K[X]) *
              alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((8 : K[X]) * a3 ^ 2 + (32 : K[X]) * a2 * H ^ 2) *
          (H * (alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7
              κ).derivative -
            (12 : K[X]) *
              alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((64 : K[X]) * a1 * H ^ 4 + (48 : K[X]) * a2 * a3 * H ^ 2 -
            (2 : K[X]) * a3 ^ 3) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) *
              alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((2048 : K[X]) * a0 * H ^ 6 + (2048 : K[X]) * a1 * a3 * H ^ 4 +
            (1024 : K[X]) * a2 ^ 2 * H ^ 4) *
          (H * (alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7
              κ).derivative -
            (9 : K[X]) * alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((5120 : K[X]) * a0 * a3 * H ^ 6 + (5120 : K[X]) * a1 * a2 * H ^ 6 +
            (640 : K[X]) * a1 * a3 ^ 2 * H ^ 4 +
            (640 : K[X]) * a2 ^ 2 * a3 * H ^ 4 -
            (160 : K[X]) * a2 * a3 ^ 3 * H ^ 2 + (14 : K[X]) * a3 ^ 5) *
          ((2 : K[X]) * H *
              (alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ).derivative -
            (15 : K[X]) * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ *
              H.derivative) +
        ((49152 : K[X]) * a0 * a2 * H ^ 8 + (24576 : K[X]) * a1 ^ 2 * H ^ 8 +
            (12288 : K[X]) * a0 * a3 ^ 2 * H ^ 6 +
            (24576 : K[X]) * a1 * a2 * a3 * H ^ 6 +
            (4096 : K[X]) * a2 ^ 3 * H ^ 6 -
            (2048 : K[X]) * a1 * a3 ^ 3 * H ^ 4 -
            (3072 : K[X]) * a2 ^ 2 * a3 ^ 2 * H ^ 4 +
            (768 : K[X]) * a2 * a3 ^ 4 * H ^ 2 - (64 : K[X]) * a3 ^ 6) *
          (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
            (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
              H.derivative) +
        ((229376 : K[X]) * a0 * a1 * H ^ 10 +
            (172032 : K[X]) * a0 * a2 * a3 * H ^ 8 +
            (86016 : K[X]) * a1 ^ 2 * a3 * H ^ 8 +
            (86016 : K[X]) * a1 * a2 ^ 2 * H ^ 8 -
            (7168 : K[X]) * a0 * a3 ^ 3 * H ^ 6 -
            (21504 : K[X]) * a1 * a2 * a3 ^ 2 * H ^ 6 -
            (7168 : K[X]) * a2 ^ 3 * a3 * H ^ 6 +
            (2240 : K[X]) * a1 * a3 ^ 4 * H ^ 4 +
            (4480 : K[X]) * a2 ^ 2 * a3 ^ 3 * H ^ 4 -
            (1008 : K[X]) * a2 * a3 ^ 5 * H ^ 2 + (78 : K[X]) * a3 ^ 7) *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) *
              alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) := by
  simp only [memory410_flatTenthDefect, memory410_flatNinthDefect, memory410_flatEighthDefect,
    memory410_flatSeventhDefect, memory410_flatSixthDefect, memory410_flatFifthDefect,
    memory410_flatFourthDefect, memory410_flatThirdDefect,
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
