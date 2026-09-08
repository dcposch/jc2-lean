import Fable410ScaleTwoAlignedFlatDefectPart09Scratch

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
set_option maxHeartbeats 64000000 in
/-- Exact combination of the degree-`2` Jacobian expression with the
weight-`33/2` bracket of `M₁₈`.  The corrections are the consumed
degree-`10` through degree-`3` brackets of `M₂` through `M₁₆`: neither
the aligned-face residual `N` nor the degree-`11` relation `R`
appears — the correction module is empty for the fifth row in a row —
and the `M₁₆` bracket carries the row's entire `q₀'`-content with
cofactor `48 p₃`.  Every correction vanishes on the aligned face. -/
theorem alignedEleventhDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (67108864 : K[X]) * H ^ 16 *
        (a2.derivative * b1 +
          a1.derivative * (b2 * (2 : K[X])) +
          a0.derivative * (b3 * (3 : K[X])) -
        ((a3 * (3 : K[X])) * b0.derivative +
          (a2 * (2 : K[X])) * b1.derivative +
          a1 * b2.derivative)) =
      ((2 : K[X]) * H *
          (alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
            κ).derivative -
        (33 : K[X]) *
          alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
          H.derivative) +
        (48 : K[X]) * a3 *
          (H * (alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6
              b7 κ).derivative -
            (15 : K[X]) *
              alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7
                κ * H.derivative) +
        ((96 : K[X]) * H ^ 2 * a2 + (12 : K[X]) * a3 ^ 2) *
          ((2 : K[X]) * H *
              (alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
                κ).derivative -
            (27 : K[X]) *
              alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((1536 : K[X]) * H ^ 4 * a1 + (768 : K[X]) * H ^ 2 * a2 * a3 -
            (64 : K[X]) * a3 ^ 3) *
          (H * (alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7
              κ).derivative -
            (12 : K[X]) *
              alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((3072 : K[X]) * H ^ 6 * a0 + (1152 : K[X]) * H ^ 4 * a2 ^ 2 +
            (2304 : K[X]) * H ^ 4 * a1 * a3 -
            (288 : K[X]) * H ^ 2 * a2 * a3 ^ 2 + (30 : K[X]) * a3 ^ 4) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) *
              alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((98304 : K[X]) * H ^ 6 * a1 * a2 +
            (98304 : K[X]) * H ^ 6 * a0 * a3) *
          (H * (alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7
              κ).derivative -
            (9 : K[X]) * alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((122880 : K[X]) * H ^ 8 * a1 ^ 2 +
            (245760 : K[X]) * H ^ 8 * a0 * a2 +
            (10240 : K[X]) * H ^ 6 * a2 ^ 3 +
            (61440 : K[X]) * H ^ 6 * a1 * a2 * a3 +
            (30720 : K[X]) * H ^ 6 * a0 * a3 ^ 2 -
            (11520 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 2 -
            (7680 : K[X]) * H ^ 4 * a1 * a3 ^ 3 +
            (3360 : K[X]) * H ^ 2 * a2 * a3 ^ 4 - (308 : K[X]) * a3 ^ 6) *
          ((2 : K[X]) * H *
              (alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ).derivative -
            (15 : K[X]) * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ *
              H.derivative) +
        ((2359296 : K[X]) * H ^ 10 * a0 * a1 +
            (589824 : K[X]) * H ^ 8 * a1 * a2 ^ 2 +
            (589824 : K[X]) * H ^ 8 * a1 ^ 2 * a3 +
            (1179648 : K[X]) * H ^ 8 * a0 * a2 * a3 -
            (98304 : K[X]) * H ^ 6 * a2 ^ 3 * a3 -
            (294912 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 2 -
            (98304 : K[X]) * H ^ 6 * a0 * a3 ^ 3 +
            (73728 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 3 +
            (36864 : K[X]) * H ^ 4 * a1 * a3 ^ 4 -
            (18432 : K[X]) * H ^ 2 * a2 * a3 ^ 5 + (1536 : K[X]) * a3 ^ 7) *
          (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
            (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
              H.derivative) +
        ((5505024 : K[X]) * H ^ 12 * a0 ^ 2 +
            (4128768 : K[X]) * H ^ 10 * a1 ^ 2 * a2 +
            (4128768 : K[X]) * H ^ 10 * a0 * a2 ^ 2 +
            (8257536 : K[X]) * H ^ 10 * a0 * a1 * a3 -
            (86016 : K[X]) * H ^ 8 * a2 ^ 4 -
            (1032192 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 -
            (516096 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 2 -
            (1032192 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 2 +
            (215040 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 2 +
            (430080 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 3 +
            (107520 : K[X]) * H ^ 6 * a0 * a3 ^ 4 -
            (120960 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 4 -
            (48384 : K[X]) * H ^ 4 * a1 * a3 ^ 5 +
            (26208 : K[X]) * H ^ 2 * a2 * a3 ^ 6 - (1989 : K[X]) * a3 ^ 8) *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) *
              alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) := by
  simp only [memory410_flatEleventhDefect, memory410_flatTenthDefect,
    memory410_flatNinthDefect, memory410_flatEighthDefect, memory410_flatSeventhDefect,
    memory410_flatSixthDefect, memory410_flatFifthDefect, memory410_flatFourthDefect,
    memory410_flatThirdDefect,
    Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left,
    Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons,
    Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right,
    pow_zero, pow_one, one_mul, mul_one,
    Polynomial.derivative_neg, Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_ofNat, Polynomial.derivative_C, nsmul_eq_mul,
    zero_mul, mul_zero, zero_add, add_zero, neg_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat, Polynomial.eval_zero]
  ring

#print axioms alignedEleventhDefect_weightedDerivative_identity_410

end Max11DegreeRoutes
