import Fable610ScaleTwoAlignedNinthFacePart02Scratch
import Fable610ScaleTwoAlignedFlatDefectPart07Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

open private memory610_flatThirdDefect from Fable610ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory610_flatFourthDefect from Fable610ScaleTwoAlignedFlatDefectPart02Scratch in
open private memory610_flatFifthDefect from Fable610ScaleTwoAlignedFlatDefectPart03Scratch in
open private memory610_flatSixthDefect from Fable610ScaleTwoAlignedFlatDefectPart04Scratch in
open private memory610_flatSeventhDefect from Fable610ScaleTwoAlignedFlatDefectPart05Scratch in
open private memory610_flatEighthDefect from Fable610ScaleTwoAlignedFlatDefectPart06Scratch in
open private memory610_flatNinthDefect from Fable610ScaleTwoAlignedFlatDefectPart07Scratch in
set_option maxHeartbeats 8000000000 in
/-- Exact combination of the degree-`6` Jacobian expression with the
weighted derivative of `L`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`13` through
degree-`7` rows.  The row sees neither `q₉` nor `q₈`, so there is no
`N`-correction and no `C`-correction — the source-correction module is
EMPTY. -/
theorem alignedNinthDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (544195584 : K[X]) * H ^ 20 * ((H ^ 3).derivative * b1 + a5.derivative *
      (b2 * (2 : K[X])) + a4.derivative * (b3 * (3 : K[X])) + a3.derivative
      * (b4 * (4 : K[X])) + a2.derivative * (b5 * (5 : K[X])) +
      a1.derivative * (b6 * (6 : K[X])) + a0.derivative * (b7 * (7 : K[X]))
      - ((H ^ 3 * (6 : K[X])) * b1.derivative + (a5 * (5 : K[X])) *
      b2.derivative + (a4 * (4 : K[X])) * b3.derivative + (a3 * (3 : K[X]))
      * b4.derivative + (a2 * (2 : K[X])) * b5.derivative + a1 *
      b6.derivative)) = ((2 : K[X]) * H * (alignedNinthDefect610 H a0 a1 a2
      a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ).derivative - (45 : K[X]) *
      alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ *
      H.derivative) + ((23514624 : K[X]) * a0 * H ^ 15 + (27433728 : K[X]) *
      a1 * a5 * H ^ 12 + (27433728 : K[X]) * a2 * a4 * H ^ 12 + (13716864 :
      K[X]) * a3 ^ 2 * H ^ 12 + (2286144 : K[X]) * a2 * a5 ^ 2 * H ^ 9 +
      (4572288 : K[X]) * a3 * a4 * a5 * H ^ 9 + (762048 : K[X]) * a4 ^ 3 * H
      ^ 9 - (635040 : K[X]) * a3 * a5 ^ 3 * H ^ 6 - (952560 : K[X]) * a4 ^ 2
      * a5 ^ 2 * H ^ 6 + (291060 : K[X]) * a4 * a5 ^ 4 * H ^ 3 - (27489 :
      K[X]) * a5 ^ 6) * ((2 : K[X]) * H * (alignedThirdDefect610 H a3 a4 a5
      b7 κ).derivative - (15 : K[X]) * alignedThirdDefect610 H a3 a4 a5 b7 κ
      * H.derivative) + ((7838208 : K[X]) * a1 * H ^ 12 + (7838208 : K[X]) *
      a2 * a5 * H ^ 9 + (7838208 : K[X]) * a3 * a4 * H ^ 9) * (H *
      (alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ).derivative - (10 :
      K[X]) * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ * H.derivative) +
      ((326592 : K[X]) * a2 * H ^ 9 + (272160 : K[X]) * a3 * a5 * H ^ 6 +
      (136080 : K[X]) * a4 ^ 2 * H ^ 6 - (22680 : K[X]) * a4 * a5 ^ 2 * H ^
      3 + (2205 : K[X]) * a5 ^ 4) * ((2 : K[X]) * H * (alignedFifthDefect610
      H a1 a2 a3 a4 a5 b5 b6 b7 κ).derivative - (25 : K[X]) *
      alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ * H.derivative) +
      ((36288 : K[X]) * a3 * H ^ 6 + (24192 : K[X]) * a4 * a5 * H ^ 3 -
      (1344 : K[X]) * a5 ^ 3) * (H * (alignedSixthDefect610 H a0 a1 a2 a3 a4
      a5 b4 b5 b6 b7 κ).derivative - (15 : K[X]) * alignedSixthDefect610 H
      a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ * H.derivative) + ((756 : K[X]) * a4 *
      H ^ 3 + (189 : K[X]) * a5 ^ 2) * ((2 : K[X]) * H *
      (alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7
      κ).derivative - (35 : K[X]) * alignedSeventhDefect610 H a0 a1 a2 a3 a4
      a5 b3 b4 b5 b6 b7 κ * H.derivative) + (252 : K[X]) * a5 * (H *
      (alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
      κ).derivative - (20 : K[X]) * alignedEighthDefect610 H a0 a1 a2 a3 a4
      a5 b2 b3 b4 b5 b6 b7 κ * H.derivative) := by
  simp only [memory610_flatNinthDefect, memory610_flatEighthDefect, memory610_flatSeventhDefect, memory610_flatSixthDefect, memory610_flatFifthDefect, memory610_flatFourthDefect, memory610_flatThirdDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, Polynomial.derivative_sub, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_neg, Polynomial.derivative_ofNat, Polynomial.derivative_C, nsmul_eq_mul, zero_mul, mul_zero, zero_add, add_zero, neg_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C,
    Polynomial.eval_natCast, Polynomial.eval_ofNat, Polynomial.eval_zero]
  ring

end Max11DegreeRoutes
