import Sol610ScaleTwoAlignedTwelfthCertificateWithCSplitBaseScratch

/-! # SPEED: theorems of `Sol610ScaleTwoAlignedTwelfthCertificateWithCScratch`, part 0 of 3, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open scoped Polynomial.Bivariate
open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000
set_option maxRecDepth 8000000

set_option maxHeartbeats 480000000 in
set_option maxRecDepth 100000 in
/-- Exact C-extended multiplier identity for the degree-three row. -/
theorem alignedTwelfthDefect_withC_multiplier_identity_610
    {K : Type*} [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7 b8 : K[X]) (κ : K) :
    (705277476864 : K[X]) * H ^ 29 *
        (a3.derivative * b1 + (2 : K[X]) * a2.derivative * b2 +
          (3 : K[X]) * a1.derivative * b3 +
          (4 : K[X]) * a0.derivative * b4 -
          ((4 : K[X]) * a4 * b0.derivative +
            (3 : K[X]) * a3 * b1.derivative +
            (2 : K[X]) * a2 * b2.derivative + a1 * b3.derivative)) =
      (16384 : K[X]) * alignedEvenWeightedRow610 30 H
        (alignedTwelfthDefect610 H a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1) +
      alignedEvenWeightedRow610 25 H
          (alignedTwelfthCofactorC610 H a0 a1 a2 a3 a4 a5) *
        alignedTwelfthBaseEquation610 H a4 a5 b8 κ +
      alignedTwelfthCofactorC610 H a0 a1 a2 a3 a4 a5 *
        alignedEvenWeightedRow610 5 H
          (alignedTwelfthBaseEquation610 H a4 a5 b8 κ) +
      alignedTwelfthCofactorD610 H a0 a1 a2 a3 a4 a5 *
        alignedOddWeightedRow610 15 H
          (alignedThirdDefect610 H a3 a4 a5 b7 κ) +
      alignedTwelfthCofactorE610 H a0 a1 a2 a3 a4 *
        alignedEvenWeightedRow610 10 H
          (alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ) +
      alignedTwelfthCofactorF610 H a0 a1 a2 a3 a4 a5 *
        alignedOddWeightedRow610 25 H
          (alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ) +
      alignedTwelfthCofactorG610 H a0 a1 a2 a3 a4 a5 *
        alignedEvenWeightedRow610 15 H
          (alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ) +
      alignedTwelfthCofactorI610 H a1 a2 a3 a4 a5 *
        alignedOddWeightedRow610 35 H
          (alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ) +
      alignedTwelfthCofactorJ610 H a2 a3 a4 a5 *
        alignedEvenWeightedRow610 20 H
          (alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 κ) +
      alignedTwelfthCofactorL610 H a3 a4 a5 *
        alignedOddWeightedRow610 45 H
          (alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ) +
      alignedTwelfthCofactorOmega610 H a4 *
        alignedEvenWeightedRow610 25 H
          (alignedTenthDefect610 H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7 κ) +
      alignedTwelfthCofactorLambda610 a5 *
        alignedOddWeightedRow610 55 H
          (alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ) := by
  simp only [alignedTwelfthBaseEquation610, alignedTwelfthCofactorC610,
    alignedTwelfthCofactorD610, alignedTwelfthCofactorE610,
    alignedTwelfthCofactorF610, alignedTwelfthCofactorG610,
    alignedTwelfthCofactorI610, alignedTwelfthCofactorJ610,
    alignedTwelfthCofactorL610, alignedTwelfthCofactorOmega610,
    alignedTwelfthCofactorLambda610, alignedEvenWeightedRow610,
    alignedOddWeightedRow610, alignedTwelfthDefect610,
    alignedTwelfthDefectBlock1_610, alignedTwelfthDefectBlock2_610,
    alignedTwelfthDefectBlock3_610, alignedTwelfthDefectBlock4_610,
    alignedTwelfthDefectBlock5_610, alignedEleventhDefect610,
    alignedTenthDefect610, alignedNinthDefect610, alignedEighthDefect610,
    alignedSeventhDefect610, alignedSixthDefect610, alignedFifthDefect610,
    alignedFourthDefect610, alignedThirdDefect610, alignedSecondDefect610,
    Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_ofNat, Polynomial.derivative_C,
    nsmul_eq_mul, zero_mul, mul_zero, zero_add, add_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

#print axioms alignedTwelfthDefect_withC_multiplier_identity_610

end Max11DegreeRoutes

end
