import Fable610ScaleTwoAlignedFlatDefectPart07Scratch
import Fable610ScaleTwoAlignedTenthFacePart02Scratch
import Fable610ScaleTwoAlignedEleventhFacePart02Scratch

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
set_option maxHeartbeats 12800000000 in
/-- Exact combination of the degree-`4` Jacobian expression with the
weighted derivative of `Λ`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`13` through
degree-`5` rows.  The row sees neither `q₉` nor `q₈`, so there is no
`N`-correction and no `C`-correction — the source-correction module is
EMPTY, as for the ninth and tenth faces.  The corrections run through
the TENTH defect `Ω` (with cofactor `80 p₅`) even though `Ω` does not
enter the defect itself. -/
theorem alignedEleventhDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (156728328192 : K[X]) * H ^ 26 * (a4.derivative * b1 + a3.derivative
      * (b2 * (2 : K[X])) + a2.derivative * (b3 * (3 : K[X])) +
      a1.derivative * (b4 * (4 : K[X])) + a0.derivative * (b5 * (5 :
      K[X])) - ((a5 * (5 : K[X])) * b0.derivative + (a4 * (4 : K[X])) *
      b1.derivative + (a3 * (3 : K[X])) * b2.derivative + (a2 * (2 :
      K[X])) * b3.derivative + a1 * b4.derivative)) = ((2 : K[X]) * H *
      (alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
      κ).derivative - (55 : K[X]) * alignedEleventhDefect610 H a0 a1 a2 a3
      a4 a5 b1 b2 b3 b4 b5 b6 b7 κ * H.derivative) + ((5643509760 : K[X])
      * a0 * a4 * H ^ 18 + (470292480 : K[X]) * a0 * a5 ^ 2 * H ^ 15 +
      (5643509760 : K[X]) * a1 * a3 * H ^ 18 + (940584960 : K[X]) * a1 *
      a4 * a5 * H ^ 15 - (130636800 : K[X]) * a1 * a5 ^ 3 * H ^ 12 +
      (2821754880 : K[X]) * a2 ^ 2 * H ^ 18 + (940584960 : K[X]) * a2 * a3
      * a5 * H ^ 15 + (470292480 : K[X]) * a2 * a4 ^ 2 * H ^ 15 -
      (391910400 : K[X]) * a2 * a4 * a5 ^ 2 * H ^ 12 + (59875200 : K[X]) *
      a2 * a5 ^ 4 * H ^ 9 + (470292480 : K[X]) * a3 ^ 2 * a4 * H ^ 15 -
      (195955200 : K[X]) * a3 ^ 2 * a5 ^ 2 * H ^ 12 - (391910400 : K[X]) *
      a3 * a4 ^ 2 * a5 * H ^ 12 + (239500800 : K[X]) * a3 * a4 * a5 ^ 3 *
      H ^ 9 - (33929280 : K[X]) * a3 * a5 ^ 5 * H ^ 6 - (32659200 : K[X])
      * a4 ^ 4 * H ^ 12 + (119750400 : K[X]) * a4 ^ 3 * a5 ^ 2 * H ^ 9 -
      (84823200 : K[X]) * a4 ^ 2 * a5 ^ 4 * H ^ 6 + (21677040 : K[X]) * a4
      * a5 ^ 6 * H ^ 3 - (1870935 : K[X]) * a5 ^ 8) * ((2 : K[X]) * H *
      (alignedThirdDefect610 H a3 a4 a5 b7 κ).derivative - (15 : K[X]) *
      alignedThirdDefect610 H a3 a4 a5 b7 κ * H.derivative) + ((1612431360
      : K[X]) * a0 * a5 * H ^ 15 + (1612431360 : K[X]) * a1 * a4 * H ^ 15
      + (1612431360 : K[X]) * a2 * a3 * H ^ 15) * (H *
      (alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ).derivative - (10 :
      K[X]) * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ * H.derivative)
      + ((67184640 : K[X]) * a0 * H ^ 15 + (55987200 : K[X]) * a1 * a5 * H
      ^ 12 + (55987200 : K[X]) * a2 * a4 * H ^ 12 - (4665600 : K[X]) * a2
      * a5 ^ 2 * H ^ 9 + (27993600 : K[X]) * a3 ^ 2 * H ^ 12 - (9331200 :
      K[X]) * a3 * a4 * a5 * H ^ 9 + (1814400 : K[X]) * a3 * a5 ^ 3 * H ^
      6 - (1555200 : K[X]) * a4 ^ 3 * H ^ 9 + (2721600 : K[X]) * a4 ^ 2 *
      a5 ^ 2 * H ^ 6 - (982800 : K[X]) * a4 * a5 ^ 4 * H ^ 3 + (103740 :
      K[X]) * a5 ^ 6) * ((2 : K[X]) * H * (alignedFifthDefect610 H a1 a2
      a3 a4 a5 b5 b6 b7 κ).derivative - (25 : K[X]) *
      alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ * H.derivative) +
      ((7464960 : K[X]) * a1 * H ^ 12 + (4976640 : K[X]) * a2 * a5 * H ^ 9
      + (4976640 : K[X]) * a3 * a4 * H ^ 9 - (829440 : K[X]) * a3 * a5 ^ 2
      * H ^ 6 - (829440 : K[X]) * a4 ^ 2 * a5 * H ^ 6 + (368640 : K[X]) *
      a4 * a5 ^ 3 * H ^ 3 - (43008 : K[X]) * a5 ^ 5) * (H *
      (alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ).derivative
      - (15 : K[X]) * alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6
      b7 κ * H.derivative) + ((155520 : K[X]) * a2 * H ^ 9 + (77760 :
      K[X]) * a3 * a5 * H ^ 6 + (38880 : K[X]) * a4 ^ 2 * H ^ 6 - (19440 :
      K[X]) * a4 * a5 ^ 2 * H ^ 3 + (2430 : K[X]) * a5 ^ 4) * ((2 : K[X])
      * H * (alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7
      κ).derivative - (35 : K[X]) * alignedSeventhDefect610 H a0 a1 a2 a3
      a4 a5 b3 b4 b5 b6 b7 κ * H.derivative) + ((51840 : K[X]) * a3 * H ^
      6 + (17280 : K[X]) * a4 * a5 * H ^ 3 - (1920 : K[X]) * a5 ^ 3) * (H
      * (alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
      κ).derivative - (20 : K[X]) * alignedEighthDefect610 H a0 a1 a2 a3
      a4 a5 b2 b3 b4 b5 b6 b7 κ * H.derivative) + ((240 : K[X]) * a4 * H ^
      3 + (20 : K[X]) * a5 ^ 2) * ((2 : K[X]) * H * (alignedNinthDefect610
      H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ).derivative - (45 : K[X])
      * alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ *
      H.derivative) + ((80 : K[X]) * a5) * (H * (alignedTenthDefect610 H
      a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7 κ).derivative - (25 :
      K[X]) * alignedTenthDefect610 H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5
      b6 b7 κ * H.derivative) := by
  simp only [alignedEleventhDefect610, alignedTenthDefect610, memory610_flatNinthDefect, memory610_flatEighthDefect, memory610_flatSeventhDefect, memory610_flatSixthDefect, memory610_flatFifthDefect, memory610_flatFourthDefect, memory610_flatThirdDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, Polynomial.derivative_sub, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_neg, Polynomial.derivative_ofNat, Polynomial.derivative_C, nsmul_eq_mul, zero_mul, mul_zero, zero_add, add_zero, neg_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C,
    Polynomial.eval_natCast, Polynomial.eval_ofNat, Polynomial.eval_zero]
  ring

end Max11DegreeRoutes
