import Sol610ScaleTwoAlignedTwelfthDefectScratch

/-! # Actual degree-three multiplier certificate with the consumed C row

The frozen weight-thirty candidate necessarily sees `b8'`, while the literal
degree-three Jacobian row and defects `D,...,Lambda` do not.  The minimal
source-backed repair is the already-consumed base equation

`C = 9 b8 H - 15 a4 H^3 - 5 a5^2 - kappa H^5 = 0`

together with its weight-five derivative row.  Exact CAS elimination gives
the certificate below.  All rational cofactors were cleared by `16384`; the
identity is therefore valid over every characteristic-zero field without
polynomial division.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000

/-- Literal consumed base equation, with its integration constant retained. -/
def alignedTwelfthBaseEquation610 {K : Type*} [CommRing K]
    (H a4 a5 b8 : K[X]) (κ : K) : K[X] :=
  alignedSecondDefect610 H a4 a5 b8 - Polynomial.C κ * H ^ 5

/-- Polynomial multiplying the weight-five base row.  The factor `393216`
is `16384 * 24`, after clearing every CAS denominator. -/
def alignedTwelfthCofactorC610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 : K[X]) : K[X] :=
  (393216 : K[X]) * (
    (1062882 : K[X]) * H ^ 24 * a0 * a2 +
    (531441 : K[X]) * H ^ 24 * a1 ^ 2 -
    (1771470 : K[X]) * H ^ 21 * a0 * a3 * a5 -
    (885735 : K[X]) * H ^ 21 * a0 * a4 ^ 2 -
    (1771470 : K[X]) * H ^ 21 * a1 * a2 * a5 -
    (1771470 : K[X]) * H ^ 21 * a1 * a3 * a4 -
    (885735 : K[X]) * H ^ 21 * a2 ^ 2 * a4 -
    (885735 : K[X]) * H ^ 21 * a2 * a3 ^ 2 +
    (2361960 : K[X]) * H ^ 18 * a0 * a4 * a5 ^ 2 +
    (2361960 : K[X]) * H ^ 18 * a1 * a3 * a5 ^ 2 +
    (2361960 : K[X]) * H ^ 18 * a1 * a4 ^ 2 * a5 +
    (1180980 : K[X]) * H ^ 18 * a2 ^ 2 * a5 ^ 2 +
    (4723920 : K[X]) * H ^ 18 * a2 * a3 * a4 * a5 +
    (787320 : K[X]) * H ^ 18 * a2 * a4 ^ 3 +
    (787320 : K[X]) * H ^ 18 * a3 ^ 3 * a5 +
    (1180980 : K[X]) * H ^ 18 * a3 ^ 2 * a4 ^ 2 -
    (721710 : K[X]) * H ^ 15 * a0 * a5 ^ 4 -
    (2886840 : K[X]) * H ^ 15 * a1 * a4 * a5 ^ 3 -
    (2886840 : K[X]) * H ^ 15 * a2 * a3 * a5 ^ 3 -
    (4330260 : K[X]) * H ^ 15 * a2 * a4 ^ 2 * a5 ^ 2 -
    (4330260 : K[X]) * H ^ 15 * a3 ^ 2 * a4 * a5 ^ 2 -
    (2886840 : K[X]) * H ^ 15 * a3 * a4 ^ 3 * a5 -
    (144342 : K[X]) * H ^ 15 * a4 ^ 5 +
    (673596 : K[X]) * H ^ 12 * a1 * a5 ^ 5 +
    (3367980 : K[X]) * H ^ 12 * a2 * a4 * a5 ^ 4 +
    (1683990 : K[X]) * H ^ 12 * a3 ^ 2 * a5 ^ 4 +
    (6735960 : K[X]) * H ^ 12 * a3 * a4 ^ 2 * a5 ^ 3 +
    (1683990 : K[X]) * H ^ 12 * a4 ^ 4 * a5 ^ 2 -
    (636174 : K[X]) * H ^ 9 * a2 * a5 ^ 6 -
    (3817044 : K[X]) * H ^ 9 * a3 * a4 * a5 ^ 5 -
    (3180870 : K[X]) * H ^ 9 * a4 ^ 3 * a5 ^ 4 +
    (605880 : K[X]) * H ^ 6 * a3 * a5 ^ 7 +
    (2120580 : K[X]) * H ^ 6 * a4 ^ 2 * a5 ^ 6 -
    (580635 : K[X]) * H ^ 3 * a4 * a5 ^ 8 +
    (55913 : K[X]) * a5 ^ 10)

def alignedTwelfthCofactorD610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 : K[X]) : K[X] :=
  (20316635136 : K[X]) * H ^ 21 * a0 * a3 +
  (20316635136 : K[X]) * H ^ 21 * a1 * a2 +
  (3386105856 : K[X]) * H ^ 18 * a0 * a4 * a5 +
  (3386105856 : K[X]) * H ^ 18 * a1 * a3 * a5 +
  (1693052928 : K[X]) * H ^ 18 * a1 * a4 ^ 2 +
  (1693052928 : K[X]) * H ^ 18 * a2 ^ 2 * a5 +
  (3386105856 : K[X]) * H ^ 18 * a2 * a3 * a4 +
  (564350976 : K[X]) * H ^ 18 * a3 ^ 3 -
  (470292480 : K[X]) * H ^ 15 * a0 * a5 ^ 3 -
  (1410877440 : K[X]) * H ^ 15 * a1 * a4 * a5 ^ 2 -
  (1410877440 : K[X]) * H ^ 15 * a2 * a3 * a5 ^ 2 -
  (1410877440 : K[X]) * H ^ 15 * a2 * a4 ^ 2 * a5 -
  (1410877440 : K[X]) * H ^ 15 * a3 ^ 2 * a4 * a5 -
  (470292480 : K[X]) * H ^ 15 * a3 * a4 ^ 3 +
  (215550720 : K[X]) * H ^ 12 * a1 * a5 ^ 4 +
  (862202880 : K[X]) * H ^ 12 * a2 * a4 * a5 ^ 3 +
  (431101440 : K[X]) * H ^ 12 * a3 ^ 2 * a5 ^ 3 +
  (1293304320 : K[X]) * H ^ 12 * a3 * a4 ^ 2 * a5 ^ 2 +
  (215550720 : K[X]) * H ^ 12 * a4 ^ 4 * a5 -
  (122145408 : K[X]) * H ^ 9 * a2 * a5 ^ 5 -
  (610727040 : K[X]) * H ^ 9 * a3 * a4 * a5 ^ 4 -
  (407151360 : K[X]) * H ^ 9 * a4 ^ 3 * a5 ^ 3 +
  (78037344 : K[X]) * H ^ 6 * a3 * a5 ^ 6 +
  (234112032 : K[X]) * H ^ 6 * a4 ^ 2 * a5 ^ 5 -
  (53882928 : K[X]) * H ^ 3 * a4 * a5 ^ 7 +
  (4365515 : K[X]) * a5 ^ 9

def alignedTwelfthCofactorE610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 : K[X]) : K[X] :=
  (16384 : K[X]) * (177147 : K[X]) * H ^ 18 *
    ((2 : K[X]) * a0 * a4 + (2 : K[X]) * a1 * a3 + a2 ^ 2)

def alignedTwelfthCofactorF610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 : K[X]) : K[X] :=
  (36 : K[X]) * (
    (5598720 : K[X]) * H ^ 15 * a0 * a5 +
    (5598720 : K[X]) * H ^ 15 * a1 * a4 +
    (5598720 : K[X]) * H ^ 15 * a2 * a3 -
    (466560 : K[X]) * H ^ 12 * a1 * a5 ^ 2 -
    (933120 : K[X]) * H ^ 12 * a2 * a4 * a5 -
    (466560 : K[X]) * H ^ 12 * a3 ^ 2 * a5 -
    (466560 : K[X]) * H ^ 12 * a3 * a4 ^ 2 +
    (181440 : K[X]) * H ^ 9 * a2 * a5 ^ 3 +
    (544320 : K[X]) * H ^ 9 * a3 * a4 * a5 ^ 2 +
    (181440 : K[X]) * H ^ 9 * a4 ^ 3 * a5 -
    (98280 : K[X]) * H ^ 6 * a3 * a5 ^ 4 -
    (196560 : K[X]) * H ^ 6 * a4 ^ 2 * a5 ^ 3 +
    (62244 : K[X]) * H ^ 3 * a4 * a5 ^ 5 -
    (6175 : K[X]) * a5 ^ 7)

def alignedTwelfthCofactorG610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 : K[X]) : K[X] :=
  (12288 : K[X]) * (
    (2187 : K[X]) * H ^ 15 * a0 +
    (1458 : K[X]) * H ^ 12 * a1 * a5 +
    (1458 : K[X]) * H ^ 12 * a2 * a4 +
    (729 : K[X]) * H ^ 12 * a3 ^ 2 -
    (243 : K[X]) * H ^ 9 * a2 * a5 ^ 2 -
    (486 : K[X]) * H ^ 9 * a3 * a4 * a5 -
    (81 : K[X]) * H ^ 9 * a4 ^ 3 +
    (108 : K[X]) * H ^ 6 * a3 * a5 ^ 3 +
    (162 : K[X]) * H ^ 6 * a4 ^ 2 * a5 ^ 2 -
    (63 : K[X]) * H ^ 3 * a4 * a5 ^ 4 +
    (7 : K[X]) * a5 ^ 6)

def alignedTwelfthCofactorI610 {K : Type*} [CommRing K]
    (H a1 a2 a3 a4 a5 : K[X]) : K[X] :=
  (4374 : K[X]) * (
    (128 : K[X]) * H ^ 12 * a1 +
    (64 : K[X]) * H ^ 9 * a2 * a5 +
    (64 : K[X]) * H ^ 9 * a3 * a4 -
    (16 : K[X]) * H ^ 6 * a3 * a5 ^ 2 -
    (16 : K[X]) * H ^ 6 * a4 ^ 2 * a5 +
    (8 : K[X]) * H ^ 3 * a4 * a5 ^ 3 - a5 ^ 5)

def alignedTwelfthCofactorJ610 {K : Type*} [CommRing K]
    (H a2 a3 a4 a5 : K[X]) : K[X] :=
  (576 : K[X]) * (
    (324 : K[X]) * H ^ 9 * a2 +
    (108 : K[X]) * H ^ 6 * a3 * a5 +
    (54 : K[X]) * H ^ 6 * a4 ^ 2 -
    (36 : K[X]) * H ^ 3 * a4 * a5 ^ 2 +
    (5 : K[X]) * a5 ^ 4)

def alignedTwelfthCofactorL610 {K : Type*} [CommRing K]
    (H a3 a4 a5 : K[X]) : K[X] :=
  (4 : K[X]) * ((216 : K[X]) * H ^ 6 * a3 +
    (36 : K[X]) * H ^ 3 * a4 * a5 - (5 : K[X]) * a5 ^ 3)

def alignedTwelfthCofactorOmega610 {K : Type*} [CommRing K]
    (H a4 : K[X]) : K[X] := (288 : K[X]) * H ^ 3 * a4

def alignedTwelfthCofactorLambda610 {K : Type*} [CommRing K]
    (a5 : K[X]) : K[X] := (3 : K[X]) * a5

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
