import Sol610ScaleTwoAlignedFourteenthResidualSourceBridgeScratch

/-! # Constant-field and local clearing bridge for the aligned `(6,10)` ν tail

The normalized weight-seventy residual is already known to have zero RatFunc
derivative on the supplied source.  This file records its compact, exact
weighted-homogeneous numerator and descends the resulting ground constant to
the original polynomial ring.  No source or square-root witness is changed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section FourteenthClearedNumerator610

variable {R : Type*} [CommRing R]

/-- The 72-term integral numerator obtained by substituting the aligned
depressed-coordinate numerators into `19042491875328 · ν`.  This definition
is over a commutative ring, so it remains a genuine polynomial expression
when instantiated in `k[X]`. -/
def clearedFourteenthResidual610
    (A B C0 D E P Q R0 S T U V W : R) : R :=
    (14040 : R) * A ^ 7
    - (44226 : R) * A ^ 6 * P
    - (110565 : R) * A ^ 5 * C0
    + (5103 : R) * A ^ 5 * R0
    - (163800 : R) * A ^ 4 * B ^ 2
    + (317520 : R) * A ^ 4 * B * Q
    + (306180 : R) * A ^ 4 * C0 * P
    + (4725 : R) * A ^ 4 * E
    - (3402 : R) * A ^ 4 * T
    + (362880 : R) * A ^ 3 * B ^ 2 * P
    + (604800 : R) * A ^ 3 * B * D
    - (136080 : R) * A ^ 3 * B * S
    + (255150 : R) * A ^ 3 * C0 ^ 2
    - (30618 : R) * A ^ 3 * C0 * R0
    - (762048 : R) * A ^ 3 * D * Q
    - (13608 : R) * A ^ 3 * E * P
    + (1458 : R) * A ^ 3 * V
    + (453600 : R) * A ^ 2 * B ^ 2 * C0
    - (27216 : R) * A ^ 2 * B ^ 2 * R0
    - (1143072 : R) * A ^ 2 * B * C0 * Q
    - (1306368 : R) * A ^ 2 * B * D * P
    + (23328 : R) * A ^ 2 * B * U
    - (551124 : R) * A ^ 2 * C0 ^ 2 * P
    - (17010 : R) * A ^ 2 * C0 * E
    + (17496 : R) * A ^ 2 * C0 * T
    - (544320 : R) * A ^ 2 * D ^ 2
    + (349920 : R) * A ^ 2 * D * S
    + (1458 : R) * A ^ 2 * E * R0
    + (44800 : R) * A * B ^ 4
    - (225792 : R) * A * B ^ 3 * Q
    - (653184 : R) * A * B ^ 2 * C0 * P
    - (10080 : R) * A * B ^ 2 * E
    + (10368 : R) * A * B ^ 2 * T
    - (1088640 : R) * A * B * C0 * D
    + (349920 : R) * A * B * C0 * S
    + (93312 : R) * A * B * D * R0
    + (36288 : R) * A * B * E * Q
    - (324 : R) * A * B * W
    - (153090 : R) * A * C0 ^ 3
    + (39366 : R) * A * C0 ^ 2 * R0
    + (1959552 : R) * A * C0 * D * Q
    + (34992 : R) * A * C0 * E * P
    - (6561 : R) * A * C0 * V
    + (1119744 : R) * A * D ^ 2 * P
    - (69984 : R) * A * D * U
    + (270 : R) * A * E ^ 2
    - (972 : R) * A * E * T
    - (32256 : R) * B ^ 4 * P
    - (107520 : R) * B ^ 3 * D
    + (34560 : R) * B ^ 3 * S
    - (136080 : R) * B ^ 2 * C0 ^ 2
    + (23328 : R) * B ^ 2 * C0 * R0
    + (580608 : R) * B ^ 2 * D * Q
    + (10368 : R) * B ^ 2 * E * P
    - (1944 : R) * B ^ 2 * V
    + (489888 : R) * B * C0 ^ 2 * Q
    + (1119744 : R) * B * C0 * D * P
    - (34992 : R) * B * C0 * U
    + (17280 : R) * B * D * E
    - (31104 : R) * B * D * T
    - (9720 : R) * B * E * S
    + (157464 : R) * C0 ^ 3 * P
    + (7290 : R) * C0 ^ 2 * E
    - (13122 : R) * C0 ^ 2 * T
    + (466560 : R) * C0 * D ^ 2
    - (524880 : R) * C0 * D * S
    - (2187 : R) * C0 * E * R0
    - (69984 : R) * D ^ 2 * R0
    - (54432 : R) * D * E * Q
    + (1944 : R) * D * W
    - (486 : R) * E ^ 2 * P
    + (729 : R) * E * V

/-- The source-polynomial specialization of the compact aligned numerator. -/
def alignedClearedFourteenthDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
  let A := (12 : R) * a4 * h ^ 6 - 5 * a5 ^ 2
  let B := (54 : R) * a3 * h ^ 12 - 36 * a4 * a5 * h ^ 6 + 10 * a5 ^ 3
  let C0 := (144 : R) * a2 * h ^ 18 - 72 * a3 * a5 * h ^ 12 +
    24 * a4 * a5 ^ 2 * h ^ 6 - 5 * a5 ^ 4
  let D := (324 : R) * a1 * h ^ 24 - 108 * a2 * a5 * h ^ 18 +
    27 * a3 * a5 ^ 2 * h ^ 12 - 6 * a4 * a5 ^ 3 * h ^ 6 + a5 ^ 5
  let E := (46656 : R) * a0 * h ^ 30 - 7776 * a1 * a5 * h ^ 24 +
    1296 * a2 * a5 ^ 2 * h ^ 18 - 216 * a3 * a5 ^ 3 * h ^ 12 +
    36 * a4 * a5 ^ 4 * h ^ 6 - 5 * a5 ^ 6
  let P := -(5 : R) * a5 ^ 2 + 4 * b8 * h ^ 2
  let Q := (10 : R) * a5 ^ 3 - 12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8
  let R0 := -(210 : R) * a5 ^ 4 + 336 * a5 ^ 2 * b8 * h ^ 2 -
    504 * a5 * b7 * h ^ 8 + 432 * b6 * h ^ 14
  let S := (28 : R) * a5 ^ 5 - 56 * a5 ^ 3 * b8 * h ^ 2 +
    126 * a5 ^ 2 * b7 * h ^ 8 - 216 * a5 * b6 * h ^ 14 +
    216 * b5 * h ^ 20
  let T := -(175 : R) * a5 ^ 6 + 420 * a5 ^ 4 * b8 * h ^ 2 -
    1260 * a5 ^ 3 * b7 * h ^ 8 + 3240 * a5 ^ 2 * b6 * h ^ 14 -
    6480 * a5 * b5 * h ^ 20 + 7776 * b4 * h ^ 26
  let U := (30 : R) * a5 ^ 7 - 84 * a5 ^ 5 * b8 * h ^ 2 +
    315 * a5 ^ 4 * b7 * h ^ 8 - 1080 * a5 ^ 3 * b6 * h ^ 14 +
    3240 * a5 ^ 2 * b5 * h ^ 20 - 7776 * a5 * b4 * h ^ 26 +
    11664 * b3 * h ^ 32
  let V := -(35 : R) * a5 ^ 8 + 112 * a5 ^ 6 * b8 * h ^ 2 -
    504 * a5 ^ 5 * b7 * h ^ 8 + 2160 * a5 ^ 4 * b6 * h ^ 14 -
    8640 * a5 ^ 3 * b5 * h ^ 20 + 31104 * a5 ^ 2 * b4 * h ^ 26 -
    93312 * a5 * b3 * h ^ 32 + 186624 * b2 * h ^ 38
  let W := (40 : R) * a5 ^ 9 - 144 * a5 ^ 7 * b8 * h ^ 2 +
    756 * a5 ^ 6 * b7 * h ^ 8 - 3888 * a5 ^ 5 * b6 * h ^ 14 +
    19440 * a5 ^ 4 * b5 * h ^ 20 - 93312 * a5 ^ 3 * b4 * h ^ 26 +
    419904 * a5 ^ 2 * b3 * h ^ 32 - 1679616 * a5 * b2 * h ^ 38 +
    5038848 * b1 * h ^ 44
  clearedFourteenthResidual610 A B C0 D E P Q R0 S T U V W

end FourteenthClearedNumerator610

section FourteenthNumericalClearing610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- Exact numerical and `h`-power clearing for the aligned weight-seventy
residual.  The coefficient `19042491875328` and all 72 terms were
independently reconstructed over `ℚ` by the bounded CAS ledger. -/
theorem fourteenthResidual610_eq_cleared_aligned
    (h A B C0 D E P Q R0 S T U V W : F) (hh : h ≠ 0) :
    (19042491875328 : F) * h ^ 70 *
        fourteenthResidual610 0
          (A / (12 * h ^ 10)) (B / (54 * h ^ 15))
          (C0 / (144 * h ^ 20)) (D / (324 * h ^ 25))
          (E / (46656 * h ^ 30)) (P / (4 * h ^ 10))
          (Q / (9 * h ^ 15)) (R0 / (432 * h ^ 20))
          (S / (216 * h ^ 25)) (T / (7776 * h ^ 30))
          (U / (11664 * h ^ 35)) (V / (186624 * h ^ 40))
          (W / (5038848 * h ^ 45)) =
      clearedFourteenthResidual610 A B C0 D E P Q R0 S T U V W := by
  simp only [fourteenthResidual610, rawFourthTailCoefficient610,
    rawFourthTailPure610, rawFourthTailLBlock610,
    rawFourthTailAlphaBlock610, rawFourthTailBetaBlock610,
    rawFourthTailDeltaBlock610, rawFourthTailEpsilonBlock610,
    rawFourthTailEtaBlock610, rawFourthTailThetaBlock610,
    rawFourthTailZetaBlock610, alphaResidual610, betaResidual610,
    gammaResidual610, deltaResidual610, epsilonResidual610,
    zetaResidual610, etaResidual610, thetaResidual610,
    kappaResidual610, lambdaResidual610, clearedFourteenthResidual610,
    zero_mul, zero_add]
  field_simp [hh]
  ring

end FourteenthNumericalClearing610

end Max11DegreeRoutes
