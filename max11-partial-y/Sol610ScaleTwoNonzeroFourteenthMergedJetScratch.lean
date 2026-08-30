import Sol610ScaleTwoNonzeroFourteenthSourceDescentScratch

/-! # The merged-jet head of the nonzero `(6,10)` fourth tail

The 85-term compact bar numerator has order `63` on the merged source jet.
This file records its quotient without expanding in the original source
coefficients, and identifies its residue at the supplied linear root.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section MergedBarQuotient610

variable {R : Type*} [CommRing R]

private def nuBarAHigh610
    (A B C0 E P Q R0 T : R) : R :=
    (14040 : R) * A ^ 7
    - (44226 : R) * A ^ 6 * P
    - (110565 : R) * A ^ 5 * C0
    + (5103 : R) * A ^ 5 * R0
    - (163800 : R) * A ^ 4 * B ^ 2
    + (317520 : R) * A ^ 4 * B * Q
    + (306180 : R) * A ^ 4 * C0 * P
    + (4725 : R) * A ^ 4 * E
    - (3402 : R) * A ^ 4 * T

private def nuBarAMid610
    (A B C0 D E P Q R0 S T U V : R) : R :=
    (362880 : R) * A ^ 3 * B ^ 2 * P
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

private def nuBarALow610
    (A B C0 D E P Q R0 S T U V W : R) : R :=
    (44800 : R) * A * B ^ 4
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

private def nuBarAZero610
    (B C0 D E P Q R0 S T U V W : R) : R :=
    -(32256 : R) * B ^ 4 * P
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

private def nuBarLambda610
    (A B C0 D E lambda : R) : R :=
    (88452 : R) * A ^ 5 * B * lambda
    - (204120 : R) * A ^ 4 * D * lambda
    - (408240 : R) * A ^ 3 * B * C0 * lambda
    - (120960 : R) * A ^ 2 * B ^ 3 * lambda
    + (13608 : R) * A ^ 2 * B * E * lambda
    + (734832 : R) * A ^ 2 * C0 * D * lambda
    + (435456 : R) * A * B ^ 2 * D * lambda
    + (367416 : R) * A * B * C0 ^ 2 * lambda
    - (23328 : R) * A * D * E * lambda
    + (72576 : R) * B ^ 3 * C0 * lambda
    - (11664 : R) * B * C0 * E * lambda
    - (373248 : R) * B * D ^ 2 * lambda
    - (314928 : R) * C0 ^ 2 * D * lambda

private def nuJetAHigh610
    (h A B C0 E P Q R0 T : R) : R :=
    (14040 : R) * A ^ 7 - 44226 * A ^ 6 * P - 110565 * A ^ 5 * C0 +
      5103 * A ^ 5 * R0 - 163800 * A ^ 4 * B ^ 2 * h +
      317520 * A ^ 4 * B * Q * h + 306180 * A ^ 4 * C0 * P +
      4725 * A ^ 4 * E * h - 3402 * A ^ 4 * T

private def nuJetAMid610
    (h A B C0 D E P Q R0 S T U V : R) : R :=
    362880 * A ^ 3 * B ^ 2 * P * h + 604800 * A ^ 3 * B * D * h -
      136080 * A ^ 3 * B * S * h + 255150 * A ^ 3 * C0 ^ 2 -
      30618 * A ^ 3 * C0 * R0 - 762048 * A ^ 3 * D * Q * h -
      13608 * A ^ 3 * E * P * h + 1458 * A ^ 3 * V * h +
      453600 * A ^ 2 * B ^ 2 * C0 * h - 27216 * A ^ 2 * B ^ 2 * R0 * h -
      1143072 * A ^ 2 * B * C0 * Q * h -
      1306368 * A ^ 2 * B * D * P * h + 23328 * A ^ 2 * B * U * h -
      551124 * A ^ 2 * C0 ^ 2 * P - 17010 * A ^ 2 * C0 * E * h +
      17496 * A ^ 2 * C0 * T - 544320 * A ^ 2 * D ^ 2 * h +
      349920 * A ^ 2 * D * S * h + 1458 * A ^ 2 * E * R0 * h

private def nuJetALow610
    (h A B C0 D E P Q R0 S T U V W : R) : R :=
    44800 * A * B ^ 4 * h ^ 2 - 225792 * A * B ^ 3 * Q * h ^ 2 -
      653184 * A * B ^ 2 * C0 * P * h - 10080 * A * B ^ 2 * E * h ^ 2 +
      10368 * A * B ^ 2 * T * h - 1088640 * A * B * C0 * D * h +
      349920 * A * B * C0 * S * h + 93312 * A * B * D * R0 * h +
      36288 * A * B * E * Q * h ^ 2 - 324 * A * B * W * h ^ 2 -
      153090 * A * C0 ^ 3 + 39366 * A * C0 ^ 2 * R0 +
      1959552 * A * C0 * D * Q * h + 34992 * A * C0 * E * P * h -
      6561 * A * C0 * V * h + 1119744 * A * D ^ 2 * P * h -
      69984 * A * D * U * h + 270 * A * E ^ 2 * h ^ 2 -
      972 * A * E * T * h

private def nuJetAZero610
    (h B C0 D E P Q R0 S T U V W : R) : R :=
    -32256 * B ^ 4 * P * h ^ 2 - 107520 * B ^ 3 * D * h ^ 2 +
      34560 * B ^ 3 * S * h ^ 2 - 136080 * B ^ 2 * C0 ^ 2 * h +
      23328 * B ^ 2 * C0 * R0 * h + 580608 * B ^ 2 * D * Q * h ^ 2 +
      10368 * B ^ 2 * E * P * h ^ 2 - 1944 * B ^ 2 * V * h ^ 2 +
      489888 * B * C0 ^ 2 * Q * h + 1119744 * B * C0 * D * P * h -
      34992 * B * C0 * U * h + 17280 * B * D * E * h ^ 2 -
      31104 * B * D * T * h - 9720 * B * E * S * h ^ 2 +
      157464 * C0 ^ 3 * P + 7290 * C0 ^ 2 * E * h -
      13122 * C0 ^ 2 * T + 466560 * C0 * D ^ 2 * h -
      524880 * C0 * D * S * h - 2187 * C0 * E * R0 * h -
      69984 * D ^ 2 * R0 * h - 54432 * D * E * Q * h ^ 2 +
      1944 * D * W * h ^ 2 - 486 * E ^ 2 * P * h ^ 2 +
      729 * E * V * h ^ 2

private def nuJetLambda610
    (h A B C0 D E lambda : R) : R :=
    88452 * A ^ 5 * B * lambda * h - 204120 * A ^ 4 * D * lambda * h -
      408240 * A ^ 3 * B * C0 * lambda * h -
      120960 * A ^ 2 * B ^ 3 * lambda * h ^ 2 +
      13608 * A ^ 2 * B * E * lambda * h ^ 2 +
      734832 * A ^ 2 * C0 * D * lambda * h +
      435456 * A * B ^ 2 * D * lambda * h ^ 2 +
      367416 * A * B * C0 ^ 2 * lambda * h -
      23328 * A * D * E * lambda * h ^ 2 +
      72576 * B ^ 3 * C0 * lambda * h ^ 2 -
      11664 * B * C0 * E * lambda * h ^ 2 -
      373248 * B * D ^ 2 * lambda * h ^ 2 -
      314928 * C0 ^ 2 * D * lambda * h

/-- Quotient after assigning merged-jet orders
`(9,14,18,23,28;9,14,18,23,27,32,37,42;5)` to the compact bar
coordinates and removing the common factor `h^63`. -/
def nonzeroFourteenthMergedBarQuotient610
    (h A B C0 D E P Q R0 S T U V W lambda : R) : R :=
  nuJetAHigh610 h A B C0 E P Q R0 T +
    nuJetAMid610 h A B C0 D E P Q R0 S T U V +
    nuJetALow610 h A B C0 D E P Q R0 S T U V W +
    nuJetAZero610 h B C0 D E P Q R0 S T U V W +
    nuJetLambda610 h A B C0 D E lambda

private theorem nonzeroClearedFourteenthResidual610_blocks
    (A B C0 D E P Q R0 S T U V W lambda : R) :
    nonzeroClearedFourteenthResidual610 A B C0 D E P Q R0 S T U V W
        lambda =
      nuBarAHigh610 A B C0 E P Q R0 T +
      nuBarAMid610 A B C0 D E P Q R0 S T U V +
      nuBarALow610 A B C0 D E P Q R0 S T U V W +
      nuBarAZero610 B C0 D E P Q R0 S T U V W +
      nuBarLambda610 A B C0 D E lambda := by
  simp only [nonzeroClearedFourteenthResidual610,
    clearedFourteenthResidual610, nuBarAHigh610, nuBarAMid610,
    nuBarALow610, nuBarAZero610, nuBarLambda610, sub_eq_add_neg,
    neg_mul, add_assoc]

private theorem nuBarAHigh610_factored
    (h A B C0 E P Q R0 T : R) :
    nuBarAHigh610 (h ^ 9 * A) (h ^ 14 * B) (h ^ 18 * C0)
        (h ^ 28 * E) (h ^ 9 * P) (h ^ 14 * Q) (h ^ 18 * R0)
        (h ^ 27 * T) =
      h ^ 63 * nuJetAHigh610 h A B C0 E P Q R0 T := by
  simp only [nuBarAHigh610, nuJetAHigh610]
  ring

private theorem nuBarAMid610_factored
    (h A B C0 D E P Q R0 S T U V : R) :
    nuBarAMid610 (h ^ 9 * A) (h ^ 14 * B) (h ^ 18 * C0)
        (h ^ 23 * D) (h ^ 28 * E) (h ^ 9 * P) (h ^ 14 * Q)
        (h ^ 18 * R0) (h ^ 23 * S) (h ^ 27 * T) (h ^ 32 * U)
        (h ^ 37 * V) =
      h ^ 63 * nuJetAMid610 h A B C0 D E P Q R0 S T U V := by
  simp only [nuBarAMid610, nuJetAMid610]
  ring

private theorem nuBarALow610_factored
    (h A B C0 D E P Q R0 S T U V W : R) :
    nuBarALow610 (h ^ 9 * A) (h ^ 14 * B) (h ^ 18 * C0)
        (h ^ 23 * D) (h ^ 28 * E) (h ^ 9 * P) (h ^ 14 * Q)
        (h ^ 18 * R0) (h ^ 23 * S) (h ^ 27 * T) (h ^ 32 * U)
        (h ^ 37 * V) (h ^ 42 * W) =
      h ^ 63 * nuJetALow610 h A B C0 D E P Q R0 S T U V W := by
  simp only [nuBarALow610, nuJetALow610]
  ring

private theorem nuBarAZero610_factored
    (h B C0 D E P Q R0 S T U V W : R) :
    nuBarAZero610 (h ^ 14 * B) (h ^ 18 * C0) (h ^ 23 * D)
        (h ^ 28 * E) (h ^ 9 * P) (h ^ 14 * Q) (h ^ 18 * R0)
        (h ^ 23 * S) (h ^ 27 * T) (h ^ 32 * U) (h ^ 37 * V)
        (h ^ 42 * W) =
      h ^ 63 * nuJetAZero610 h B C0 D E P Q R0 S T U V W := by
  simp only [nuBarAZero610, nuJetAZero610]
  ring

private theorem nuBarLambda610_factored
    (h A B C0 D E lambda : R) :
    nuBarLambda610 (h ^ 9 * A) (h ^ 14 * B) (h ^ 18 * C0)
        (h ^ 23 * D) (h ^ 28 * E) (h ^ 5 * lambda) =
      h ^ 63 * nuJetLambda610 h A B C0 D E lambda := by
  simp only [nuBarLambda610, nuJetLambda610]
  ring

set_option maxHeartbeats 400000000 in
/-- The quotient is exactly the compact numerator after the merged orders
are inserted.  The certificate is split into five bounded homogeneity
blocks so no single reflection step expands all 85 terms. -/
theorem nonzeroClearedFourteenthResidual610_mergedBar_factored
    (h A B C0 D E P Q R0 S T U V W lambda : R) :
    nonzeroClearedFourteenthResidual610
        (h ^ 9 * A) (h ^ 14 * B) (h ^ 18 * C0) (h ^ 23 * D)
        (h ^ 28 * E) (h ^ 9 * P) (h ^ 14 * Q) (h ^ 18 * R0)
        (h ^ 23 * S) (h ^ 27 * T) (h ^ 32 * U) (h ^ 37 * V)
        (h ^ 42 * W) (h ^ 5 * lambda) =
      h ^ 63 *
        nonzeroFourteenthMergedBarQuotient610 h A B C0 D E P Q R0 S T U
          V W lambda := by
  rw [nonzeroClearedFourteenthResidual610_blocks]
  rw [nuBarAHigh610_factored, nuBarAMid610_factored,
    nuBarALow610_factored, nuBarAZero610_factored,
    nuBarLambda610_factored]
  simp only [nonzeroFourteenthMergedBarQuotient610]
  ring

end MergedBarQuotient610

section MergedSourceBars610

variable {R : Type*} [CommRing R]

def mergedNuA610 (h w1 a41 : R) : R := 12 * a41 - 5 * h * w1 ^ 2
def mergedNuB610 (h w1 a41 p32 : R) : R :=
  54 * p32 - 36 * a41 * w1 + 10 * h * w1 ^ 3
def mergedNuC610 (h w1 a41 p32 p2 : R) : R :=
  144 * p2 + 24 * a41 * h * w1 ^ 2 - 72 * h * p32 * w1 -
    5 * h ^ 2 * w1 ^ 4
def mergedNuD610 (h w1 a41 p32 p2 p1 : R) : R :=
  -108 * p2 * w1 + h * (-6 * a41 * w1 ^ 3 + 324 * p1 +
    27 * p32 * w1 ^ 2) + h ^ 2 * w1 ^ 5
def mergedNuE610 (h w1 a41 p32 p2 p1 p0 : R) : R :=
  1296 * p2 * w1 ^ 2 + h * (36 * a41 * w1 ^ 4 - 7776 * p1 * w1 -
    216 * p32 * w1 ^ 3) + h ^ 2 * (46656 * p0 - 5 * w1 ^ 6)
def mergedNuP610 (h w1 s1 lambda : R) : R :=
  4 * s1 + h * (2 * lambda * w1 - 5 * w1 ^ 2)
def mergedNuQ610 (h w1 s1 u2 lambda : R) : R :=
  -12 * s1 * w1 + 9 * u2 + h * (-3 * lambda * w1 ^ 2 + 10 * w1 ^ 3)
def mergedNuR610 (h w1 s1 u2 b62 lambda : R) : R :=
  432 * b62 + h * (336 * s1 * w1 ^ 2 - 504 * u2 * w1) +
    h ^ 2 * (56 * lambda * w1 ^ 3 - 210 * w1 ^ 4)
def mergedNuS610 (h w1 s1 u2 b62 q53 lambda : R) : R :=
  -216 * b62 * w1 + 216 * q53 +
    h * (-56 * s1 * w1 ^ 3 + 126 * u2 * w1 ^ 2) +
    h ^ 2 * (-7 * lambda * w1 ^ 4 + 28 * w1 ^ 5)
def mergedNuT610 (h w1 s1 u2 b62 q53 q41 lambda : R) : R :=
  7776 * q41 + h * (3240 * b62 * w1 ^ 2 - 6480 * q53 * w1) +
    h ^ 2 * (420 * s1 * w1 ^ 4 - 1260 * u2 * w1 ^ 3) +
    h ^ 3 * (42 * lambda * w1 ^ 5 - 175 * w1 ^ 6)
def mergedNuU610 (h w1 s1 u2 b62 q53 q41 q3 lambda : R) : R :=
  11664 * q3 - 7776 * q41 * w1 +
    h * (-1080 * b62 * w1 ^ 3 + 3240 * q53 * w1 ^ 2) +
    h ^ 2 * (-84 * s1 * w1 ^ 5 + 315 * u2 * w1 ^ 4) +
    h ^ 3 * (-7 * lambda * w1 ^ 6 + 30 * w1 ^ 7)
def mergedNuV610 (h w1 s1 u2 b62 q53 q41 q3 q2 lambda : R) : R :=
  -93312 * q3 * w1 + 31104 * q41 * w1 ^ 2 +
    h * (2160 * b62 * w1 ^ 4 + 186624 * q2 - 8640 * q53 * w1 ^ 3) +
    h ^ 2 * (112 * s1 * w1 ^ 6 - 504 * u2 * w1 ^ 5) +
    h ^ 3 * (8 * lambda * w1 ^ 7 - 35 * w1 ^ 8)
def mergedNuW610
    (h w1 s1 u2 b62 q53 q41 q3 q2 q1 lambda : R) : R :=
  419904 * q3 * w1 ^ 2 - 93312 * q41 * w1 ^ 3 +
    h * (-3888 * b62 * w1 ^ 5 - 1679616 * q2 * w1 +
      19440 * q53 * w1 ^ 4) +
    h ^ 2 * (5038848 * q1 - 144 * s1 * w1 ^ 7 + 756 * u2 * w1 ^ 6) +
    h ^ 3 * (-9 * lambda * w1 ^ 8 + 40 * w1 ^ 9)

/-- Compact order-`63` quotient on the literal merged source jet. -/
def nonzeroFourteenthMergedJetQuotient610
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 lambda : R) : R :=
  nonzeroFourteenthMergedBarQuotient610 h
    (mergedNuA610 h w1 a41)
    (mergedNuB610 h w1 a41 p32)
    (mergedNuC610 h w1 a41 p32 p2)
    (mergedNuD610 h w1 a41 p32 p2 p1)
    (mergedNuE610 h w1 a41 p32 p2 p1 p0)
    (mergedNuP610 h w1 s1 lambda)
    (mergedNuQ610 h w1 s1 u2 lambda)
    (mergedNuR610 h w1 s1 u2 b62 lambda)
    (mergedNuS610 h w1 s1 u2 b62 q53 lambda)
    (mergedNuT610 h w1 s1 u2 b62 q53 q41 lambda)
    (mergedNuU610 h w1 s1 u2 b62 q53 q41 q3 lambda)
    (mergedNuV610 h w1 s1 u2 b62 q53 q41 q3 q2 lambda)
    (mergedNuW610 h w1 s1 u2 b62 q53 q41 q3 q2 q1 lambda) lambda

/-- The exact `h^63` head from the bounded CAS ledger. -/
def nonzeroFourteenthMergedJetHead610
    (a41 s1 b62 p2 q41 : R) : R :=
  (967458816 : R) *
    ((520 : R) * a41 ^ 7 - 546 * a41 ^ 6 * s1 +
      567 * a41 ^ 5 * b62 - 4095 * a41 ^ 5 * p2 +
      3780 * a41 ^ 4 * p2 * s1 - 567 * a41 ^ 4 * q41 -
      3402 * a41 ^ 3 * b62 * p2 + 9450 * a41 ^ 3 * p2 ^ 2 -
      6804 * a41 ^ 2 * p2 ^ 2 * s1 + 2916 * a41 ^ 2 * p2 * q41 +
      4374 * a41 * b62 * p2 ^ 2 - 5670 * a41 * p2 ^ 3 +
      1944 * p2 ^ 3 * s1 - 2187 * p2 ^ 2 * q41)

private def rawNuA610 (h a5 a4 : R) : R :=
  12 * a4 * h ^ 6 - 5 * a5 ^ 2

private def rawNuB610 (h a5 a4 a3 : R) : R :=
  54 * a3 * h ^ 12 - 36 * a4 * a5 * h ^ 6 + 10 * a5 ^ 3

private def rawNuC610 (h a5 a4 a3 a2 : R) : R :=
  144 * a2 * h ^ 18 - 72 * a3 * a5 * h ^ 12 +
    24 * a4 * a5 ^ 2 * h ^ 6 - 5 * a5 ^ 4

private def rawNuD610 (h a5 a4 a3 a2 a1 : R) : R :=
  324 * a1 * h ^ 24 - 108 * a2 * a5 * h ^ 18 +
    27 * a3 * a5 ^ 2 * h ^ 12 - 6 * a4 * a5 ^ 3 * h ^ 6 + a5 ^ 5

private def rawNuE610 (h a5 a4 a3 a2 a1 a0 : R) : R :=
  46656 * a0 * h ^ 30 - 7776 * a1 * a5 * h ^ 24 +
    1296 * a2 * a5 ^ 2 * h ^ 18 - 216 * a3 * a5 ^ 3 * h ^ 12 +
    36 * a4 * a5 ^ 4 * h ^ 6 - 5 * a5 ^ 6

private def rawNuP610 (h a5 b8 lambda : R) : R :=
  -5 * a5 ^ 2 + 2 * lambda * a5 * h ^ 5 + 4 * b8 * h ^ 2

private def rawNuQ610 (h a5 b8 b7 lambda : R) : R :=
  10 * a5 ^ 3 - 3 * lambda * a5 ^ 2 * h ^ 5 -
    12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8

private def rawNuR610 (h a5 b8 b7 b6 lambda : R) : R :=
  -210 * a5 ^ 4 + 56 * lambda * a5 ^ 3 * h ^ 5 +
    336 * a5 ^ 2 * b8 * h ^ 2 - 504 * a5 * b7 * h ^ 8 +
    432 * b6 * h ^ 14

private def rawNuS610 (h a5 b8 b7 b6 b5 lambda : R) : R :=
  28 * a5 ^ 5 - 7 * lambda * a5 ^ 4 * h ^ 5 -
    56 * a5 ^ 3 * b8 * h ^ 2 + 126 * a5 ^ 2 * b7 * h ^ 8 -
    216 * a5 * b6 * h ^ 14 + 216 * b5 * h ^ 20

private def rawNuT610 (h a5 b8 b7 b6 b5 b4 lambda : R) : R :=
  -175 * a5 ^ 6 + 42 * lambda * a5 ^ 5 * h ^ 5 +
    420 * a5 ^ 4 * b8 * h ^ 2 - 1260 * a5 ^ 3 * b7 * h ^ 8 +
    3240 * a5 ^ 2 * b6 * h ^ 14 - 6480 * a5 * b5 * h ^ 20 +
    7776 * b4 * h ^ 26

private def rawNuU610 (h a5 b8 b7 b6 b5 b4 b3 lambda : R) : R :=
  30 * a5 ^ 7 - 7 * lambda * a5 ^ 6 * h ^ 5 -
    84 * a5 ^ 5 * b8 * h ^ 2 + 315 * a5 ^ 4 * b7 * h ^ 8 -
    1080 * a5 ^ 3 * b6 * h ^ 14 + 3240 * a5 ^ 2 * b5 * h ^ 20 -
    7776 * a5 * b4 * h ^ 26 + 11664 * b3 * h ^ 32

private def rawNuV610
    (h a5 b8 b7 b6 b5 b4 b3 b2 lambda : R) : R :=
  -35 * a5 ^ 8 + 8 * lambda * a5 ^ 7 * h ^ 5 +
    112 * a5 ^ 6 * b8 * h ^ 2 - 504 * a5 ^ 5 * b7 * h ^ 8 +
    2160 * a5 ^ 4 * b6 * h ^ 14 - 8640 * a5 ^ 3 * b5 * h ^ 20 +
    31104 * a5 ^ 2 * b4 * h ^ 26 - 93312 * a5 * b3 * h ^ 32 +
    186624 * b2 * h ^ 38

private def rawNuW610
    (h a5 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
  40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
    144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
    3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
    93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
    1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44

private theorem nonzeroLocalClearedFourteenthDefect610_eq_rawBars
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    nonzeroLocalClearedFourteenthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6
        b5 b4 b3 b2 b1 lambda =
      nonzeroClearedFourteenthResidual610
        (rawNuA610 h a5 a4) (rawNuB610 h a5 a4 a3)
        (rawNuC610 h a5 a4 a3 a2) (rawNuD610 h a5 a4 a3 a2 a1)
        (rawNuE610 h a5 a4 a3 a2 a1 a0) (rawNuP610 h a5 b8 lambda)
        (rawNuQ610 h a5 b8 b7 lambda) (rawNuR610 h a5 b8 b7 b6 lambda)
        (rawNuS610 h a5 b8 b7 b6 b5 lambda)
        (rawNuT610 h a5 b8 b7 b6 b5 b4 lambda)
        (rawNuU610 h a5 b8 b7 b6 b5 b4 b3 lambda)
        (rawNuV610 h a5 b8 b7 b6 b5 b4 b3 b2 lambda)
        (rawNuW610 h a5 b8 b7 b6 b5 b4 b3 b2 b1 lambda)
        (lambda * h ^ 5) := by
  rfl

private theorem rawNuA610_factored (h w1 a41 : R) :
    rawNuA610 h (h ^ 5 * w1) (h ^ 3 * a41) =
      h ^ 9 * mergedNuA610 h w1 a41 := by
  simp [rawNuA610, mergedNuA610]; ring

private theorem rawNuB610_factored (h w1 a41 p32 : R) :
    rawNuB610 h (h ^ 5 * w1) (h ^ 3 * a41) (h ^ 2 * p32) =
      h ^ 14 * mergedNuB610 h w1 a41 p32 := by
  simp [rawNuB610, mergedNuB610]; ring

private theorem rawNuC610_factored (h w1 a41 p32 p2 : R) :
    rawNuC610 h (h ^ 5 * w1) (h ^ 3 * a41) (h ^ 2 * p32) p2 =
      h ^ 18 * mergedNuC610 h w1 a41 p32 p2 := by
  simp [rawNuC610, mergedNuC610]; ring

private theorem rawNuD610_factored (h w1 a41 p32 p2 p1 : R) :
    rawNuD610 h (h ^ 5 * w1) (h ^ 3 * a41) (h ^ 2 * p32) p2 p1 =
      h ^ 23 * mergedNuD610 h w1 a41 p32 p2 p1 := by
  simp [rawNuD610, mergedNuD610]; ring

private theorem rawNuE610_factored (h w1 a41 p32 p2 p1 p0 : R) :
    rawNuE610 h (h ^ 5 * w1) (h ^ 3 * a41) (h ^ 2 * p32) p2 p1 p0 =
      h ^ 28 * mergedNuE610 h w1 a41 p32 p2 p1 p0 := by
  simp [rawNuE610, mergedNuE610]; ring

private theorem rawNuP610_factored (h w1 s1 lambda : R) :
    rawNuP610 h (h ^ 5 * w1) (h ^ 7 * s1) lambda =
      h ^ 9 * mergedNuP610 h w1 s1 lambda := by
  simp [rawNuP610, mergedNuP610]; ring

private theorem rawNuQ610_factored (h w1 s1 u2 lambda : R) :
    rawNuQ610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2) lambda =
      h ^ 14 * mergedNuQ610 h w1 s1 u2 lambda := by
  simp [rawNuQ610, mergedNuQ610]; ring

private theorem rawNuR610_factored (h w1 s1 u2 b62 lambda : R) :
    rawNuR610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) lambda =
      h ^ 18 * mergedNuR610 h w1 s1 u2 b62 lambda := by
  simp [rawNuR610, mergedNuR610]; ring

private theorem rawNuS610_factored (h w1 s1 u2 b62 q53 lambda : R) :
    rawNuS610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) (h ^ 3 * q53) lambda =
      h ^ 23 * mergedNuS610 h w1 s1 u2 b62 q53 lambda := by
  simp [rawNuS610, mergedNuS610]; ring

private theorem rawNuT610_factored
    (h w1 s1 u2 b62 q53 q41 lambda : R) :
    rawNuT610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) (h ^ 3 * q53) (h * q41) lambda =
      h ^ 27 * mergedNuT610 h w1 s1 u2 b62 q53 q41 lambda := by
  simp [rawNuT610, mergedNuT610]; ring

private theorem rawNuU610_factored
    (h w1 s1 u2 b62 q53 q41 q3 lambda : R) :
    rawNuU610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) (h ^ 3 * q53) (h * q41) q3 lambda =
      h ^ 32 * mergedNuU610 h w1 s1 u2 b62 q53 q41 q3 lambda := by
  simp [rawNuU610, mergedNuU610]; ring

private theorem rawNuV610_factored
    (h w1 s1 u2 b62 q53 q41 q3 q2 lambda : R) :
    rawNuV610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) (h ^ 3 * q53) (h * q41) q3 q2 lambda =
      h ^ 37 * mergedNuV610 h w1 s1 u2 b62 q53 q41 q3 q2 lambda := by
  simp [rawNuV610, mergedNuV610]; ring

private theorem rawNuW610_factored
    (h w1 s1 u2 b62 q53 q41 q3 q2 q1 lambda : R) :
    rawNuW610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) (h ^ 3 * q53) (h * q41) q3 q2 q1 lambda =
      h ^ 42 * mergedNuW610 h w1 s1 u2 b62 q53 q41 q3 q2 q1 lambda := by
  simp [rawNuW610, mergedNuW610]; ring

set_option maxHeartbeats 800000000 in
/-- Exact factorization of the source-specialized compact numerator. -/
theorem nonzeroLocalClearedFourteenthDefect610_mergedJet_factored
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 lambda : R) :
    nonzeroLocalClearedFourteenthDefect610 h (h ^ 5 * w1)
        (h ^ 3 * a41) (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1)
        (h ^ 6 * u2) (h ^ 4 * b62) (h ^ 3 * q53) (h * q41)
        q3 q2 q1 lambda =
      h ^ 63 * nonzeroFourteenthMergedJetQuotient610 h w1 a41 p32 s1 u2
        b62 q53 p2 p1 p0 q41 q3 q2 q1 lambda := by
  rw [nonzeroLocalClearedFourteenthDefect610_eq_rawBars]
  rw [rawNuA610_factored, rawNuB610_factored, rawNuC610_factored,
    rawNuD610_factored, rawNuE610_factored, rawNuP610_factored,
    rawNuQ610_factored, rawNuR610_factored, rawNuS610_factored,
    rawNuT610_factored, rawNuU610_factored, rawNuV610_factored,
    rawNuW610_factored]
  rw [mul_comm lambda (h ^ 5)]
  unfold nonzeroFourteenthMergedJetQuotient610
  apply nonzeroClearedFourteenthResidual610_mergedBar_factored

set_option maxHeartbeats 800000000 in
/-- The residue of the compact quotient is the recorded 14-term head. -/
theorem nonzeroFourteenthMergedJetQuotient610_zero
    (w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 lambda : R) :
    nonzeroFourteenthMergedJetQuotient610 0 w1 a41 p32 s1 u2 b62 q53
        p2 p1 p0 q41 q3 q2 q1 lambda =
      nonzeroFourteenthMergedJetHead610 a41 s1 b62 p2 q41 := by
  simp only [nonzeroFourteenthMergedJetQuotient610,
    nonzeroFourteenthMergedBarQuotient610, nuJetAHigh610,
    nuJetAMid610, nuJetALow610, nuJetAZero610, nuJetLambda610,
    mergedNuA610, mergedNuB610,
    mergedNuC610, mergedNuD610, mergedNuE610, mergedNuP610, mergedNuQ610,
    mergedNuR610, mergedNuS610, mergedNuT610, mergedNuU610, mergedNuV610,
    mergedNuW610, nonzeroFourteenthMergedJetHead610, zero_mul, zero_pow,
    Nat.ofNat_pos, add_zero, sub_zero]
  ring

end MergedSourceBars610

section MergedJetEvaluation610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the compact merged quotient. -/
theorem nonzeroFourteenthMergedJetQuotient610_eval
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 : k[X])
    (lambda x : k) :
    (nonzeroFourteenthMergedJetQuotient610 h w1 a41 p32 s1 u2 b62 q53
        p2 p1 p0 q41 q3 q2 q1 (Polynomial.C lambda)).eval x =
      nonzeroFourteenthMergedJetQuotient610 (h.eval x) (w1.eval x)
        (a41.eval x) (p32.eval x) (s1.eval x) (u2.eval x) (b62.eval x)
        (q53.eval x) (p2.eval x) (p1.eval x) (p0.eval x) (q41.eval x)
        (q3.eval x) (q2.eval x) (q1.eval x) lambda := by
  simp only [nonzeroFourteenthMergedJetQuotient610,
    nonzeroFourteenthMergedBarQuotient610, nuJetAHigh610,
    nuJetAMid610, nuJetALow610, nuJetAZero610, nuJetLambda610,
    mergedNuA610, mergedNuB610,
    mergedNuC610, mergedNuD610, mergedNuE610, mergedNuP610, mergedNuQ610,
    mergedNuR610, mergedNuS610, mergedNuT610, mergedNuU610, mergedNuV610,
    mergedNuW610, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_C]

set_option maxHeartbeats 800000000 in
/-- Source-facing vanishing of the order-`63` head at the same supplied
linear root. -/
theorem nonzeroFace610_fourteenthMergedHead_eval_zero
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 -
      (3 : k[X]) * q.coeff 9 = Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0)
    (w1 a41 p32 s1 u2 b62 q53 q41 : k[X])
    (hp5 : p.coeff 5 = h0 ^ 5 * w1)
    (hp4 : p.coeff 4 = h0 ^ 3 * a41)
    (hp3 : p.coeff 3 = h0 ^ 2 * p32)
    (hq8 : q.coeff 8 = h0 ^ 7 * s1)
    (hq7 : q.coeff 7 = h0 ^ 6 * u2)
    (hq6 : q.coeff 6 = h0 ^ 4 * b62)
    (hq5 : q.coeff 5 = h0 ^ 3 * q53)
    (hq4 : q.coeff 4 = h0 * q41) :
    nonzeroFourteenthMergedJetHead610 (a41.eval a) (s1.eval a)
      (b62.eval a) ((p.coeff 2).eval a) (q41.eval a) = 0 := by
  obtain ⟨nu, hpow⟩ := nonzeroFace610_fourteenthResidualPowerRelation
    p q H h0 j lambda hp hq hh0 hH hp6 hq10 hN hD
  have hpowJet :
      nonzeroLocalClearedFourteenthDefect610 h0 (h0 ^ 5 * w1)
          (h0 ^ 3 * a41) (h0 ^ 2 * p32) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (h0 ^ 7 * s1) (h0 ^ 6 * u2) (h0 ^ 4 * b62)
          (h0 ^ 3 * q53) (h0 * q41) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C nu * h0 ^ 70 := by
    rw [← hp5, ← hp4, ← hp3, ← hq8, ← hq7, ← hq6, ← hq5, ← hq4]
    exact hpow
  have hpeel :
      nonzeroFourteenthMergedJetQuotient610 h0 w1 a41 p32 s1 u2 b62 q53
          (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C nu * h0 ^ 7 := by
    have h63 : (h0 : k[X]) ^ 63 ≠ 0 := pow_ne_zero 63 hh0
    apply mul_left_cancel₀ h63
    rw [← nonzeroLocalClearedFourteenthDefect610_mergedJet_factored]
    rw [hpowJet]
    ring
  have hev := congrArg (Polynomial.eval a) hpeel
  rw [nonzeroFourteenthMergedJetQuotient610_eval, hroot,
    nonzeroFourteenthMergedJetQuotient610_zero] at hev
  have hzero : (0 : k) ^ 7 = 0 := by norm_num
  simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    hroot, hzero, mul_zero] using hev

#print axioms nonzeroClearedFourteenthResidual610_mergedBar_factored
#print axioms nonzeroLocalClearedFourteenthDefect610_mergedJet_factored
#print axioms nonzeroFourteenthMergedJetQuotient610_zero
#print axioms nonzeroFace610_fourteenthMergedHead_eval_zero

end MergedJetEvaluation610

end Max11DegreeRoutes
