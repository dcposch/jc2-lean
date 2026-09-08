import Sol610ScaleTwoNonzeroFourteenthComplementBackwireScratch

/-! # The first post-collapse `(6,10)` fourth-tail head

The four uniform divisibilities supplied by the fourteenth-complement
backwire force two further powers of the linear factor out of the order-`63`
merged quotient.  This file records that factorization through a compact
bar-coordinate interface and identifies the first surviving root head.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section PostCollapseBarQuotient610

variable {R : Type*} [CommRing R]

/-- Quotient left after removing the two uniform powers forced by
`A = h A₁`, `C = h C₁`, `D = h D₁`, `E = h E₁`, `P = h P₁`, and
`R = h R₁` from the order-`63` compact bar quotient. -/
def nonzeroFourteenthPostCollapseBarQuotient610
    (h A B C D E P Q R0 S T U V W lambda : R) : R :=
  h * (-(136080 : R) * B ^ 2 * C ^ 2 - 107520 * D * B ^ 3 -
      32256 * P * B ^ 4 + 729 * E * V + 1944 * D * W +
      44800 * A * B ^ 4 - 524880 * C * D * S -
      225792 * A * Q * B ^ 3 - 69984 * A * D * U -
      9720 * B * E * S - 6561 * A * C * V - 972 * A * E * T -
      324 * A * B * W + 17496 * C * T * A ^ 2 +
      23328 * B * U * A ^ 2 + 23328 * C * R0 * B ^ 2 +
      72576 * C * lambda * B ^ 3 + 489888 * B * Q * C ^ 2 +
      580608 * D * Q * B ^ 2 + 349920 * A * B * C * S) +
    h ^ 2 * (-(153090 : R) * A * C ^ 3 - 69984 * R0 * D ^ 2 -
      3402 * T * A ^ 4 + 1458 * V * A ^ 3 + 7290 * E * C ^ 2 +
      157464 * P * C ^ 3 + 466560 * C * D ^ 2 -
      373248 * B * lambda * D ^ 2 - 314928 * D * lambda * C ^ 2 -
      136080 * B * S * A ^ 3 - 120960 * lambda * A ^ 2 * B ^ 3 -
      54432 * D * E * Q - 27216 * R0 * A ^ 2 * B ^ 2 -
      10080 * A * E * B ^ 2 - 2187 * C * E * R0 +
      10368 * E * P * B ^ 2 + 17280 * B * D * E +
      39366 * A * R0 * C ^ 2 + 349920 * D * S * A ^ 2 +
      453600 * C * A ^ 2 * B ^ 2 - 1143072 * B * C * Q * A ^ 2 -
      1088640 * A * B * C * D - 653184 * A * C * P * B ^ 2 -
      11664 * B * C * E * lambda + 36288 * A * B * E * Q +
      93312 * A * B * D * R0 + 367416 * A * B * lambda * C ^ 2 +
      435456 * A * D * lambda * B ^ 2 + 1119744 * B * C * D * P +
      1959552 * A * C * D * Q) +
    h ^ 3 * (-(544320 : R) * A ^ 2 * D ^ 2 -
      163800 * A ^ 4 * B ^ 2 - 486 * P * E ^ 2 + 270 * A * E ^ 2 +
      255150 * A ^ 3 * C ^ 2 - 762048 * D * Q * A ^ 3 -
      551124 * P * A ^ 2 * C ^ 2 - 30618 * C * R0 * A ^ 3 -
      17010 * C * E * A ^ 2 + 1458 * E * R0 * A ^ 2 +
      317520 * B * Q * A ^ 4 + 362880 * P * A ^ 3 * B ^ 2 +
      604800 * B * D * A ^ 3 + 1119744 * A * P * D ^ 2 -
      1306368 * B * D * P * A ^ 2 -
      408240 * B * C * lambda * A ^ 3 - 23328 * A * D * E * lambda +
      13608 * B * E * lambda * A ^ 2 + 34992 * A * C * E * P +
      734832 * C * D * lambda * A ^ 2) +
    h ^ 4 * (-(110565 : R) * C * A ^ 5 + 4725 * E * A ^ 4 +
      5103 * R0 * A ^ 5 - 204120 * D * lambda * A ^ 4 -
      13608 * E * P * A ^ 3 + 88452 * B * lambda * A ^ 5 +
      306180 * C * P * A ^ 4) +
    h ^ 5 * ((14040 : R) * A ^ 7 - 44226 * P * A ^ 6) -
    13122 * T * C ^ 2 - 1944 * V * B ^ 2 + 34560 * S * B ^ 3 -
    34992 * B * C * U - 31104 * B * D * T + 10368 * A * T * B ^ 2

/-- Landed `nuJetAHigh610` body, copied so the substitution proof can unfold
it by name.  Privacy of the imported block otherwise leaves `ring` with
opaque atoms. -/
private def postCollapseBarHighUnfold610
    (h A B C0 E P Q R0 T : R) : R :=
  (14040 : R) * A ^ 7 - 44226 * A ^ 6 * P - 110565 * A ^ 5 * C0 +
    5103 * A ^ 5 * R0 - 163800 * A ^ 4 * B ^ 2 * h +
    317520 * A ^ 4 * B * Q * h + 306180 * A ^ 4 * C0 * P +
    4725 * A ^ 4 * E * h - 3402 * A ^ 4 * T

/-- Landed `nuJetAMid610` body, copied for named unfolding. -/
private def postCollapseBarMidUnfold610
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

/-- Landed `nuJetALow610` body, copied for named unfolding. -/
private def postCollapseBarLowUnfold610
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

/-- Landed `nuJetAZero610` body, copied for named unfolding. -/
private def postCollapseBarZeroUnfold610
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

/-- Landed `nuJetLambda610` body, copied for named unfolding. -/
private def postCollapseBarLambdaUnfold610
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

private theorem nonzeroFourteenthMergedBarQuotient610_unfold
    (h A B C0 D E P Q R0 S T U V W lambda : R) :
    nonzeroFourteenthMergedBarQuotient610 h A B C0 D E P Q R0 S T U V W
        lambda =
      postCollapseBarHighUnfold610 h A B C0 E P Q R0 T +
        postCollapseBarMidUnfold610 h A B C0 D E P Q R0 S T U V +
          postCollapseBarLowUnfold610 h A B C0 D E P Q R0 S T U V W +
            postCollapseBarZeroUnfold610 h B C0 D E P Q R0 S T U V W +
              postCollapseBarLambdaUnfold610 h A B C0 D E lambda := by
  delta nonzeroFourteenthMergedBarQuotient610
    postCollapseBarHighUnfold610 postCollapseBarMidUnfold610
    postCollapseBarLowUnfold610 postCollapseBarZeroUnfold610
    postCollapseBarLambdaUnfold610
  rfl

set_option maxHeartbeats 800000000 in
/-- Exact two-power factorization before the compact bar coordinates are
expanded into the source coefficients. -/
theorem nonzeroFourteenthMergedBarQuotient610_postCollapse_factored
    (h A B C0 D E P Q R0 S T U V W lambda : R) :
    nonzeroFourteenthMergedBarQuotient610 h (h * A) B (h * C0)
        (h * D) (h * E) (h * P) Q (h * R0) S T U V W lambda =
      h ^ 2 * nonzeroFourteenthPostCollapseBarQuotient610 h A B C0 D E
        P Q R0 S T U V W lambda := by
  rw [nonzeroFourteenthMergedBarQuotient610_unfold]
  simp only [postCollapseBarHighUnfold610, postCollapseBarMidUnfold610,
    postCollapseBarLowUnfold610, postCollapseBarZeroUnfold610,
    postCollapseBarLambdaUnfold610,
    nonzeroFourteenthPostCollapseBarQuotient610]
  ring

/-- The generic first head after the two-power peel. -/
def nonzeroFourteenthPostCollapseBarHead610
    (A B C D S T U V : R) : R :=
  -(13122 : R) * T * C ^ 2 - 1944 * V * B ^ 2 + 34560 * S * B ^ 3 -
    34992 * B * C * U - 31104 * B * D * T + 10368 * A * T * B ^ 2

theorem nonzeroFourteenthPostCollapseBarQuotient610_zero
    (A B C D E P Q R0 S T U V W lambda : R) :
    nonzeroFourteenthPostCollapseBarQuotient610 0 A B C D E P Q R0 S T
        U V W lambda =
      nonzeroFourteenthPostCollapseBarHead610 A B C D S T U V := by
  simp only [nonzeroFourteenthPostCollapseBarQuotient610,
    nonzeroFourteenthPostCollapseBarHead610, zero_mul, zero_pow,
    Nat.ofNat_pos, add_zero, sub_zero]
  ring

end PostCollapseBarQuotient610

section PostCollapseSourceCoordinates610

variable {R : Type*} [CommRing R]

def postCollapseNuA610 (w1 a42 : R) : R := 12 * a42 - 5 * w1 ^ 2
def postCollapseNuB610 (h w1 a42 p32 : R) : R :=
  54 * p32 + h * (-36 * a42 * w1 + 10 * w1 ^ 3)
def postCollapseNuC610 (h w1 a42 p32 p21 : R) : R :=
  144 * p21 - 72 * p32 * w1 + h * (24 * a42 * w1 ^ 2 - 5 * w1 ^ 4)
def postCollapseNuD610 (h w1 a42 p32 p21 p1 : R) : R :=
  -108 * p21 * w1 + 324 * p1 + 27 * p32 * w1 ^ 2 +
    h * (-6 * a42 * w1 ^ 3 + w1 ^ 5)
def postCollapseNuE610 (h w1 a42 p32 p21 p1 p0 : R) : R :=
  1296 * p21 * w1 ^ 2 - 7776 * p1 * w1 - 216 * p32 * w1 ^ 3 +
    h * (36 * a42 * w1 ^ 4 + 46656 * p0 - 5 * w1 ^ 6)
def postCollapseNuP610 (w1 s2 lambda : R) : R :=
  4 * s2 + 2 * lambda * w1 - 5 * w1 ^ 2
def postCollapseNuQ610 (h w1 s2 u2 lambda : R) : R :=
  9 * u2 + h * (-12 * s2 * w1 - 3 * lambda * w1 ^ 2 + 10 * w1 ^ 3)
def postCollapseNuR610 (h w1 s2 u2 b63 lambda : R) : R :=
  432 * b63 - 504 * u2 * w1 +
    h * (336 * s2 * w1 ^ 2 + 56 * lambda * w1 ^ 3 - 210 * w1 ^ 4)
def postCollapseNuS610 (h w1 s2 u2 b63 q53 lambda : R) : R :=
  216 * q53 + h * (-216 * b63 * w1 + 126 * u2 * w1 ^ 2) +
    h ^ 2 * (-56 * s2 * w1 ^ 3 - 7 * lambda * w1 ^ 4 + 28 * w1 ^ 5)
def postCollapseNuT610 (h w1 s2 u2 b63 q53 q41 lambda : R) : R :=
  7776 * q41 - 6480 * h * q53 * w1 +
    h ^ 2 * (3240 * b63 * w1 ^ 2 - 1260 * u2 * w1 ^ 3) +
    h ^ 3 * (420 * s2 * w1 ^ 4 + 42 * lambda * w1 ^ 5 - 175 * w1 ^ 6)
def postCollapseNuU610
    (h w1 s2 u2 b63 q53 q41 q3 lambda : R) : R :=
  11664 * q3 - 7776 * q41 * w1 + 3240 * h * q53 * w1 ^ 2 +
    h ^ 2 * (-1080 * b63 * w1 ^ 3 + 315 * u2 * w1 ^ 4) +
    h ^ 3 * (-84 * s2 * w1 ^ 5 - 7 * lambda * w1 ^ 6 + 30 * w1 ^ 7)
def postCollapseNuV610
    (h w1 s2 u2 b63 q53 q41 q3 q2 lambda : R) : R :=
  -93312 * q3 * w1 + 31104 * q41 * w1 ^ 2 +
    h * (186624 * q2 - 8640 * q53 * w1 ^ 3) +
    h ^ 2 * (2160 * b63 * w1 ^ 4 - 504 * u2 * w1 ^ 5) +
    h ^ 3 * (112 * s2 * w1 ^ 6 + 8 * lambda * w1 ^ 7 - 35 * w1 ^ 8)
def postCollapseNuW610
    (h w1 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) : R :=
  419904 * q3 * w1 ^ 2 - 93312 * q41 * w1 ^ 3 +
    h * (-1679616 * q2 * w1 + 19440 * q53 * w1 ^ 4) +
    h ^ 2 * (-3888 * b63 * w1 ^ 5 + 5038848 * q1 +
      756 * u2 * w1 ^ 6) +
    h ^ 3 * (-144 * s2 * w1 ^ 7 - 9 * lambda * w1 ^ 8 + 40 * w1 ^ 9)

/-- The order-`65` quotient on the four-times-deepened source jet. -/
def nonzeroFourteenthPostCollapseJetQuotient610
    (h w1 a42 p32 s2 u2 b63 q53 p21 p1 p0 q41 q3 q2 q1 lambda : R) : R :=
  nonzeroFourteenthPostCollapseBarQuotient610 h
    (postCollapseNuA610 w1 a42)
    (postCollapseNuB610 h w1 a42 p32)
    (postCollapseNuC610 h w1 a42 p32 p21)
    (postCollapseNuD610 h w1 a42 p32 p21 p1)
    (postCollapseNuE610 h w1 a42 p32 p21 p1 p0)
    (postCollapseNuP610 w1 s2 lambda)
    (postCollapseNuQ610 h w1 s2 u2 lambda)
    (postCollapseNuR610 h w1 s2 u2 b63 lambda)
    (postCollapseNuS610 h w1 s2 u2 b63 q53 lambda)
    (postCollapseNuT610 h w1 s2 u2 b63 q53 q41 lambda)
    (postCollapseNuU610 h w1 s2 u2 b63 q53 q41 q3 lambda)
    (postCollapseNuV610 h w1 s2 u2 b63 q53 q41 q3 q2 lambda)
    (postCollapseNuW610 h w1 s2 u2 b63 q53 q41 q3 q2 q1 lambda) lambda

private theorem postCollapseNuA610_factored
    (h w1 a42 : R) :
    mergedNuA610 h w1 (h * a42) = h * postCollapseNuA610 w1 a42 := by
  simp only [mergedNuA610, postCollapseNuA610]
  ring

private theorem postCollapseNuB610_eq
    (h w1 a42 p32 : R) :
    mergedNuB610 h w1 (h * a42) p32 =
      postCollapseNuB610 h w1 a42 p32 := by
  simp only [mergedNuB610, postCollapseNuB610]
  ring

private theorem postCollapseNuC610_factored
    (h w1 a42 p32 p21 : R) :
    mergedNuC610 h w1 (h * a42) p32 (h * p21) =
      h * postCollapseNuC610 h w1 a42 p32 p21 := by
  simp only [mergedNuC610, postCollapseNuC610]
  ring

private theorem postCollapseNuD610_factored
    (h w1 a42 p32 p21 p1 : R) :
    mergedNuD610 h w1 (h * a42) p32 (h * p21) p1 =
      h * postCollapseNuD610 h w1 a42 p32 p21 p1 := by
  simp only [mergedNuD610, postCollapseNuD610]
  ring

private theorem postCollapseNuE610_factored
    (h w1 a42 p32 p21 p1 p0 : R) :
    mergedNuE610 h w1 (h * a42) p32 (h * p21) p1 p0 =
      h * postCollapseNuE610 h w1 a42 p32 p21 p1 p0 := by
  simp only [mergedNuE610, postCollapseNuE610]
  ring

private theorem postCollapseNuP610_factored
    (h w1 s2 lambda : R) :
    mergedNuP610 h w1 (h * s2) lambda =
      h * postCollapseNuP610 w1 s2 lambda := by
  simp only [mergedNuP610, postCollapseNuP610]
  ring

private theorem postCollapseNuQ610_eq
    (h w1 s2 u2 lambda : R) :
    mergedNuQ610 h w1 (h * s2) u2 lambda =
      postCollapseNuQ610 h w1 s2 u2 lambda := by
  simp only [mergedNuQ610, postCollapseNuQ610]
  ring

private theorem postCollapseNuR610_factored
    (h w1 s2 u2 b63 lambda : R) :
    mergedNuR610 h w1 (h * s2) u2 (h * b63) lambda =
      h * postCollapseNuR610 h w1 s2 u2 b63 lambda := by
  simp only [mergedNuR610, postCollapseNuR610]
  ring

private theorem postCollapseNuS610_eq
    (h w1 s2 u2 b63 q53 lambda : R) :
    mergedNuS610 h w1 (h * s2) u2 (h * b63) q53 lambda =
      postCollapseNuS610 h w1 s2 u2 b63 q53 lambda := by
  simp only [mergedNuS610, postCollapseNuS610]
  ring

private theorem postCollapseNuT610_eq
    (h w1 s2 u2 b63 q53 q41 lambda : R) :
    mergedNuT610 h w1 (h * s2) u2 (h * b63) q53 q41 lambda =
      postCollapseNuT610 h w1 s2 u2 b63 q53 q41 lambda := by
  simp only [mergedNuT610, postCollapseNuT610]
  ring

private theorem postCollapseNuU610_eq
    (h w1 s2 u2 b63 q53 q41 q3 lambda : R) :
    mergedNuU610 h w1 (h * s2) u2 (h * b63) q53 q41 q3 lambda =
      postCollapseNuU610 h w1 s2 u2 b63 q53 q41 q3 lambda := by
  simp only [mergedNuU610, postCollapseNuU610]
  ring

private theorem postCollapseNuV610_eq
    (h w1 s2 u2 b63 q53 q41 q3 q2 lambda : R) :
    mergedNuV610 h w1 (h * s2) u2 (h * b63) q53 q41 q3 q2 lambda =
      postCollapseNuV610 h w1 s2 u2 b63 q53 q41 q3 q2 lambda := by
  simp only [mergedNuV610, postCollapseNuV610]
  ring

private theorem postCollapseNuW610_eq
    (h w1 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) :
    mergedNuW610 h w1 (h * s2) u2 (h * b63) q53 q41 q3 q2 q1 lambda =
      postCollapseNuW610 h w1 s2 u2 b63 q53 q41 q3 q2 q1 lambda := by
  simp only [mergedNuW610, postCollapseNuW610]
  ring

set_option maxHeartbeats 800000000 in
/-- Exact order-`65` source-jet factorization. -/
theorem nonzeroFourteenthMergedJetQuotient610_postCollapse_factored
    (h w1 a42 p32 s2 u2 b63 q53 p21 p1 p0 q41 q3 q2 q1 lambda : R) :
    nonzeroFourteenthMergedJetQuotient610 h w1 (h * a42) p32 (h * s2)
        u2 (h * b63) q53 (h * p21) p1 p0 q41 q3 q2 q1 lambda =
      h ^ 2 * nonzeroFourteenthPostCollapseJetQuotient610 h w1 a42 p32
        s2 u2 b63 q53 p21 p1 p0 q41 q3 q2 q1 lambda := by
  simp only [nonzeroFourteenthMergedJetQuotient610,
    nonzeroFourteenthPostCollapseJetQuotient610]
  rw [postCollapseNuA610_factored, postCollapseNuB610_eq,
    postCollapseNuC610_factored, postCollapseNuD610_factored,
    postCollapseNuE610_factored, postCollapseNuP610_factored,
    postCollapseNuQ610_eq, postCollapseNuR610_factored,
    postCollapseNuS610_eq, postCollapseNuT610_eq, postCollapseNuU610_eq,
    postCollapseNuV610_eq, postCollapseNuW610_eq]
  exact nonzeroFourteenthMergedBarQuotient610_postCollapse_factored
    h (postCollapseNuA610 w1 a42) (postCollapseNuB610 h w1 a42 p32)
      (postCollapseNuC610 h w1 a42 p32 p21)
      (postCollapseNuD610 h w1 a42 p32 p21 p1)
      (postCollapseNuE610 h w1 a42 p32 p21 p1 p0)
      (postCollapseNuP610 w1 s2 lambda)
      (postCollapseNuQ610 h w1 s2 u2 lambda)
      (postCollapseNuR610 h w1 s2 u2 b63 lambda)
      (postCollapseNuS610 h w1 s2 u2 b63 q53 lambda)
      (postCollapseNuT610 h w1 s2 u2 b63 q53 q41 lambda)
      (postCollapseNuU610 h w1 s2 u2 b63 q53 q41 q3 lambda)
      (postCollapseNuV610 h w1 s2 u2 b63 q53 q41 q3 q2 lambda)
      (postCollapseNuW610 h w1 s2 u2 b63 q53 q41 q3 q2 q1 lambda)
      lambda

/-- Compact first nonzero source head after the two-power peel. -/
def nonzeroFourteenthPostCollapseJetHead610
    (w1 a42 p32 q53 p21 p1 q41 q3 : R) : R :=
  (117546246144 : R) *
    (24 * a42 * p32 ^ 2 * q41 - 36 * p1 * p32 * q41 -
      18 * p21 ^ 2 * q41 - 27 * p21 * p32 * q3 +
      48 * p21 * p32 * q41 * w1 + 10 * p32 ^ 3 * q53 +
      18 * p32 ^ 2 * q3 * w1 - 28 * p32 ^ 2 * q41 * w1 ^ 2)

set_option maxHeartbeats 800000000 in
theorem nonzeroFourteenthPostCollapseJetQuotient610_zero
    (w1 a42 p32 s2 u2 b63 q53 p21 p1 p0 q41 q3 q2 q1 lambda : R) :
    nonzeroFourteenthPostCollapseJetQuotient610 0 w1 a42 p32 s2 u2 b63
        q53 p21 p1 p0 q41 q3 q2 q1 lambda =
      nonzeroFourteenthPostCollapseJetHead610 w1 a42 p32 q53 p21 p1 q41
        q3 := by
  simp only [nonzeroFourteenthPostCollapseJetQuotient610,
    postCollapseNuA610, postCollapseNuB610, postCollapseNuC610,
    postCollapseNuD610, postCollapseNuE610, postCollapseNuP610,
    postCollapseNuQ610, postCollapseNuR610, postCollapseNuS610,
    postCollapseNuT610, postCollapseNuU610, postCollapseNuV610,
    postCollapseNuW610, zero_mul, add_zero]
  rw [nonzeroFourteenthPostCollapseBarQuotient610_zero]
  simp only [nonzeroFourteenthPostCollapseBarHead610,
    nonzeroFourteenthPostCollapseJetHead610]
  ring

end PostCollapseSourceCoordinates610

section PostCollapseSourceHead610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the compact post-collapse quotient. -/
theorem nonzeroFourteenthPostCollapseJetQuotient610_eval
    (h w1 a42 p32 s2 u2 b63 q53 p21 p1 p0 q41 q3 q2 q1 : k[X])
    (lambda x : k) :
    (nonzeroFourteenthPostCollapseJetQuotient610 h w1 a42 p32 s2 u2
        b63 q53 p21 p1 p0 q41 q3 q2 q1 (Polynomial.C lambda)).eval x =
      nonzeroFourteenthPostCollapseJetQuotient610 (h.eval x) (w1.eval x)
        (a42.eval x) (p32.eval x) (s2.eval x) (u2.eval x) (b63.eval x)
        (q53.eval x) (p21.eval x) (p1.eval x) (p0.eval x) (q41.eval x)
        (q3.eval x) (q2.eval x) (q1.eval x) lambda := by
  simp only [nonzeroFourteenthPostCollapseJetQuotient610,
    nonzeroFourteenthPostCollapseBarQuotient610, postCollapseNuA610,
    postCollapseNuB610, postCollapseNuC610, postCollapseNuD610,
    postCollapseNuE610, postCollapseNuP610, postCollapseNuQ610,
    postCollapseNuR610, postCollapseNuS610, postCollapseNuT610,
    postCollapseNuU610, postCollapseNuV610, postCollapseNuW610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

set_option maxHeartbeats 800000000 in
/-- Source-facing order-`65` residual packet.  The complement backwire
provides the four deep coefficients; the order-`63` power relation then
cancels two more powers and forces the new head to vanish at the supplied
linear root. -/
theorem nonzeroFace610_linearRoot_postCollapseResidual
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a42 p32 p21 s2 u2 b63 q53 q41 : k[X]) (nu : k),
      p.coeff 5 = h0 ^ 5 * w1 ∧
      p.coeff 4 = h0 ^ 4 * a42 ∧
      p.coeff 3 = h0 ^ 2 * p32 ∧
      p.coeff 2 = h0 * p21 ∧
      q.coeff 8 = h0 ^ 8 * s2 ∧
      q.coeff 7 = h0 ^ 6 * u2 ∧
      q.coeff 6 = h0 ^ 5 * b63 ∧
      q.coeff 5 = h0 ^ 3 * q53 ∧
      q.coeff 4 = h0 * q41 ∧
      nonzeroFourteenthPostCollapseJetQuotient610 h0 w1 a42 p32 s2 u2
          b63 q53 p21 (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C nu * h0 ^ 5 ∧
      nonzeroFourteenthPostCollapseJetHead610 (w1.eval a) (a42.eval a)
          (p32.eval a) (q53.eval a) (p21.eval a) ((p.coeff 1).eval a)
          (q41.eval a) ((q.coeff 3).eval a) = 0 := by
  obtain ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, hw, hp4deep,
      hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep⟩ :=
    nonzeroFace610_linearRoot_fourteenthComplementBackwire p q H h0 j
      lambda a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  obtain ⟨nu, hpow⟩ := nonzeroFace610_fourteenthResidualPowerRelation
    p q H h0 j lambda hp hq hh0 hH hp6 hq10 hN hD
  have hp4old : p.coeff 4 = h0 ^ 3 * (h0 * a42) := by
    rw [hp4deep]
    ring
  have hp2old : p.coeff 2 = h0 * p21 := hp2deep
  have hq8old : q.coeff 8 = h0 ^ 7 * (h0 * s2) := by
    rw [hq8deep]
    ring
  have hq6old : q.coeff 6 = h0 ^ 4 * (h0 * b63) := by
    rw [hq6deep]
    ring
  have hpowJet :
      nonzeroLocalClearedFourteenthDefect610 h0 (h0 ^ 5 * w1)
          (h0 ^ 3 * (h0 * a42)) (h0 ^ 2 * p32) (h0 * p21)
          (p.coeff 1) (p.coeff 0) (h0 ^ 7 * (h0 * s2))
          (h0 ^ 6 * u2) (h0 ^ 4 * (h0 * b63)) (h0 ^ 3 * q53)
          (h0 * q41) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) = Polynomial.C nu * h0 ^ 70 := by
    rw [← hw, ← hp4old, ← hp3deep, ← hp2old, ← hq8old, ← hq7deep,
      ← hq6old, ← hq5deep, ← hq4deep]
    exact hpow
  have hpeel63 :
      nonzeroFourteenthMergedJetQuotient610 h0 w1 (h0 * a42) p32
          (h0 * s2) u2 (h0 * b63) q53 (h0 * p21) (p.coeff 1)
          (p.coeff 0) q41 (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) = Polynomial.C nu * h0 ^ 7 := by
    have h63 : (h0 : k[X]) ^ 63 ≠ 0 := pow_ne_zero 63 hh0
    apply mul_left_cancel₀ h63
    rw [← nonzeroLocalClearedFourteenthDefect610_mergedJet_factored]
    rw [hpowJet]
    ring
  have hpost :
      nonzeroFourteenthPostCollapseJetQuotient610 h0 w1 a42 p32 s2 u2
          b63 q53 p21 (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C nu * h0 ^ 5 := by
    have h2 : (h0 : k[X]) ^ 2 ≠ 0 := pow_ne_zero 2 hh0
    apply mul_left_cancel₀ h2
    rw [← nonzeroFourteenthMergedJetQuotient610_postCollapse_factored]
    rw [hpeel63]
    ring
  have hhead :
      nonzeroFourteenthPostCollapseJetHead610 (w1.eval a) (a42.eval a)
          (p32.eval a) (q53.eval a) (p21.eval a) ((p.coeff 1).eval a)
          (q41.eval a) ((q.coeff 3).eval a) = 0 := by
    have hev := congrArg (Polynomial.eval a) hpost
    rw [nonzeroFourteenthPostCollapseJetQuotient610_eval, hroot,
      nonzeroFourteenthPostCollapseJetQuotient610_zero] at hev
    have hzero : (0 : k) ^ 5 = 0 := by norm_num
    simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      hroot, hzero, mul_zero] using hev
  exact ⟨w1, a42, p32, p21, s2, u2, b63, q53, q41, nu, hw, hp4deep,
    hp3deep, hp2deep, hq8deep, hq7deep, hq6deep, hq5deep, hq4deep, hpost,
    hhead⟩

#print axioms nonzeroFourteenthMergedBarQuotient610_postCollapse_factored
#print axioms nonzeroFourteenthMergedJetQuotient610_postCollapse_factored
#print axioms nonzeroFourteenthPostCollapseJetQuotient610_zero
#print axioms nonzeroFace610_linearRoot_postCollapseResidual

end PostCollapseSourceHead610

end Max11DegreeRoutes
