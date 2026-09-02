import Sol610ScaleTwoAlignedFourteenthResidualConstantBridgeScratch

/-! # Compact nonzero-face clearing for the `(6,10)` fourth tail

The aligned numerator already contains the 72 terms independent of the
ninth-power parameter.  The exact CAS certificate adds only the thirteen
terms below.  Keeping those terms in depressed bar coordinates avoids the
huge source-expanded polynomial while retaining the supplied `h` and
`lambda` witnesses.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section CompactNonzeroNumerator610

variable {R : Type*} [CommRing R]

/-- The 85-term integral numerator of the nonzero-face weight-seventy
residual.  It is the verified 72-term aligned numerator plus the thirteen
terms linear in the weight-five bar coordinate `lambdaBar`. -/
def nonzeroClearedFourteenthResidual610
    (A B C0 D E P Q R0 S T U V W lambdaBar : R) : R :=
  clearedFourteenthResidual610 A B C0 D E P Q R0 S T U V W
    + (88452 : R) * A ^ 5 * B * lambdaBar
    - (204120 : R) * A ^ 4 * D * lambdaBar
    - (408240 : R) * A ^ 3 * B * C0 * lambdaBar
    - (120960 : R) * A ^ 2 * B ^ 3 * lambdaBar
    + (13608 : R) * A ^ 2 * B * E * lambdaBar
    + (734832 : R) * A ^ 2 * C0 * D * lambdaBar
    + (435456 : R) * A * B ^ 2 * D * lambdaBar
    + (367416 : R) * A * B * C0 ^ 2 * lambdaBar
    - (23328 : R) * A * D * E * lambdaBar
    + (72576 : R) * B ^ 3 * C0 * lambdaBar
    - (11664 : R) * B * C0 * E * lambdaBar
    - (373248 : R) * B * D ^ 2 * lambdaBar
    - (314928 : R) * C0 ^ 2 * D * lambdaBar

/-- Source-coordinate specialization of the compact numerator.  In
particular the parameter is `lambda * h^5`, its weight-five bar coordinate;
the definition does not expand the resulting source polynomial. -/
def nonzeroLocalClearedFourteenthDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
  let A := (12 : R) * a4 * h ^ 6 - 5 * a5 ^ 2
  let B := (54 : R) * a3 * h ^ 12 - 36 * a4 * a5 * h ^ 6 + 10 * a5 ^ 3
  let C0 := (144 : R) * a2 * h ^ 18 - 72 * a3 * a5 * h ^ 12 +
    24 * a4 * a5 ^ 2 * h ^ 6 - 5 * a5 ^ 4
  let D := (324 : R) * a1 * h ^ 24 - 108 * a2 * a5 * h ^ 18 +
    27 * a3 * a5 ^ 2 * h ^ 12 - 6 * a4 * a5 ^ 3 * h ^ 6 + a5 ^ 5
  let E := (46656 : R) * a0 * h ^ 30 - 7776 * a1 * a5 * h ^ 24 +
    1296 * a2 * a5 ^ 2 * h ^ 18 - 216 * a3 * a5 ^ 3 * h ^ 12 +
    36 * a4 * a5 ^ 4 * h ^ 6 - 5 * a5 ^ 6
  let P := -(5 : R) * a5 ^ 2 + 2 * lambda * a5 * h ^ 5 + 4 * b8 * h ^ 2
  let Q := (10 : R) * a5 ^ 3 - 3 * lambda * a5 ^ 2 * h ^ 5 -
    12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8
  let R0 := -(210 : R) * a5 ^ 4 + 56 * lambda * a5 ^ 3 * h ^ 5 +
    336 * a5 ^ 2 * b8 * h ^ 2 - 504 * a5 * b7 * h ^ 8 +
    432 * b6 * h ^ 14
  let S := (28 : R) * a5 ^ 5 - 7 * lambda * a5 ^ 4 * h ^ 5 -
    56 * a5 ^ 3 * b8 * h ^ 2 + 126 * a5 ^ 2 * b7 * h ^ 8 -
    216 * a5 * b6 * h ^ 14 + 216 * b5 * h ^ 20
  let T := -(175 : R) * a5 ^ 6 + 42 * lambda * a5 ^ 5 * h ^ 5 +
    420 * a5 ^ 4 * b8 * h ^ 2 - 1260 * a5 ^ 3 * b7 * h ^ 8 +
    3240 * a5 ^ 2 * b6 * h ^ 14 - 6480 * a5 * b5 * h ^ 20 +
    7776 * b4 * h ^ 26
  let U := (30 : R) * a5 ^ 7 - 7 * lambda * a5 ^ 6 * h ^ 5 -
    84 * a5 ^ 5 * b8 * h ^ 2 + 315 * a5 ^ 4 * b7 * h ^ 8 -
    1080 * a5 ^ 3 * b6 * h ^ 14 + 3240 * a5 ^ 2 * b5 * h ^ 20 -
    7776 * a5 * b4 * h ^ 26 + 11664 * b3 * h ^ 32
  let V := -(35 : R) * a5 ^ 8 + 8 * lambda * a5 ^ 7 * h ^ 5 +
    112 * a5 ^ 6 * b8 * h ^ 2 - 504 * a5 ^ 5 * b7 * h ^ 8 +
    2160 * a5 ^ 4 * b6 * h ^ 14 - 8640 * a5 ^ 3 * b5 * h ^ 20 +
    31104 * a5 ^ 2 * b4 * h ^ 26 - 93312 * a5 * b3 * h ^ 32 +
    186624 * b2 * h ^ 38
  let W := (40 : R) * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
    144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
    3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
    93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
    1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44
  nonzeroClearedFourteenthResidual610 A B C0 D E P Q R0 S T U V W
    (lambda * h ^ 5)

end CompactNonzeroNumerator610

section CompactNonzeroClearing610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- Exact denominator-free CAS identity in depressed bar coordinates. -/
theorem fourteenthResidual610_eq_nonzeroCompact
    (A B C0 D E P Q R0 S T U V W lambda : F) :
    (19042491875328 : F) *
        fourteenthResidual610 (-lambda / 3)
          (A / 12) (B / 54) (C0 / 144) (D / 324) (E / 46656)
          (P / 4) (Q / 9) (R0 / 432) (S / 216) (T / 7776)
          (U / 11664) (V / 186624) (W / 5038848) =
      nonzeroClearedFourteenthResidual610 A B C0 D E P Q R0 S T U V W
        lambda := by
  simp only [fourteenthResidual610, rawFourthTailCoefficient610,
    rawFourthTailPure610, rawFourthTailLBlock610,
    rawFourthTailAlphaBlock610, rawFourthTailBetaBlock610,
    rawFourthTailDeltaBlock610, rawFourthTailEpsilonBlock610,
    rawFourthTailEtaBlock610, rawFourthTailThetaBlock610,
    rawFourthTailZetaBlock610, alphaResidual610, betaResidual610,
    gammaResidual610, deltaResidual610, epsilonResidual610,
    zetaResidual610, etaResidual610, thetaResidual610,
    kappaResidual610, lambdaResidual610,
    nonzeroClearedFourteenthResidual610, clearedFourteenthResidual610]
  ring

set_option maxHeartbeats 800000000 in
/-- Weight-seventy homogeneity of the compact numerator. -/
theorem nonzeroClearedFourteenthResidual610_div_h
    (h A B C0 D E P Q R0 S T U V W lambda : F) (hh : h ≠ 0) :
    h ^ 70 *
        nonzeroClearedFourteenthResidual610
          (A / h ^ 10) (B / h ^ 15) (C0 / h ^ 20) (D / h ^ 25)
          (E / h ^ 30) (P / h ^ 10) (Q / h ^ 15) (R0 / h ^ 20)
          (S / h ^ 25) (T / h ^ 30) (U / h ^ 35) (V / h ^ 40)
          (W / h ^ 45) lambda =
      nonzeroClearedFourteenthResidual610 A B C0 D E P Q R0 S T U V W
        (lambda * h ^ 5) := by
  simp only [nonzeroClearedFourteenthResidual610,
    clearedFourteenthResidual610]
  field_simp [hh]

/-- Exact numerical and `h`-power clearing on arbitrary nonzero-face bar
coordinates. -/
theorem fourteenthResidual610_eq_nonzeroCleared
    (h A B C0 D E P Q R0 S T U V W lambda : F) (hh : h ≠ 0) :
    (19042491875328 : F) * h ^ 70 *
        fourteenthResidual610 (-lambda / 3)
          (A / (12 * h ^ 10)) (B / (54 * h ^ 15))
          (C0 / (144 * h ^ 20)) (D / (324 * h ^ 25))
          (E / (46656 * h ^ 30)) (P / (4 * h ^ 10))
          (Q / (9 * h ^ 15)) (R0 / (432 * h ^ 20))
          (S / (216 * h ^ 25)) (T / (7776 * h ^ 30))
          (U / (11664 * h ^ 35)) (V / (186624 * h ^ 40))
          (W / (5038848 * h ^ 45)) =
      nonzeroClearedFourteenthResidual610 A B C0 D E P Q R0 S T U V W
        (lambda * h ^ 5) := by
  have hcompact := fourteenthResidual610_eq_nonzeroCompact
    (A / h ^ 10) (B / h ^ 15) (C0 / h ^ 20) (D / h ^ 25)
    (E / h ^ 30) (P / h ^ 10) (Q / h ^ 15) (R0 / h ^ 20)
    (S / h ^ 25) (T / h ^ 30) (U / h ^ 35) (V / h ^ 40)
    (W / h ^ 45) lambda
  have hhom := nonzeroClearedFourteenthResidual610_div_h
    h A B C0 D E P Q R0 S T U V W lambda hh
  have hcompact' :
      (19042491875328 : F) *
          fourteenthResidual610 (-lambda / 3)
            (A / (12 * h ^ 10)) (B / (54 * h ^ 15))
            (C0 / (144 * h ^ 20)) (D / (324 * h ^ 25))
            (E / (46656 * h ^ 30)) (P / (4 * h ^ 10))
            (Q / (9 * h ^ 15)) (R0 / (432 * h ^ 20))
            (S / (216 * h ^ 25)) (T / (7776 * h ^ 30))
            (U / (11664 * h ^ 35)) (V / (186624 * h ^ 40))
            (W / (5038848 * h ^ 45)) =
        nonzeroClearedFourteenthResidual610
          (A / h ^ 10) (B / h ^ 15) (C0 / h ^ 20) (D / h ^ 25)
          (E / h ^ 30) (P / h ^ 10) (Q / h ^ 15) (R0 / h ^ 20)
          (S / h ^ 25) (T / h ^ 30) (U / h ^ 35) (V / h ^ 40)
          (W / h ^ 45) lambda := by
    convert hcompact using 1 <;> field_simp [hh]
  calc
    (19042491875328 : F) * h ^ 70 *
          fourteenthResidual610 (-lambda / 3)
            (A / (12 * h ^ 10)) (B / (54 * h ^ 15))
            (C0 / (144 * h ^ 20)) (D / (324 * h ^ 25))
            (E / (46656 * h ^ 30)) (P / (4 * h ^ 10))
            (Q / (9 * h ^ 15)) (R0 / (432 * h ^ 20))
            (S / (216 * h ^ 25)) (T / (7776 * h ^ 30))
            (U / (11664 * h ^ 35)) (V / (186624 * h ^ 40))
            (W / (5038848 * h ^ 45)) =
        h ^ 70 * ((19042491875328 : F) *
          fourteenthResidual610 (-lambda / 3)
            (A / (12 * h ^ 10)) (B / (54 * h ^ 15))
            (C0 / (144 * h ^ 20)) (D / (324 * h ^ 25))
            (E / (46656 * h ^ 30)) (P / (4 * h ^ 10))
            (Q / (9 * h ^ 15)) (R0 / (432 * h ^ 20))
            (S / (216 * h ^ 25)) (T / (7776 * h ^ 30))
            (U / (11664 * h ^ 35)) (V / (186624 * h ^ 40))
            (W / (5038848 * h ^ 45))) := by ring
    _ = h ^ 70 * nonzeroClearedFourteenthResidual610
          (A / h ^ 10) (B / h ^ 15) (C0 / h ^ 20) (D / h ^ 25)
          (E / h ^ 30) (P / h ^ 10) (Q / h ^ 15) (R0 / h ^ 20)
          (S / h ^ 25) (T / h ^ 30) (U / h ^ 35) (V / h ^ 40)
          (W / h ^ 45) lambda := by rw [hcompact']
    _ = nonzeroClearedFourteenthResidual610 A B C0 D E P Q R0 S T U V W
          (lambda * h ^ 5) := hhom

/-- Exact source-coordinate clearing on the supplied ninth-power witness.
No polynomial source or square-core witness is reselected. -/
theorem fourteenthDefect_eq_nonzeroClearedNu610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (19042491875328 : F) * h ^ 70 *
        fourteenthResidual610
          (depressedL610 h (sexticDepressionR610 h a5) b9)
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
          (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
          (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
          (depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1)
          (depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 a0)
          (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
          (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7)
          (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6)
          (depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5)
          (depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4)
          (depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3)
          (depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3 b2)
          (depressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6
            b5 b4 b3 b2 b1) =
      nonzeroLocalClearedFourteenthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7
        b6 b5 b4 b3 b2 b1 lambda := by
  have hL := depressedL610_eq_of_ninthPower h a5 b9 lambda hh hN
  have hA := depressedA610_eq_cleared h a5 a4 hh
  have hB := depressedB610_eq_cleared h a5 a4 a3 hh
  have hC := depressedC610_eq_cleared h a5 a4 a3 a2 hh
  have hD := depressedD610_eq_cleared h a5 a4 a3 a2 a1 hh
  have hE := depressedE610_eq_cleared h a5 a4 a3 a2 a1 a0 hh
  have hP := depressedP610_eq_cleared_ninthPower h a5 b9 b8 lambda hh hN
  have hQ := depressedQ610_eq_cleared h a5 b9 b8 b7 lambda hh hN
  have hR := depressedR610_eq_cleared h a5 b9 b8 b7 b6 lambda hh hN
  have hS := depressedS610_eq_cleared h a5 b9 b8 b7 b6 b5 lambda hh hN
  have hT := depressedT610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 lambda hh hN
  have hU := depressedU610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  have hV := depressedV610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh hN
  have hW := depressedW610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2
    b1 lambda hh hN
  rw [hL, hA, hB, hC, hD, hE, hP, hQ, hR, hS, hT, hU, hV, hW]
  unfold nonzeroLocalClearedFourteenthDefect610
  apply fourteenthResidual610_eq_nonzeroCleared
  exact hh

#print axioms fourteenthResidual610_eq_nonzeroCompact
#print axioms nonzeroClearedFourteenthResidual610_div_h
#print axioms fourteenthResidual610_eq_nonzeroCleared
#print axioms fourteenthDefect_eq_nonzeroClearedNu610

end CompactNonzeroClearing610

end Max11DegreeRoutes
