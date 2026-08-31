import Sol610ScaleTwoDegreeZeroPrimitiveScratch

/-! # Compact source numerator of the `(6,10)` degree-zero primitive

This is the integer 103-term compact numerator obtained after clearing the
standard depressed-coordinate denominators.  It is kept separate from the
differential certificate so source jets can use it over arbitrary
commutative rings.
-/

noncomputable section

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section DegreeZeroCompact610

variable {R : Type*} [CommRing R]

def degreeZeroClearedCompact610
    (A B C0 D0 E0 P Q R0 S0 T0 U0 V0 W0 lambda : R) : R :=
  -(27909765 : R) * A ^ 7 * lambda + 144717300 * A ^ 6 * B -
    117641160 * A ^ 6 * Q - 403341120 * A ^ 5 * B * P +
    226879380 * A ^ 5 * C0 * lambda - 336117600 * A ^ 5 * D0 +
    60501168 * A ^ 5 * S0 + 336117600 * A ^ 4 * B ^ 2 * lambda -
    840294000 * A ^ 4 * B * C0 + 40334112 * A ^ 4 * B * R0 +
    847016352 * A ^ 4 * C0 * Q + 968018688 * A ^ 4 * D0 * P -
    10083528 * A ^ 4 * E0 * lambda - 12737088 * A ^ 4 * U0 -
    331968000 * A ^ 3 * B ^ 3 + 1003871232 * A ^ 3 * B ^ 2 * Q +
    1936037376 * A ^ 3 * B * C0 * P -
    1290691584 * A ^ 3 * B * D0 * lambda + 29877120 * A ^ 3 * B * E0 -
    22643712 * A ^ 3 * B * T0 - 544510512 * A ^ 3 * C0 ^ 2 * lambda +
    1613364480 * A ^ 3 * C0 * D0 - 382112640 * A ^ 3 * C0 * S0 -
    101896704 * A ^ 3 * D0 * R0 - 39626496 * A ^ 3 * E0 * Q +
    217728 * A ^ 3 * W0 + 573640704 * A ^ 2 * B ^ 3 * P -
    968018688 * A ^ 2 * B ^ 2 * C0 * lambda +
    1434101760 * A ^ 2 * B ^ 2 * D0 - 339655680 * A ^ 2 * B ^ 2 * S0 +
    1210023360 * A ^ 2 * B * C0 ^ 2 - 152845056 * A ^ 2 * B * C0 * R0 -
    3804143616 * A ^ 2 * B * D0 * Q - 67931136 * A ^ 2 * B * E0 * P +
    7838208 * A ^ 2 * B * V0 - 1604873088 * A ^ 2 * C0 ^ 2 * Q -
    3668281344 * A ^ 2 * C0 * D0 * P +
    38211264 * A ^ 2 * C0 * E0 * lambda + 70543872 * A ^ 2 * C0 * U0 +
    1222760448 * A ^ 2 * D0 ^ 2 * lambda - 56609280 * A ^ 2 * D0 * E0 +
    62705664 * A ^ 2 * D0 * T0 + 19595520 * A ^ 2 * E0 * S0 -
    95606784 * A * B ^ 4 * lambda + 478033920 * A * B ^ 3 * C0 -
    30191616 * A * B ^ 3 * R0 - 1902071808 * A * B ^ 2 * C0 * Q -
    2173796352 * A * B ^ 2 * D0 * P + 22643712 * A * B ^ 2 * E0 * lambda +
    41803776 * A * B ^ 2 * U0 - 1834140672 * A * B * C0 ^ 2 * P +
    2445520896 * A * B * C0 * D0 * lambda - 56609280 * A * B * C0 * E0 +
    62705664 * A * B * C0 * T0 - 1811496960 * A * B * D0 ^ 2 +
    1254113280 * A * B * D0 * S0 + 5225472 * A * B * E0 * R0 +
    343901376 * A * C0 ^ 3 * lambda - 1528450560 * A * C0 ^ 2 * D0 +
    529079040 * A * C0 ^ 2 * S0 + 282175488 * A * C0 * D0 * R0 +
    109734912 * A * C0 * E0 * Q - 1119744 * A * C0 * W0 +
    3511517184 * A * D0 ^ 2 * Q + 125411328 * A * D0 * E0 * P -
    26873856 * A * D0 * V0 - 653184 * A * E0 ^ 2 * lambda -
    4478976 * A * E0 * U0 + 14163968 * B ^ 5 - 93929472 * B ^ 4 * Q -
    362299392 * B ^ 3 * C0 * P + 241532928 * B ^ 3 * D0 * lambda -
    5591040 * B ^ 3 * E0 + 6193152 * B ^ 3 * T0 +
    305690112 * B ^ 2 * C0 ^ 2 * lambda - 905748480 * B ^ 2 * C0 * D0 +
    313528320 * B ^ 2 * C0 * S0 + 83607552 * B ^ 2 * D0 * R0 +
    32514048 * B ^ 2 * E0 * Q - 331776 * B ^ 2 * W0 -
    254741760 * B * C0 ^ 3 + 70543872 * B * C0 ^ 2 * R0 +
    3511517184 * B * C0 * D0 * Q + 62705664 * B * C0 * E0 * P -
    13436928 * B * C0 * V0 + 2006581248 * B * D0 ^ 2 * P -
    41803776 * B * D0 * E0 * lambda - 143327232 * B * D0 * U0 +
    483840 * B * E0 ^ 2 - 1990656 * B * E0 * T0 +
    493807104 * C0 ^ 3 * Q + 1693052928 * C0 ^ 2 * D0 * P -
    17635968 * C0 ^ 2 * E0 * lambda - 60466176 * C0 ^ 2 * U0 -
    1128701952 * C0 * D0 ^ 2 * lambda + 52254720 * C0 * D0 * E0 -
    107495424 * C0 * D0 * T0 - 33592320 * C0 * E0 * S0 +
    557383680 * D0 ^ 3 - 1074954240 * D0 ^ 2 * S0 -
    8957952 * D0 * E0 * R0 - 1741824 * E0 ^ 2 * Q + 248832 * E0 * W0

end DegreeZeroCompact610

section DegreeZeroCompactFieldBridge610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- Exact numerical clearing from the depressed primitive to the compact
integer numerator. -/
theorem degreeZeroPrimitive610_eq_clearedCompact
    (A B C0 D0 E0 P Q R0 S0 T0 U0 V0 W0 lambda : F) :
    degreeZeroClearedCompact610 A B C0 D0 E0 P Q R0 S0 T0 U0 V0 W0
        lambda =
      58498535041007616 *
        degreeZeroPrimitive610 (-lambda / 3) (A / 12) (B / 54) (C0 / 144)
          (D0 / 324) (E0 / 46656) (P / 4) (Q / 9) (R0 / 432)
          (S0 / 216) (T0 / 7776) (U0 / 11664) (V0 / 186624)
          (W0 / 5038848) 0 := by
  simp only [degreeZeroClearedCompact610, degreeZeroPrimitive610,
    degreeZeroBaseGroup610, degreeZeroAlphaGroup610,
    degreeZeroBetaGroup610, degreeZeroDeltaGroup610,
    degreeZeroEpsilonGroup610, degreeZeroZetaGroup610,
    degreeZeroEtaGroup610, degreeZeroThetaGroup610, alphaResidual610,
    betaResidual610, gammaResidual610, deltaResidual610,
    epsilonResidual610, zetaResidual610, etaResidual610, thetaResidual610]
  ring

#print axioms degreeZeroPrimitive610_eq_clearedCompact

end DegreeZeroCompactFieldBridge610

end Max11DegreeRoutes
