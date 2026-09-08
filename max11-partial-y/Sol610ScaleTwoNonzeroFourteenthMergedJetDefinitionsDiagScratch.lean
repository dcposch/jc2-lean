import Sol610ScaleTwoNonzeroFourteenthSourceDescentScratch

/-! Definition-only diagnostic for the five literal bar blocks and their
five order-`63` quotient blocks. -/

noncomputable section

namespace Max11DegreeRoutes.DefinitionDiag610

variable {R : Type*} [CommRing R]

def nuBarAHigh610 (A B C0 E P Q R0 T : R) : R :=
  (14040 : R) * A ^ 7 - 44226 * A ^ 6 * P - 110565 * A ^ 5 * C0 +
    5103 * A ^ 5 * R0 - 163800 * A ^ 4 * B ^ 2 +
    317520 * A ^ 4 * B * Q + 306180 * A ^ 4 * C0 * P +
    4725 * A ^ 4 * E - 3402 * A ^ 4 * T

def nuBarAMid610 (A B C0 D E P Q R0 S T U V : R) : R :=
  (362880 : R) * A ^ 3 * B ^ 2 * P + 604800 * A ^ 3 * B * D -
    136080 * A ^ 3 * B * S + 255150 * A ^ 3 * C0 ^ 2 -
    30618 * A ^ 3 * C0 * R0 - 762048 * A ^ 3 * D * Q -
    13608 * A ^ 3 * E * P + 1458 * A ^ 3 * V +
    453600 * A ^ 2 * B ^ 2 * C0 - 27216 * A ^ 2 * B ^ 2 * R0 -
    1143072 * A ^ 2 * B * C0 * Q - 1306368 * A ^ 2 * B * D * P +
    23328 * A ^ 2 * B * U - 551124 * A ^ 2 * C0 ^ 2 * P -
    17010 * A ^ 2 * C0 * E + 17496 * A ^ 2 * C0 * T -
    544320 * A ^ 2 * D ^ 2 + 349920 * A ^ 2 * D * S +
    1458 * A ^ 2 * E * R0

def nuBarALow610 (A B C0 D E P Q R0 S T U V W : R) : R :=
  (44800 : R) * A * B ^ 4 - 225792 * A * B ^ 3 * Q -
    653184 * A * B ^ 2 * C0 * P - 10080 * A * B ^ 2 * E +
    10368 * A * B ^ 2 * T - 1088640 * A * B * C0 * D +
    349920 * A * B * C0 * S + 93312 * A * B * D * R0 +
    36288 * A * B * E * Q - 324 * A * B * W - 153090 * A * C0 ^ 3 +
    39366 * A * C0 ^ 2 * R0 + 1959552 * A * C0 * D * Q +
    34992 * A * C0 * E * P - 6561 * A * C0 * V +
    1119744 * A * D ^ 2 * P - 69984 * A * D * U + 270 * A * E ^ 2 -
    972 * A * E * T

def nuBarAZero610 (B C0 D E P Q R0 S T U V W : R) : R :=
  -(32256 : R) * B ^ 4 * P - 107520 * B ^ 3 * D + 34560 * B ^ 3 * S -
    136080 * B ^ 2 * C0 ^ 2 + 23328 * B ^ 2 * C0 * R0 +
    580608 * B ^ 2 * D * Q + 10368 * B ^ 2 * E * P - 1944 * B ^ 2 * V +
    489888 * B * C0 ^ 2 * Q + 1119744 * B * C0 * D * P -
    34992 * B * C0 * U + 17280 * B * D * E - 31104 * B * D * T -
    9720 * B * E * S + 157464 * C0 ^ 3 * P + 7290 * C0 ^ 2 * E -
    13122 * C0 ^ 2 * T + 466560 * C0 * D ^ 2 - 524880 * C0 * D * S -
    2187 * C0 * E * R0 - 69984 * D ^ 2 * R0 - 54432 * D * E * Q +
    1944 * D * W - 486 * E ^ 2 * P + 729 * E * V

def nuBarLambda610 (A B C0 D E lambda : R) : R :=
  (88452 : R) * A ^ 5 * B * lambda - 204120 * A ^ 4 * D * lambda -
    408240 * A ^ 3 * B * C0 * lambda - 120960 * A ^ 2 * B ^ 3 * lambda +
    13608 * A ^ 2 * B * E * lambda + 734832 * A ^ 2 * C0 * D * lambda +
    435456 * A * B ^ 2 * D * lambda + 367416 * A * B * C0 ^ 2 * lambda -
    23328 * A * D * E * lambda + 72576 * B ^ 3 * C0 * lambda -
    11664 * B * C0 * E * lambda - 373248 * B * D ^ 2 * lambda -
    314928 * C0 ^ 2 * D * lambda

def nuJetAHigh610 (h A B C0 E P Q R0 T : R) : R :=
  (14040 : R) * A ^ 7 - 44226 * A ^ 6 * P - 110565 * A ^ 5 * C0 +
    5103 * A ^ 5 * R0 - 163800 * A ^ 4 * B ^ 2 * h +
    317520 * A ^ 4 * B * Q * h + 306180 * A ^ 4 * C0 * P +
    4725 * A ^ 4 * E * h - 3402 * A ^ 4 * T

def nuJetAMid610 (h A B C0 D E P Q R0 S T U V : R) : R :=
  362880 * A ^ 3 * B ^ 2 * P * h + 604800 * A ^ 3 * B * D * h -
    136080 * A ^ 3 * B * S * h + 255150 * A ^ 3 * C0 ^ 2 -
    30618 * A ^ 3 * C0 * R0 - 762048 * A ^ 3 * D * Q * h -
    13608 * A ^ 3 * E * P * h + 1458 * A ^ 3 * V * h +
    453600 * A ^ 2 * B ^ 2 * C0 * h - 27216 * A ^ 2 * B ^ 2 * R0 * h -
    1143072 * A ^ 2 * B * C0 * Q * h - 1306368 * A ^ 2 * B * D * P * h +
    23328 * A ^ 2 * B * U * h - 551124 * A ^ 2 * C0 ^ 2 * P -
    17010 * A ^ 2 * C0 * E * h + 17496 * A ^ 2 * C0 * T -
    544320 * A ^ 2 * D ^ 2 * h + 349920 * A ^ 2 * D * S * h +
    1458 * A ^ 2 * E * R0 * h

def nuJetALow610 (h A B C0 D E P Q R0 S T U V W : R) : R :=
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

def nuJetAZero610 (h B C0 D E P Q R0 S T U V W : R) : R :=
  -32256 * B ^ 4 * P * h ^ 2 - 107520 * B ^ 3 * D * h ^ 2 +
    34560 * B ^ 3 * S * h ^ 2 - 136080 * B ^ 2 * C0 ^ 2 * h +
    23328 * B ^ 2 * C0 * R0 * h + 580608 * B ^ 2 * D * Q * h ^ 2 +
    10368 * B ^ 2 * E * P * h ^ 2 - 1944 * B ^ 2 * V * h ^ 2 +
    489888 * B * C0 ^ 2 * Q * h + 1119744 * B * C0 * D * P * h -
    34992 * B * C0 * U * h + 17280 * B * D * E * h ^ 2 -
    31104 * B * D * T * h - 9720 * B * E * S * h ^ 2 +
    157464 * C0 ^ 3 * P + 7290 * C0 ^ 2 * E * h - 13122 * C0 ^ 2 * T +
    466560 * C0 * D ^ 2 * h - 524880 * C0 * D * S * h -
    2187 * C0 * E * R0 * h - 69984 * D ^ 2 * R0 * h -
    54432 * D * E * Q * h ^ 2 + 1944 * D * W * h ^ 2 -
    486 * E ^ 2 * P * h ^ 2 + 729 * E * V * h ^ 2

def nuJetLambda610 (h A B C0 D E lambda : R) : R :=
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

#check nuBarAHigh610
#check nuBarAMid610
#check nuBarALow610
#check nuBarAZero610
#check nuBarLambda610
#check nuJetAHigh610
#check nuJetAMid610
#check nuJetALow610
#check nuJetAZero610
#check nuJetLambda610

end Max11DegreeRoutes.DefinitionDiag610
