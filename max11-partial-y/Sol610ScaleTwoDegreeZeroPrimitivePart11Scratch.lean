import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroAlphaCertificate610 (A B C0 D0 E0 : F) : F :=
  -(8 * A ^ 5 * B - 15 * A ^ 4 * D0 - 60 * A ^ 3 * B * C0 -
    30 * A ^ 2 * B ^ 3 + 108 * A ^ 2 * B * E0 +
    108 * A ^ 2 * C0 * D0 + 108 * A * B ^ 2 * D0 +
    108 * A * B * C0 ^ 2 - 324 * A * D0 * E0 + 36 * B ^ 3 * C0 -
    324 * B * C0 * E0 - 162 * B * D0 ^ 2 - 162 * C0 ^ 2 * D0) / 729

end DegreeZeroPrimitive610

end Max11DegreeRoutes
