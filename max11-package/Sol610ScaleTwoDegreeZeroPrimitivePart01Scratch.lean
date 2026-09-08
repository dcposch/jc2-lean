import Fable610ScaleZeroTwelfthDefectScratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroAlphaGroup610 (A B C0 D0 E0 : F) : F :=
  (35 * A ^ 5 * B - 51 * A ^ 4 * D0 - 222 * A ^ 3 * B * C0 -
    117 * A ^ 2 * B ^ 3 + 189 * A ^ 2 * B * E0 +
    297 * A ^ 2 * C0 * D0 + 324 * A * B ^ 2 * D0 +
    324 * A * B * C0 ^ 2 - 324 * A * D0 * E0 +
    108 * B ^ 3 * C0 - 324 * B * C0 * E0 - 324 * B * D0 ^ 2 -
    324 * C0 ^ 2 * D0) / 729

end DegreeZeroPrimitive610

end Max11DegreeRoutes
