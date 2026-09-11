import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroBetaCertificate610 (A B C0 D0 E0 : F) : F :=
  -7 * (187 * A ^ 6 - 1980 * A ^ 4 * C0 - 3960 * A ^ 3 * B ^ 2 +
    4320 * A ^ 3 * E0 + 12960 * A ^ 2 * B * D0 +
    6480 * A ^ 2 * C0 ^ 2 + 12960 * A * B ^ 2 * C0 -
    31104 * A * C0 * E0 - 15552 * A * D0 ^ 2 + 1080 * B ^ 4 -
    15552 * B ^ 2 * E0 - 31104 * B * C0 * D0 - 5184 * C0 ^ 3 -
    93312 * E0 ^ 2) / 1119744

end DegreeZeroPrimitive610

end Max11DegreeRoutes
