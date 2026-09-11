import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroDeltaCertificate610 (A B C0 D0 E0 : F) : F :=
  -(91 * A ^ 5 - 840 * A ^ 3 * C0 - 1260 * A ^ 2 * B ^ 2 +
    2160 * A ^ 2 * E0 + 4320 * A * B * D0 + 2160 * A * C0 ^ 2 +
    2160 * B ^ 2 * C0 - 25920 * C0 * E0 - 12960 * D0 ^ 2) / 31104

end DegreeZeroPrimitive610

end Max11DegreeRoutes
