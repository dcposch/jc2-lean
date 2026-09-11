import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroZetaCertificate610 (A B C0 D0 E0 : F) : F :=
  (A ^ 4 - 8 * A ^ 2 * C0 - 8 * A * B ^ 2 + 32 * A * E0 +
    32 * B * D0 + 16 * C0 ^ 2) / 64

end DegreeZeroPrimitive610

end Max11DegreeRoutes
