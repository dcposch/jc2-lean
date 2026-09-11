import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroZetaGroup610 (A B C0 D0 : F) : F :=
  -(7 * A ^ 4 - 40 * A ^ 2 * C0 - 48 * A * B ^ 2 +
    96 * B * D0 + 48 * C0 ^ 2) / 192

end DegreeZeroPrimitive610

end Max11DegreeRoutes
