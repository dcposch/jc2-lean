import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroEpsilonGroup610 (A B C0 D0 : F) : F :=
  -(7 * A ^ 3 * B - 9 * A ^ 2 * D0 - 24 * A * B * C0 -
    4 * B ^ 3 + 36 * C0 * D0) / 54

end DegreeZeroPrimitive610

end Max11DegreeRoutes
