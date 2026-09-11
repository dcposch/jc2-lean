import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroThetaCertificate610 (A B C0 E0 : F) : F :=
  -(5 * A ^ 3 - 36 * A * C0 - 18 * B ^ 2 - 216 * E0) / 216

end DegreeZeroPrimitive610

end Max11DegreeRoutes
