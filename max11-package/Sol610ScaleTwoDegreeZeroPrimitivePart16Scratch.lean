import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroEtaCertificate610 (A B C0 D0 : F) : F :=
  -(A ^ 2 * B - 3 * A * D0 - 3 * B * C0) / 9

end DegreeZeroPrimitive610

end Max11DegreeRoutes
