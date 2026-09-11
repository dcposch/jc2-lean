import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroEtaGroup610 (A B C0 D0 : F) : F :=
  (7 * A ^ 2 * B - 12 * A * D0 - 12 * B * C0) / 36

end DegreeZeroPrimitive610

end Max11DegreeRoutes
