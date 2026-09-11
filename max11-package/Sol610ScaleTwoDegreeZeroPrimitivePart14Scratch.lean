import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroEpsilonCertificate610 (A B C0 D0 E0 : F) : F :=
  (4 * A ^ 3 * B - 9 * A ^ 2 * D0 - 18 * A * B * C0 - 3 * B ^ 3 +
    54 * B * E0 + 54 * C0 * D0) / 81

end DegreeZeroPrimitive610

end Max11DegreeRoutes
