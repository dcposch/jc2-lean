import Fable610ScaleZeroTwelfthDefectScratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroDeltaGroup610 (A B C0 D0 : F) : F :=
  (49 * A ^ 5 - 360 * A ^ 3 * C0 - 600 * A ^ 2 * B ^ 2 +
    1440 * A * B * D0 + 720 * A * C0 ^ 2 + 720 * B ^ 2 * C0 -
    2160 * D0 ^ 2) / 5184

end DegreeZeroPrimitive610

end Max11DegreeRoutes
