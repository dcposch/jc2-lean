import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroBetaGroup610 (A B C0 D0 E0 : F) : F :=
  7 * (385 * A ^ 6 - 3420 * A ^ 4 * C0 - 7380 * A ^ 3 * B ^ 2 +
    3024 * A ^ 3 * E0 + 18144 * A ^ 2 * B * D0 +
    9072 * A ^ 2 * C0 ^ 2 + 19440 * A * B ^ 2 * C0 -
    15552 * A * C0 * E0 - 15552 * A * D0 ^ 2 + 1620 * B ^ 4 -
    7776 * B ^ 2 * E0 - 31104 * B * C0 * D0 - 5184 * C0 ^ 3 +
    46656 * E0 ^ 2) / 559872

end DegreeZeroPrimitive610

end Max11DegreeRoutes
