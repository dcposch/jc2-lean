import Fable610ScaleZeroTwelfthDefectScratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroLCertificate610 (A B C0 D0 E0 : F) : F :=
  (A ^ 7 - 12 * A ^ 5 * C0 - 30 * A ^ 4 * B ^ 2 + 24 * A ^ 4 * E0 +
    96 * A ^ 3 * B * D0 + 48 * A ^ 3 * C0 ^ 2 +
    144 * A ^ 2 * B ^ 2 * C0 - 192 * A ^ 2 * C0 * E0 -
    96 * A ^ 2 * D0 ^ 2 + 24 * A * B ^ 4 - 192 * A * B ^ 2 * E0 -
    384 * A * B * C0 * D0 - 64 * A * C0 ^ 3 + 384 * A * E0 ^ 2 -
    64 * B ^ 3 * D0 - 96 * B ^ 2 * C0 ^ 2 + 768 * B * D0 * E0 +
    384 * C0 ^ 2 * E0 + 384 * C0 * D0 ^ 2) / 1024

end DegreeZeroPrimitive610

end Max11DegreeRoutes
