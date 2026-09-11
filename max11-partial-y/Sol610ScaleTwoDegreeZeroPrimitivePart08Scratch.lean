import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroBaseGroup610 (L A B C0 D0 E0 : F) : F :=
  -(10935 * A ^ 7 * L + 62720 * A ^ 6 * B -
    113724 * A ^ 5 * C0 * L - 92160 * A ^ 5 * D0 -
    301806 * A ^ 4 * B ^ 2 * L - 491520 * A ^ 4 * B * C0 +
    122472 * A ^ 4 * E0 * L - 343040 * A ^ 3 * B ^ 3 +
    769824 * A ^ 3 * B * D0 * L + 483840 * A ^ 3 * B * E0 +
    384912 * A ^ 3 * C0 ^ 2 * L + 668160 * A ^ 3 * C0 * D0 +
    1224720 * A ^ 2 * B ^ 2 * C0 * L + 1071360 * A ^ 2 * B ^ 2 * D0 +
    1071360 * A ^ 2 * B * C0 ^ 2 - 699840 * A ^ 2 * C0 * E0 * L -
    559872 * A ^ 2 * D0 ^ 2 * L - 622080 * A ^ 2 * D0 * E0 +
    209952 * A * B ^ 4 * L + 737280 * A * B ^ 3 * C0 -
    839808 * A * B ^ 2 * E0 * L - 2519424 * A * B * C0 * D0 * L -
    1658880 * A * B * C0 * E0 - 1244160 * A * B * D0 ^ 2 -
    419904 * A * C0 ^ 3 * L - 1244160 * A * C0 ^ 2 * D0 +
    36864 * B ^ 5 - 419904 * B ^ 3 * D0 * L - 276480 * B ^ 3 * E0 -
    629856 * B ^ 2 * C0 ^ 2 * L - 1244160 * B ^ 2 * C0 * D0 -
    414720 * B * C0 ^ 3 + 1679616 * B * D0 * E0 * L +
    839808 * C0 ^ 2 * E0 * L + 1679616 * C0 * D0 ^ 2 * L +
    2488320 * C0 * D0 * E0 + 829440 * D0 ^ 3) / 2239488

end DegreeZeroPrimitive610

end Max11DegreeRoutes
