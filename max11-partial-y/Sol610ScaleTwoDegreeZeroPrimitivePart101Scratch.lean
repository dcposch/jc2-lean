import Fable610ScaleZeroTwelfthDefectSpeedTPart06Scratch

noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroAlphaGroup610 (A B C0 D0 E0 : F) : F :=
  (35 * A ^ 5 * B - 51 * A ^ 4 * D0 - 222 * A ^ 3 * B * C0 -
    117 * A ^ 2 * B ^ 3 + 189 * A ^ 2 * B * E0 +
    297 * A ^ 2 * C0 * D0 + 324 * A * B ^ 2 * D0 +
    324 * A * B * C0 ^ 2 - 324 * A * D0 * E0 +
    108 * B ^ 3 * C0 - 324 * B * C0 * E0 - 324 * B * D0 ^ 2 -
    324 * C0 ^ 2 * D0) / 729

end DegreeZeroPrimitive610

end Max11DegreeRoutes
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
noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroEtaGroup610 (A B C0 D0 : F) : F :=
  (7 * A ^ 2 * B - 12 * A * D0 - 12 * B * C0) / 36

end DegreeZeroPrimitive610

end Max11DegreeRoutes
noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroThetaGroup610 (A B C0 E0 : F) : F :=
  (7 * A ^ 3 - 36 * A * C0 - 18 * B ^ 2 + 216 * E0) / 216

end DegreeZeroPrimitive610

end Max11DegreeRoutes
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
noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroAlphaCertificate610 (A B C0 D0 E0 : F) : F :=
  -(8 * A ^ 5 * B - 15 * A ^ 4 * D0 - 60 * A ^ 3 * B * C0 -
    30 * A ^ 2 * B ^ 3 + 108 * A ^ 2 * B * E0 +
    108 * A ^ 2 * C0 * D0 + 108 * A * B ^ 2 * D0 +
    108 * A * B * C0 ^ 2 - 324 * A * D0 * E0 + 36 * B ^ 3 * C0 -
    324 * B * C0 * E0 - 162 * B * D0 ^ 2 - 162 * C0 ^ 2 * D0) / 729

end DegreeZeroPrimitive610

end Max11DegreeRoutes
noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroBetaCertificate610 (A B C0 D0 E0 : F) : F :=
  -7 * (187 * A ^ 6 - 1980 * A ^ 4 * C0 - 3960 * A ^ 3 * B ^ 2 +
    4320 * A ^ 3 * E0 + 12960 * A ^ 2 * B * D0 +
    6480 * A ^ 2 * C0 ^ 2 + 12960 * A * B ^ 2 * C0 -
    31104 * A * C0 * E0 - 15552 * A * D0 ^ 2 + 1080 * B ^ 4 -
    15552 * B ^ 2 * E0 - 31104 * B * C0 * D0 - 5184 * C0 ^ 3 -
    93312 * E0 ^ 2) / 1119744

end DegreeZeroPrimitive610

end Max11DegreeRoutes
noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroDeltaCertificate610 (A B C0 D0 E0 : F) : F :=
  -(91 * A ^ 5 - 840 * A ^ 3 * C0 - 1260 * A ^ 2 * B ^ 2 +
    2160 * A ^ 2 * E0 + 4320 * A * B * D0 + 2160 * A * C0 ^ 2 +
    2160 * B ^ 2 * C0 - 25920 * C0 * E0 - 12960 * D0 ^ 2) / 31104

end DegreeZeroPrimitive610

end Max11DegreeRoutes
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
noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroZetaCertificate610 (A B C0 D0 E0 : F) : F :=
  (A ^ 4 - 8 * A ^ 2 * C0 - 8 * A * B ^ 2 + 32 * A * E0 +
    32 * B * D0 + 16 * C0 ^ 2) / 64

end DegreeZeroPrimitive610

end Max11DegreeRoutes
noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroEtaCertificate610 (A B C0 D0 : F) : F :=
  -(A ^ 2 * B - 3 * A * D0 - 3 * B * C0) / 9

end DegreeZeroPrimitive610

end Max11DegreeRoutes
noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

def degreeZeroThetaCertificate610 (A B C0 E0 : F) : F :=
  -(5 * A ^ 3 - 36 * A * C0 - 18 * B ^ 2 - 216 * E0) / 216

end DegreeZeroPrimitive610

end Max11DegreeRoutes
noncomputable section
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section DegreeZeroPrimitive610

variable {F : Type*} [Field F] [CharZero F]

/-- The canonical weight-fifteen primitive after the polynomial-part faces
have been transported back to their literal residual functions. -/
def degreeZeroPrimitive610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 : F) : F :=
  degreeZeroBaseGroup610 L A B C0 D0 E0 +
    alphaResidual610 A P * degreeZeroAlphaGroup610 A B C0 D0 E0 +
    betaResidual610 L A B Q * degreeZeroBetaGroup610 A B C0 D0 E0 +
    deltaResidual610 L A B C0 D0 P Q S0 *
      degreeZeroDeltaGroup610 A B C0 D0 +
    epsilonResidual610 L A B C0 D0 E0 P Q R T0 *
      degreeZeroEpsilonGroup610 A B C0 D0 +
    zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 *
      degreeZeroZetaGroup610 A B C0 D0 +
    etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 *
      degreeZeroEtaGroup610 A B C0 D0 +
    thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0 *
      degreeZeroThetaGroup610 A B C0 E0

end DegreeZeroPrimitive610

end Max11DegreeRoutes
