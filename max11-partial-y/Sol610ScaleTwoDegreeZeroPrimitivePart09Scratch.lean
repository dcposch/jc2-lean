import Sol610ScaleTwoDegreeZeroPrimitivePart08Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart07Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart06Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart05Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart04Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart03Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart02Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart01Scratch

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
