import Sol610ScaleTwoDegreeZeroPostCollapseCoordinateBridgeScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquarePrimitiveDummy610

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
/-- The weight-fifteen primitive does not use its last slot. -/
theorem alignedSquarePrimitive610_independent_of_X0
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 Y0 : F) :
    degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 =
      degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 Y0 :=
  rfl

end AlignedSquarePrimitiveDummy610

end Max11DegreeRoutes
