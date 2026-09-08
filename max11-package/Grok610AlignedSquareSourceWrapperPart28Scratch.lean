import Sol610ScaleTwoDegreeZeroPostCollapseCoordinateBridgeScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

/-- Polynomial numerator of `54 h¹⁵ B` after the MixedPair peel. -/
def alignedSquareBBar610 (h w1 e1 e3 : F) : F :=
  -((12 : F) * e1 * h ^ 13 * w1) + (2 : F) * e3 * h ^ 14

end AlignedSquareBars610

end Max11DegreeRoutes
