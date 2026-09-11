import Sol610ScaleTwoDegreeZeroPostCollapseCoordinateBridgeScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareHead610

variable {R : Type*} [CommRing R]

/-- MixedPair base-order head of the cleared compact numerator. -/
def alignedSquareBaseHead610 (b8 w1 : R) : R :=
  (67814496 : R) * b8 * w1 ^ 13

end AlignedSquareHead610

end Max11DegreeRoutes
