import Sol610ScaleTwoDegreeZeroPostCollapseCoordinateBridgeScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Remaining pole of `ρ` after the MixedPair peel: `75 - 54 = 21`.
Not the linear-root remaining pole `6`. -/
def alignedSquareRemainingPole610 : ℕ := 21

end Max11DegreeRoutes
