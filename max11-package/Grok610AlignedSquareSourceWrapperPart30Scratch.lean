import Sol610ScaleTwoDegreeZeroPostCollapseCoordinateBridgeScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

/-- Polynomial numerator of `144 h²⁰ C` after the MixedPair peel. -/
def alignedSquareCBar610 (h w1 e1 e3 a2 : F) : F :=
  ((432 : F) * a2 * h ^ 18 + (24 : F) * e1 * h ^ 17 * w1 ^ 2 -
      (8 : F) * e3 * h ^ 18 * w1 + h ^ 16 * w1 ^ 4) / 3

end AlignedSquareBars610

end Max11DegreeRoutes
