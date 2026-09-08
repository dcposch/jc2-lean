import Sol610ScaleTwoDegreeZeroPostCollapseCoordinateBridgeScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

/-- Polynomial numerator of `4 h¹⁰ P` on `λ = 0` after `a₅ = h⁴ w₁`. -/
def alignedSquarePBar610 (h w1 b8 : F) : F :=
  (4 : F) * b8 * h ^ 2 - (5 : F) * h ^ 8 * w1 ^ 2

end AlignedSquareBars610

end Max11DegreeRoutes
