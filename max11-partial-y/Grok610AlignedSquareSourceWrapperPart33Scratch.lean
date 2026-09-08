import Grok610AlignedSquareSourceWrapperPart29Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

theorem alignedSquarePBar610_eq_generic
    (h w1 b8 : F) :
    -((5 : F) * (h ^ 4 * w1) ^ 2) + (4 : F) * b8 * h ^ 2 =
      alignedSquarePBar610 h w1 b8 := by
  simp only [alignedSquarePBar610]
  ring

end AlignedSquareBars610

end Max11DegreeRoutes
