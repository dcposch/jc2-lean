import Grok610AlignedSquareSourceWrapperPart101Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

theorem alignedSquareP_pole_eight610
    (h w1 b8 : F) (hh : h ≠ 0) :
    alignedSquarePBar610 h w1 b8 / ((4 : F) * h ^ 10) =
      b8 / h ^ 8 - (5 : F) * w1 ^ 2 / ((4 : F) * h ^ 2) := by
  simp only [alignedSquarePBar610]
  field_simp [hh]

end AlignedSquareBars610

end Max11DegreeRoutes
