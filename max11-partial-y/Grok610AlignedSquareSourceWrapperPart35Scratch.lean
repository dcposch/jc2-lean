import Grok610AlignedSquareSourceWrapperPart101Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

theorem alignedSquareA_pole_two610
    (h w1 e1 : F) (hh : h ≠ 0) :
    alignedSquareABar610 h w1 e1 / ((12 : F) * h ^ 10) =
      -w1 ^ 2 / ((12 : F) * h ^ 2) + e1 / ((3 : F) * h) := by
  simp only [alignedSquareABar610]
  field_simp [hh]
  ring

end AlignedSquareBars610

end Max11DegreeRoutes
