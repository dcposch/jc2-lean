import Grok610AlignedSquareSourceWrapperPart28Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

theorem alignedSquareB_pole_two610
    (h w1 e1 e3 : F) (hh : h ≠ 0) :
    alignedSquareBBar610 h w1 e1 e3 / ((54 : F) * h ^ 15) =
      -((2 : F) * e1 * w1) / ((9 : F) * h ^ 2) +
        e3 / ((27 : F) * h) := by
  simp only [alignedSquareBBar610]
  field_simp [hh]
  ring

end AlignedSquareBars610

end Max11DegreeRoutes
