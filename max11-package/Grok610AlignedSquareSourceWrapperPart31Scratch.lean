import Grok610AlignedSquareSourceWrapperPart27Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

theorem alignedSquareABar610_eq_generic
    (h w1 f2 e1 : F)
    (he1 : (3 : F) * f2 - w1 ^ 2 = h * e1) :
    (12 : F) * (h ^ 2 * f2) * h ^ 6 - (5 : F) * (h ^ 4 * w1) ^ 2 =
      alignedSquareABar610 h w1 e1 := by
  simp only [alignedSquareABar610]
  have h12 : (12 : F) * f2 = (4 : F) * ((3 : F) * f2) := by ring
  calc
    (12 : F) * (h ^ 2 * f2) * h ^ 6 - (5 : F) * (h ^ 4 * w1) ^ 2 =
        (12 : F) * f2 * h ^ 8 - (5 : F) * h ^ 8 * w1 ^ 2 := by ring
    _ = ((4 : F) * ((3 : F) * f2) - (5 : F) * w1 ^ 2) * h ^ 8 := by ring
    _ = ((4 : F) * (w1 ^ 2 + h * e1) - (5 : F) * w1 ^ 2) * h ^ 8 := by
      rw [← he1]; ring
    _ = (4 : F) * e1 * h ^ 9 - h ^ 8 * w1 ^ 2 := by ring

end AlignedSquareBars610

end Max11DegreeRoutes
