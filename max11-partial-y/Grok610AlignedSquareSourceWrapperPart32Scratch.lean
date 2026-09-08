import Grok610AlignedSquareSourceWrapperPart28Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

theorem alignedSquareBBar610_eq_generic
    (h w1 f2 e1 e3 a3 : F)
    (he1 : (3 : F) * f2 - w1 ^ 2 = h * e1)
    (ha3 : (27 : F) * a3 = w1 ^ 3 + h ^ 2 * e3) :
    (54 : F) * a3 * h ^ 12 - (36 : F) * (h ^ 2 * f2) * (h ^ 4 * w1) * h ^ 6 +
        (10 : F) * (h ^ 4 * w1) ^ 3 =
      alignedSquareBBar610 h w1 e1 e3 := by
  simp only [alignedSquareBBar610]
  have h27 : (27 : F) ≠ 0 := by norm_num
  have ha3' : a3 = (w1 ^ 3 + h ^ 2 * e3) / 27 := by
    field_simp [h27]
    linear_combination ha3
  rw [ha3']
  have hf2 : f2 = (w1 ^ 2 + h * e1) / 3 := by
    have h3 : (3 : F) ≠ 0 := by norm_num
    field_simp [h3]
    linear_combination he1
  rw [hf2]
  field_simp [h27]
  ring

end AlignedSquareBars610

end Max11DegreeRoutes
