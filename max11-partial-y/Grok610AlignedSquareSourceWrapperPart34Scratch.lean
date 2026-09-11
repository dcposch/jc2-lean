import Grok610AlignedSquareSourceWrapperPart101Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

theorem alignedSquareDepressedA_eq_peeled
    (h w1 f2 e1 : F) (hh : h ≠ 0)
    (he1 : (3 : F) * f2 - w1 ^ 2 = h * e1) :
    depressedA610 h (sexticDepressionR610 h (h ^ 4 * w1))
        (h ^ 4 * w1) (h ^ 2 * f2) =
      alignedSquareABar610 h w1 e1 / ((12 : F) * h ^ 10) := by
  have hA :=
    depressedA610_eq_cleared h (h ^ 4 * w1) (h ^ 2 * f2) hh
  have hbar := alignedSquareABar610_eq_generic h w1 f2 e1 he1
  rw [hA, hbar]

end AlignedSquareBars610

end Max11DegreeRoutes
