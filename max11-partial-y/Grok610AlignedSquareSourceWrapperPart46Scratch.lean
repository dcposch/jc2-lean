import Grok610AlignedSquareSourceWrapperPart09Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareHeadKill610

variable {k : Type*} [Field k] [CharZero k]

theorem alignedSquareBaseHeadCoeff610_ne_zero :
    (alignedSquareBaseHeadCoeff610 : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

end AlignedSquareHeadKill610

end Max11DegreeRoutes
