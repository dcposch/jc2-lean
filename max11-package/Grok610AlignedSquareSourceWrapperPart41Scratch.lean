import Grok610AlignedSquareSourceWrapperPart40Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareSourcePrimitive610

variable {F : Type*} [Field F] [CharZero F]

/-- MixedPair specialisation of the aligned source primitive. -/
def alignedSquarePeeledPrimitive610
    (h w1 f2 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F) : F :=
  alignedSquareSourcePrimitive610 h (h ^ 4 * w1) (h ^ 2 * f2) a3 a2 a1
    a0 ((5 : F) / 3 * (h ^ 4 * w1) * h ^ 4) b8 b7 b6 b5 b4 b3 b2 b1

end AlignedSquareSourcePrimitive610

end Max11DegreeRoutes
