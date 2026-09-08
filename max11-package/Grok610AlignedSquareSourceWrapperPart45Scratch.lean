import Grok610AlignedSquareSourceWrapperPart44Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem alignedSquareJetQuotient610_head
    (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 0 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 b1 =
      alignedSquareBaseHead610 b8 w1 := by
  simp only [alignedSquareJetQuotient610, alignedSquareBaseHead610]
  ring

end AlignedSquareHead610

end Max11DegreeRoutes
