import Grok610AlignedSquareSourceWrapperPart04Scratch
import Grok610AlignedSquareSourceWrapperPart101Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem alignedSquareDerivativePoleOrder610_ne_remaining :
    alignedSquareDerivativePoleOrder610 ≠
      alignedSquareRemainingPole610 := by
  decide

end Max11DegreeRoutes
