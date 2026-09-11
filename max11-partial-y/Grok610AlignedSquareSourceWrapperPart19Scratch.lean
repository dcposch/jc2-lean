import Grok610AlignedSquareSourceWrapperPart03Scratch
import Grok610AlignedSquareSourceWrapperPart02Scratch
import Grok610AlignedSquareSourceWrapperPart01Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem alignedSquareSourceClearingPower610_eq_mul :
    alignedSquareSourceClearingPower610 =
      alignedSquareCoordinateClearingStep610 *
        alignedSquarePrimitiveWeight610 :=
  rfl

end Max11DegreeRoutes
