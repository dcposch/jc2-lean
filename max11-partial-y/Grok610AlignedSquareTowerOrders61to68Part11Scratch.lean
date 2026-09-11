import Grok610AlignedSquareTowerOrders61to68Part01Scratch
import Grok610AlignedSquareTowerOrders61to68Part212Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000
set_option maxHeartbeats 1600000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem alignedSquareW1ZeroRemainingPole610_eq_sub :
    alignedSquareW1ZeroRemainingPole610 =
      alignedSquareTowerCeiling610 - alignedSquareTowerBaseOrder610 :=
  rfl

end Max11DegreeRoutes
