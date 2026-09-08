import Grok610AlignedSquareTowerOrders61to68Part23Scratch
import Grok610AlignedSquareTowerOrders61to68Part28Scratch
import Grok610AlignedSquareTowerOrders61to68Part33Scratch
import Grok610AlignedSquareTowerOrders61to68Part38Scratch
import Grok610AlignedSquareTowerOrders61to68Part43Scratch
import Grok610AlignedSquareTowerOrders61to68Part48Scratch
import Grok610AlignedSquareTowerOrders61to68Part53Scratch
import Grok610AlignedSquareTowerOrders61to68Part58Scratch
import Grok610AlignedSquareTowerOrders61to68Part62Scratch

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

section AlignedSquareTowerScale610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- On `w₁ = 0` the MixedPair jet is `h⁷` times the order-`61`
tower (remaining pole `14`). -/
theorem alignedSquareJetQuotient610_w1Zero_scale
    (h e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 h 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
        b4 b3 b2 b1 =
      h ^ 7 * (
          alignedSquareW1ZeroOrder61610 e1 e3 a2 b8
        + h * alignedSquareW1ZeroOrder62610 e1 e3 a2 a1 b8 b7
        + h ^ 2 * alignedSquareW1ZeroOrder63610 e1 e3 a2 a1 b8 b7
        + h ^ 3 * alignedSquareW1ZeroOrder64610 e1 e3 a2 a1 a0 b8 b7 b6
        + h ^ 4 * alignedSquareW1ZeroOrder65610 e1 e3 a2 a1 a0 b8 b7 b6 b5
        + h ^ 5 * alignedSquareW1ZeroOrder66610 e1 e3 a2 a1 a0 b7 b6 b5
        + h ^ 6 * alignedSquareW1ZeroOrder67610 e1 e3 a2 a1 a0 b6 b5 b4
        + h ^ 7 * alignedSquareW1ZeroOrder68610 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
        + h ^ 8 * alignedSquareW1ZeroOrder68Plus610 h e1 e3 a2 a1 a0 b4 b3 b2 b1) := by
  simp only [alignedSquareJetQuotient610, alignedSquareW1ZeroOrder61610, alignedSquareW1ZeroOrder62610, alignedSquareW1ZeroOrder63610, alignedSquareW1ZeroOrder64610, alignedSquareW1ZeroOrder65610, alignedSquareW1ZeroOrder66610, alignedSquareW1ZeroOrder67610, alignedSquareW1ZeroOrder68610, alignedSquareW1ZeroOrder68Plus610]
  ring

end AlignedSquareTowerScale610

end Max11DegreeRoutes
