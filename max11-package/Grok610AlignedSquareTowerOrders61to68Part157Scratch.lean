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
  simp only [alignedSquareJetQuotient610,
    alignedSquareJetQuotient610c0, alignedSquareJetQuotient610c1, alignedSquareJetQuotient610c2, alignedSquareJetQuotient610c3, alignedSquareJetQuotient610c4, alignedSquareJetQuotient610c5, alignedSquareJetQuotient610c6, alignedSquareJetQuotient610c7, alignedSquareJetQuotient610c8, alignedSquareJetQuotient610c9, alignedSquareJetQuotient610c10, alignedSquareJetQuotient610c11, alignedSquareJetQuotient610c12, alignedSquareJetQuotient610c13, alignedSquareJetQuotient610c14, alignedSquareJetQuotient610c15, alignedSquareJetQuotient610c16, alignedSquareJetQuotient610c17, alignedSquareJetQuotient610c18, alignedSquareJetQuotient610c19, alignedSquareJetQuotient610c20, alignedSquareJetQuotient610c21, alignedSquareJetQuotient610c22, alignedSquareJetQuotient610c23, alignedSquareJetQuotient610c24, alignedSquareJetQuotient610c25, alignedSquareJetQuotient610c26, alignedSquareJetQuotient610c27, alignedSquareJetQuotient610c28, alignedSquareJetQuotient610c29, alignedSquareJetQuotient610c30, alignedSquareJetQuotient610c31, alignedSquareJetQuotient610c32, alignedSquareJetQuotient610c33, alignedSquareJetQuotient610c34, alignedSquareJetQuotient610c35, alignedSquareJetQuotient610c36, alignedSquareJetQuotient610c37, alignedSquareJetQuotient610c38, alignedSquareW1ZeroOrder61610, alignedSquareW1ZeroOrder62610, alignedSquareW1ZeroOrder63610, alignedSquareW1ZeroOrder64610, alignedSquareW1ZeroOrder65610, alignedSquareW1ZeroOrder66610, alignedSquareW1ZeroOrder67610, alignedSquareW1ZeroOrder68610, alignedSquareW1ZeroOrder68Plus610]
  ring

end AlignedSquareTowerScale610

end Max11DegreeRoutes
