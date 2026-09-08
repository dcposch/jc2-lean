import Grok610AlignedSquareTowerOrders61to68Part24Scratch
import Grok610AlignedSquareTowerOrders61to68Part29Scratch
import Grok610AlignedSquareTowerOrders61to68Part34Scratch
import Grok610AlignedSquareTowerOrders61to68Part39Scratch
import Grok610AlignedSquareTowerOrders61to68Part44Scratch
import Grok610AlignedSquareTowerOrders61to68Part49Scratch
import Grok610AlignedSquareTowerOrders61to68Part54Scratch
import Grok610AlignedSquareTowerOrders61to68Part59Scratch
import Grok610AlignedSquareTowerOrders61to68Part63Scratch

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
/-- After `w₁ = h w₁n` the MixedPair jet is `h⁷` times the
order-`61` mixed tower. -/
theorem alignedSquareJetQuotient610_w1Peel_scale
    (h w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 h (h * w1n) e1 e3 a2 a1 a0 b8 b7
        b6 b5 b4 b3 b2 b1 =
      h ^ 7 * (
          alignedSquareW1PeelOrder61610 w1n e1 e3 a2 b8
        + h * alignedSquareW1PeelOrder62610 w1n e1 e3 a2 a1 b8 b7
        + h ^ 2 * alignedSquareW1PeelOrder63610 w1n e1 e3 a2 a1 b8 b7
        + h ^ 3 * alignedSquareW1PeelOrder64610 w1n e1 e3 a2 a1 a0 b8 b7 b6
        + h ^ 4 * alignedSquareW1PeelOrder65610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5
        + h ^ 5 * alignedSquareW1PeelOrder66610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5
        + h ^ 6 * alignedSquareW1PeelOrder67610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4
        + h ^ 7 * alignedSquareW1PeelOrder68610 w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
        + h ^ 8 * alignedSquareW1PeelOrder68Plus610 h w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1) := by
  simp only [alignedSquareJetQuotient610, alignedSquareW1PeelOrder61610, alignedSquareW1PeelOrder62610, alignedSquareW1PeelOrder63610, alignedSquareW1PeelOrder64610, alignedSquareW1PeelOrder65610, alignedSquareW1PeelOrder66610, alignedSquareW1PeelOrder67610, alignedSquareW1PeelOrder68610, alignedSquareW1PeelOrder68Plus610]
  ring

end AlignedSquareTowerScale610

end Max11DegreeRoutes
