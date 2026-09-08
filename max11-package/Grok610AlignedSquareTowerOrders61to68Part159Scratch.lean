import Grok610AlignedSquareTowerOrders61to68Part40Scratch
import Grok610AlignedSquareTowerOrders61to68Part45Scratch
import Grok610AlignedSquareTowerOrders61to68Part50Scratch
import Grok610AlignedSquareTowerOrders61to68Part55Scratch
import Grok610AlignedSquareTowerOrders61to68Part60Scratch
import Grok610AlignedSquareTowerOrders61to68Part64Scratch

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
/-- On the `w₁ = 0` complement peel the MixedPair jet is `h¹⁰`
times the order-`64` tower.  Orders `61`–`63` vanish identically. -/
theorem alignedSquareJetQuotient610_w1Complement_scale
    (h w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 h (h * w1n) (h * e1b) (h * e3b)
        (h * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
      h ^ 10 * (
          alignedSquareW1ComplementOrder64610 w1n a2b a1 b8
        + h * alignedSquareW1ComplementOrder65610 w1n e1b e3b a2b a1 b8 b7
        + h ^ 2 * alignedSquareW1ComplementOrder66610 w1n e1b e3b a2b a1 a0 b8 b7
        + h ^ 3 * alignedSquareW1ComplementOrder67610 w1n e1b e3b a2b a1 a0 b8 b7 b6
        + h ^ 4 * alignedSquareW1ComplementOrder68610 w1n e1b e3b a2b a1 a0 b7 b6 b5
        + h ^ 5 * alignedSquareW1ComplementOrder68Plus610 h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1) := by
  simp only [alignedSquareJetQuotient610, alignedSquareW1ComplementOrder64610, alignedSquareW1ComplementOrder65610, alignedSquareW1ComplementOrder66610, alignedSquareW1ComplementOrder67610, alignedSquareW1ComplementOrder68610, alignedSquareW1ComplementOrder68Plus610]
  ring

end AlignedSquareTowerScale610

end Max11DegreeRoutes
