import Grok610AlignedSquareTowerOrders61to68Part26Scratch
import Grok610AlignedSquareTowerOrders61to68Part31Scratch
import Grok610AlignedSquareTowerOrders61to68Part36Scratch
import Grok610AlignedSquareTowerOrders61to68Part41Scratch
import Grok610AlignedSquareTowerOrders61to68Part46Scratch
import Grok610AlignedSquareTowerOrders61to68Part51Scratch
import Grok610AlignedSquareTowerOrders61to68Part56Scratch
import Grok610AlignedSquareTowerOrders61to68Part61Scratch
import Grok610AlignedSquareTowerOrders61to68Part65Scratch
import Grok610AlignedSquareTowerOrders61to68Part160Scratch

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
/-- On `μ = 0` after the `q₈` peel, the substituted jet splits as
the order-`55`–`60` prefix plus `h⁷` times the order-`61` tower. -/
theorem alignedSquareJetQuotient610_muZeroQ8_scale
    (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 h w1 (h * e1n) e3 a2 a1 a0
        (h * b8n) b7 b6 b5 b4 b3 b2 b1 =
      alignedSquareMuZeroQ8Prefix5560610 h w1 e1n e3 a2 a1 b8n b7 b6 b5 +
        h ^ 7 * (
          alignedSquareMuZeroQ8Order61610 w1 e1n e3 a2 a1 a0 b8n
        + h * alignedSquareMuZeroQ8Order62610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4
        + h ^ 2 * alignedSquareMuZeroQ8Order63610 w1 e1n e3 a2 a1 a0 b8n
        + h ^ 3 * alignedSquareMuZeroQ8Order64610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3
        + h ^ 4 * alignedSquareMuZeroQ8Order65610 w1 e1n e3 a2 a1 a0 b8n
        + h ^ 5 * alignedSquareMuZeroQ8Order66610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2
        + h ^ 6 * alignedSquareMuZeroQ8Order67610 w1 e1n e3 a1 a0 b8n
        + h ^ 7 * alignedSquareMuZeroQ8Order68610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1
        + h ^ 8 * alignedSquareMuZeroQ8Order68Plus610 h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1) := by
  simp only [alignedSquareJetQuotient610, alignedSquareMuZeroQ8Order61610, alignedSquareMuZeroQ8Order62610, alignedSquareMuZeroQ8Order63610, alignedSquareMuZeroQ8Order64610, alignedSquareMuZeroQ8Order65610, alignedSquareMuZeroQ8Order66610, alignedSquareMuZeroQ8Order67610, alignedSquareMuZeroQ8Order68610, alignedSquareMuZeroQ8Order68Plus610, alignedSquareMuZeroQ8Prefix5560610]
  ring

end AlignedSquareTowerScale610

end Max11DegreeRoutes
