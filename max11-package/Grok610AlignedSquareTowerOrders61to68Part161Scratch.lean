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
  simp only [alignedSquareJetQuotient610,
    alignedSquareJetQuotient610c0, alignedSquareJetQuotient610c1, alignedSquareJetQuotient610c2, alignedSquareJetQuotient610c3, alignedSquareJetQuotient610c4, alignedSquareJetQuotient610c5, alignedSquareJetQuotient610c6, alignedSquareJetQuotient610c7, alignedSquareJetQuotient610c8, alignedSquareJetQuotient610c9, alignedSquareJetQuotient610c10, alignedSquareJetQuotient610c11, alignedSquareJetQuotient610c12, alignedSquareJetQuotient610c13, alignedSquareJetQuotient610c14, alignedSquareJetQuotient610c15, alignedSquareJetQuotient610c16, alignedSquareJetQuotient610c17, alignedSquareJetQuotient610c18, alignedSquareJetQuotient610c19, alignedSquareJetQuotient610c20, alignedSquareJetQuotient610c21, alignedSquareJetQuotient610c22, alignedSquareJetQuotient610c23, alignedSquareJetQuotient610c24, alignedSquareJetQuotient610c25, alignedSquareJetQuotient610c26, alignedSquareJetQuotient610c27, alignedSquareJetQuotient610c28, alignedSquareJetQuotient610c29, alignedSquareJetQuotient610c30, alignedSquareJetQuotient610c31, alignedSquareJetQuotient610c32, alignedSquareJetQuotient610c33, alignedSquareJetQuotient610c34, alignedSquareJetQuotient610c35, alignedSquareJetQuotient610c36, alignedSquareJetQuotient610c37, alignedSquareJetQuotient610c38, alignedSquareMuZeroQ8Order61610, alignedSquareMuZeroQ8Order62610, alignedSquareMuZeroQ8Order63610, alignedSquareMuZeroQ8Order64610, alignedSquareMuZeroQ8Order65610, alignedSquareMuZeroQ8Order66610, alignedSquareMuZeroQ8Order67610, alignedSquareMuZeroQ8Order68610, alignedSquareMuZeroQ8Order68Plus610, alignedSquareMuZeroQ8Prefix5560610]
  ring

end AlignedSquareTowerScale610

end Max11DegreeRoutes
