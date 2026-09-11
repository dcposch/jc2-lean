import Grok610AlignedSquareSourceWrapperPart48Scratch

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

set_option maxHeartbeats 1600000000 in
/-- Order-`61` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order61610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b8n : R) : R :=
    - (302796245606400 : R) * w1 ^ 7 * e1n ^ 3 * b8n
    - (44824301862912 : R) * w1 ^ 7 * a0 * b8n
    + (169565897539584 : R) * w1 ^ 6 * e1n ^ 2 * e3 * b8n
    - (1778030640562176 : R) * w1 ^ 6 * e1n * a1 * b8n
    - (7166002278629376 : R) * w1 ^ 5 * e1n ^ 2 * a2 * b8n
    - (29489721311232 : R) * w1 ^ 5 * e1n * e3 ^ 2 * b8n
    + (418360150720512 : R) * w1 ^ 5 * e3 * a1 * b8n
    + (2274921358295040 : R) * w1 ^ 4 * e1n * e3 * a2 * b8n
    + (1560302714880 : R) * w1 ^ 4 * e3 ^ 3 * b8n
    - (22591448138907648 : R) * w1 ^ 4 * a2 * a1 * b8n
    - (38793395794083840 : R) * w1 ^ 3 * e1n * a2 ^ 2 * b8n
    - (159643604090880 : R) * w1 ^ 3 * e3 ^ 2 * a2 * b8n
    + (4563928916951040 : R) * w1 ^ 2 * e3 * a2 ^ 2 * b8n
    - (32860288202047488 : R) * w1 * a2 ^ 3 * b8n

end Max11DegreeRoutes
