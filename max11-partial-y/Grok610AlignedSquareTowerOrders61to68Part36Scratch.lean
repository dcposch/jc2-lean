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
/-- Order-`63` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order63610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b8n : R) : R :=
    (673276357877760 : R) * w1 ^ 5 * e1n ^ 4 * b8n
    + (3765241356484608 : R) * w1 ^ 5 * e1n * a0 * b8n
    - (332482152038400 : R) * w1 ^ 4 * e1n ^ 3 * e3 * b8n
    + (10237146112327680 : R) * w1 ^ 4 * e1n ^ 2 * a1 * b8n
    - (836720301441024 : R) * w1 ^ 4 * e3 * a0 * b8n
    + (8617937380835328 : R) * w1 ^ 3 * e1n ^ 3 * a2 * b8n
    + (53197144326144 : R) * w1 ^ 3 * e1n ^ 2 * e3 ^ 2 * b8n
    - (2873584873635840 : R) * w1 ^ 3 * e1n * e3 * a1 * b8n
    + (41707288871829504 : R) * w1 ^ 3 * a2 * a0 * b8n
    + (20853644435914752 : R) * w1 ^ 3 * a1 ^ 2 * b8n
    - (2248157577609216 : R) * w1 ^ 2 * e1n ^ 2 * e3 * a2 * b8n
    - (3083892424704 : R) * w1 ^ 2 * e1n * e3 ^ 3 * b8n
    + (82150720505118720 : R) * w1 ^ 2 * e1n * a2 * a1 * b8n
    + (169034404331520 : R) * w1 ^ 2 * e3 ^ 2 * a1 * b8n
    + (17342929884413952 : R) * w1 * e1n ^ 2 * a2 ^ 2 * b8n
    + (142740163657728 : R) * w1 * e1n * e3 ^ 2 * a2 * b8n
    + (48950673408 : R) * w1 * e3 ^ 4 * b8n
    - (7302286267121664 : R) * w1 * e3 * a2 * a1 * b8n
    - (1217047711186944 : R) * e1n * e3 * a2 ^ 2 * b8n
    - (1669475598336 : R) * e3 ^ 3 * a2 * b8n
    + (45498860587450368 : R) * a2 ^ 2 * a1 * b8n

end Max11DegreeRoutes
