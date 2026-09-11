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
/-- Order-`65` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order65610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b8n : R) : R :=
    - (323395683287040 : R) * w1 ^ 3 * e1n ^ 5 * b8n
    - (12931131931361280 : R) * w1 ^ 3 * e1n ^ 2 * a0 * b8n
    + (111515752857600 : R) * w1 ^ 2 * e1n ^ 4 * e3 * b8n
    - (6744472732827648 : R) * w1 ^ 2 * e1n ^ 3 * a1 * b8n
    + (3042619277967360 : R) * w1 ^ 2 * e1n * e3 * a0 * b8n
    - (68248290881175552 : R) * w1 ^ 2 * a1 * a0 * b8n
    - (1338189034291200 : R) * w1 * e1n ^ 4 * a2 * b8n
    - (11013901516800 : R) * w1 * e1n ^ 3 * e3 ^ 2 * b8n
    + (1284661472919552 : R) * w1 * e1n ^ 2 * e3 * a1 * b8n
    - (65720576404094976 : R) * w1 * e1n * a2 * a0 * b8n
    - (32860288202047488 : R) * w1 * e1n * a1 ^ 2 * b8n
    - (135227523465216 : R) * w1 * e3 ^ 2 * a0 * b8n
    + (142740163657728 : R) * e1n ^ 3 * e3 * a2 * b8n
    + (293704040448 : R) * e1n ^ 2 * e3 ^ 3 * b8n
    - (10953429400682496 : R) * e1n ^ 2 * a2 * a1 * b8n
    - (45075841155072 : R) * e1n * e3 ^ 2 * a1 * b8n
    + (3370285969440768 : R) * e3 * a2 * a0 * b8n
    + (1685142984720384 : R) * e3 * a1 ^ 2 * b8n

end Max11DegreeRoutes
