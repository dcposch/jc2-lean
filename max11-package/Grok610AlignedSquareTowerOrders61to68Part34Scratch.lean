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
/-- Order-`63` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder63610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 b8 b7 : R) : R :=
    (673276357877760 : R) * w1n ^ 5 * e1 ^ 4 * b8
    - (7166002278629376 : R) * w1n ^ 5 * e1 ^ 2 * a2 * b8
    + (5647862034726912 : R) * w1n ^ 5 * a2 ^ 2 * b8
    - (332482152038400 : R) * w1n ^ 4 * e1 ^ 3 * e3 * b8
    + (2274921358295040 : R) * w1n ^ 4 * e1 * e3 * a2 * b8
    + (53197144326144 : R) * w1n ^ 3 * e1 ^ 2 * e3 ^ 2 * b8
    - (159643604090880 : R) * w1n ^ 3 * e3 ^ 2 * a2 * b8
    + (175637310750720 : R) * w1n ^ 2 * e1 ^ 5 * b7
    - (5901413641224192 : R) * w1n ^ 2 * e1 ^ 3 * a2 * b7
    - (6744472732827648 : R) * w1n ^ 2 * e1 ^ 3 * a1 * b8
    - (3083892424704 : R) * w1n ^ 2 * e1 * e3 ^ 3 * b8
    + (35940940220989440 : R) * w1n ^ 2 * e1 * a2 ^ 2 * b7
    + (82150720505118720 : R) * w1n ^ 2 * e1 * a2 * a1 * b8
    - (43367237222400 : R) * w1n * e1 ^ 4 * e3 * b7
    + (1124078788804608 : R) * w1n * e1 ^ 2 * e3 * a2 * b7
    + (1284661472919552 : R) * w1n * e1 ^ 2 * e3 * a1 * b8
    + (48950673408 : R) * w1n * e3 ^ 4 * b8
    - (3194750241865728 : R) * w1n * e3 * a2 ^ 2 * b7
    - (7302286267121664 : R) * w1n * e3 * a2 * a1 * b8
    + (2312919318528 : R) * e1 ^ 3 * e3 ^ 2 * b7
    - (39441361010688 : R) * e1 * e3 ^ 2 * a2 * b7
    - (45075841155072 : R) * e1 * e3 ^ 2 * a1 * b8

end Max11DegreeRoutes
