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
/-- Order-`65` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder65610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 b8 b7 : R) : R :=
    (5647862034726912 : R) * w1n ^ 5 * a2b ^ 2 * b8
    - (22591448138907648 : R) * w1n ^ 4 * a2b * a1 * b8
    - (38793395794083840 : R) * w1n ^ 3 * e1b * a2b ^ 2 * b8
    + (20853644435914752 : R) * w1n ^ 3 * a1 ^ 2 * b8
    + (82150720505118720 : R) * w1n ^ 2 * e1b * a2b * a1 * b8
    + (4563928916951040 : R) * w1n ^ 2 * e3b * a2b ^ 2 * b8
    + (17342929884413952 : R) * w1n * e1b ^ 2 * a2b ^ 2 * b8
    - (32860288202047488 : R) * w1n * e1b * a1 ^ 2 * b8
    - (7302286267121664 : R) * w1n * e3b * a2b * a1 * b8
    - (10953429400682496 : R) * e1b ^ 2 * a2b * a1 * b8
    - (1217047711186944 : R) * e1b * e3b * a2b ^ 2 * b8
    + (1685142984720384 : R) * e3b * a1 ^ 2 * b8
    + (13270501004673024 : R) * a2b ^ 3 * b7

end Max11DegreeRoutes
