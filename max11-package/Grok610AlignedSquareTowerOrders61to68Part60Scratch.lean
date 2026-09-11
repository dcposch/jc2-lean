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
/-- Order-`68` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder68610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b7 b6 b5 : R) : R :=
    - (243596808 : R) * w1n ^ 12 * b7
    + (407293862976 : R) * w1n ^ 10 * e1b * b7
    - (142910127360 : R) * w1n ^ 9 * e3b * b7
    - (51319026734976 : R) * w1n ^ 8 * e1b ^ 2 * b7
    + (26066807230464 : R) * w1n ^ 7 * e1b * e3b * b7
    - (33618226397184 : R) * w1n ^ 7 * a2b * b6
    + (445110481041408 : R) * w1n ^ 6 * e1b ^ 3 * b7
    - (3201186852864 : R) * w1n ^ 6 * e3b ^ 2 * b7
    + (108612731437056 : R) * w1n ^ 6 * a1 * b6
    + (126714853343232 : R) * w1n ^ 6 * a0 * b7
    - (232231555325952 : R) * w1n ^ 5 * e1b ^ 2 * e3b * b7
    + (2823931017363456 : R) * w1n ^ 5 * e1b * a2b * b6
    - (654574236825600 : R) * w1n ^ 4 * e1b ^ 4 * b7
    + (36862151639040 : R) * w1n ^ 4 * e1b * e3b ^ 2 * b7
    - (5647862034726912 : R) * w1n ^ 4 * e1b * a1 * b6
    - (6589172373848064 : R) * w1n ^ 4 * e1b * a0 * b7
    - (627540226080768 : R) * w1n ^ 4 * e3b * a2b * b6
    + (279285007712256 : R) * w1n ^ 3 * e1b ^ 3 * e3b * b7
    - (9698348948520960 : R) * w1n ^ 3 * e1b ^ 2 * a2b * b6
    - (1724545105920 : R) * w1n ^ 3 * e3b ^ 3 * b7
    + (1158535801995264 : R) * w1n ^ 3 * e3b * a1 * b6
    + (1351625102327808 : R) * w1n ^ 3 * e3b * a0 * b7
    + (175637310750720 : R) * w1n ^ 2 * e1b ^ 5 * b7
    - (36428479266816 : R) * w1n ^ 2 * e1b ^ 2 * e3b ^ 2 * b7
    + (10268840063139840 : R) * w1n ^ 2 * e1b ^ 2 * a1 * b6
    + (11980313406996480 : R) * w1n ^ 2 * e1b ^ 2 * a0 * b7
    + (2281964458475520 : R) * w1n ^ 2 * e1b * e3b * a2b * b6
    - (21327590900367360 : R) * w1n ^ 2 * a2b ^ 2 * b5
    - (43367237222400 : R) * w1n * e1b ^ 4 * e3b * b7
    + (2890488314068992 : R) * w1n * e1b ^ 3 * a2b * b6
    + (1541946212352 : R) * w1n * e1b * e3b ^ 3 * b7
    - (1825571566780416 : R) * w1n * e1b * e3b * a1 * b6
    - (2129833494577152 : R) * w1n * e1b * e3b * a0 * b7
    - (101420642598912 : R) * w1n * e3b ^ 2 * a2b * b6
    + (56873575734312960 : R) * w1n * a2b * a1 * b5
    + (68248290881175552 : R) * w1n * a2b * a0 * b6
    - (4336723722240 : R) * e1b ^ 6 * b7
    + (2312919318528 : R) * e1b ^ 3 * e3b ^ 2 * b7
    - (912785783390208 : R) * e1b ^ 3 * a1 * b6
    - (1064916747288576 : R) * e1b ^ 3 * a0 * b7
    - (304261927796736 : R) * e1b ^ 2 * e3b * a2b * b6
    + (9478929289052160 : R) * e1b * a2b ^ 2 * b5
    - (13525843968 : R) * e3b ^ 4 * b7
    + (46809527353344 : R) * e3b ^ 2 * a1 * b6
    + (54611115245568 : R) * e3b ^ 2 * a0 * b7
    - (24374389600419840 : R) * a1 ^ 2 * b5
    - (58498535041007616 : R) * a1 * a0 * b6
    - (34124145440587776 : R) * a0 ^ 2 * b7

end Max11DegreeRoutes
