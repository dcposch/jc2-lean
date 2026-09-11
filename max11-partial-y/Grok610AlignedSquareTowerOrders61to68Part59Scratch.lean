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
/-- Order-`68` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder68610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 : R) : R :=
    - (243596808 : R) * w1n ^ 12 * b7
    - (1102449553920 : R) * w1n ^ 9 * e1 * b6
    + (389099842560 : R) * w1n ^ 8 * e3 * b6
    - (185211525058560 : R) * w1n ^ 6 * e1 ^ 2 * b5
    + (90510609530880 : R) * w1n ^ 6 * a2 * b5
    + (108612731437056 : R) * w1n ^ 6 * a1 * b6
    + (126714853343232 : R) * w1n ^ 6 * a0 * b7
    + (87158364733440 : R) * w1n ^ 5 * e1 * e3 * b5
    - (9684262748160 : R) * w1n ^ 4 * e3 ^ 2 * b5
    - (718396218408960 : R) * w1n ^ 3 * e1 ^ 3 * b4
    + (6951214811971584 : R) * w1n ^ 3 * e1 * a2 * b4
    + (8689018514964480 : R) * w1n ^ 3 * e1 * a1 * b5
    + (10426822217957376 : R) * w1n ^ 3 * e1 * a0 * b6
    + (253551606497280 : R) * w1n ^ 2 * e1 ^ 2 * e3 * b4
    - (1263857238540288 : R) * w1n ^ 2 * e3 * a2 * b4
    - (1579821548175360 : R) * w1n ^ 2 * e3 * a1 * b5
    - (1895785857810432 : R) * w1n ^ 2 * e3 * a0 * b6
    - (7113144729600 : R) * w1n * e1 ^ 7
    + (408891093811200 : R) * w1n * e1 ^ 5 * a2
    - (6423307364597760 : R) * w1n * e1 ^ 3 * a2 ^ 2
    - (22537920577536 : R) * w1n * e1 * e3 ^ 2 * b4
    + (22819644584755200 : R) * w1n * e1 * a2 ^ 3
    + (1185524121600 : R) * e1 ^ 6 * e3
    - (61953196032000 : R) * e1 ^ 4 * e3 * a2
    - (38032740974592 : R) * e1 ^ 4 * b3
    + (802913420574720 : R) * e1 ^ 2 * e3 * a2 ^ 2
    + (1895785857810432 : R) * e1 ^ 2 * a2 * b3
    + (2527714477080576 : R) * e1 ^ 2 * a1 * b4
    + (3159643096350720 : R) * e1 ^ 2 * a0 * b5
    + (385263599616 : R) * e3 ^ 3 * b4
    - (1521309638983680 : R) * e3 * a2 ^ 3
    - (14624633760251904 : R) * a2 ^ 2 * b3
    - (38999023360671744 : R) * a2 * a1 * b4
    - (48748779200839680 : R) * a2 * a0 * b5
    - (24374389600419840 : R) * a1 ^ 2 * b5
    - (58498535041007616 : R) * a1 * a0 * b6
    - (34124145440587776 : R) * a0 ^ 2 * b7

end Max11DegreeRoutes
