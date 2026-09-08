import Grok610AlignedSquareSourceWrapperScratch
import Grok610PoleCeilingLemmaScratch

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
/-- Order-`68` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder68610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 : R) : R :=
    (1185524121600 : R) * e1 ^ 6 * e3
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
