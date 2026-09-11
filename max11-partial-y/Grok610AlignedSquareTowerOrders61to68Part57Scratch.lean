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
/-- Frozen order-`68` coefficient of the MixedPair jet (`h^14` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder68610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (537476582522880 : R) * w1 ^ 6 * e3 * a0
    - (470184984576 : R) * w1 ^ 6 * b1
    + (10237146112327680 : R) * w1 ^ 5 * e1 ^ 2 * a0
    - (28239310173634560 : R) * w1 ^ 5 * a2 * a0
    - (14119655086817280 : R) * w1 ^ 5 * a1 ^ 2
    - (141351107788800 : R) * w1 ^ 4 * e3 ^ 2 * a1
    + (14627977297920 : R) * w1 ^ 4 * e3 * b2
    - (624488216002560 : R) * w1 ^ 3 * e1 ^ 2 * e3 * a1
    + (579267900997632 : R) * w1 ^ 3 * e1 ^ 2 * b2
    - (23795466240 : R) * w1 ^ 3 * e3 ^ 4
    + (6338790162432000 : R) * w1 ^ 3 * e3 * a2 * a1
    - (1354132755578880 : R) * w1 ^ 3 * a2 * b2
    - (2031199133368320 : R) * w1 ^ 3 * a1 * b3
    - (2708265511157760 : R) * w1 ^ 3 * a0 * b4
    + (1254552219648000 : R) * w1 ^ 2 * e1 ^ 4 * a1
    + (1147281408000 : R) * w1 ^ 2 * e1 ^ 2 * e3 ^ 3
    - (10839331177758720 : R) * w1 ^ 2 * e1 ^ 2 * a2 * a1
    - (1652085227520 : R) * w1 ^ 2 * e3 ^ 3 * a2
    - (17553572757504 : R) * w1 ^ 2 * e3 ^ 2 * b3
    - (30806520189419520 : R) * w1 ^ 2 * a2 ^ 2 * a1
    + (4206698496000 : R) * w1 * e1 ^ 4 * e3 ^ 2
    - (79300090920960 : R) * w1 * e1 ^ 2 * e3 ^ 2 * a2
    - (152130963898368 : R) * w1 * e1 ^ 2 * e3 * b3
    + (140862003609600 : R) * w1 * e3 ^ 2 * a2 ^ 2
    + (1263857238540288 : R) * w1 * e3 * a2 * b3
    + (1685142984720384 : R) * w1 * e3 * a1 * b4
    + (2106428730900480 : R) * w1 * e3 * a0 * b5
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
