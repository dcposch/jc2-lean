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
/-- Order-`68` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order68610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (516534771916800 : R) * w1 ^ 7 * e1n ^ 4
    - (2328373457879040 : R) * w1 ^ 7 * e1n * a0
    + (259751681280000 : R) * w1 ^ 6 * e1n ^ 3 * e3
    - (7713405230469120 : R) * w1 ^ 6 * e1n ^ 2 * a1
    + (537476582522880 : R) * w1 ^ 6 * e3 * a0
    - (470184984576 : R) * w1 ^ 6 * b1
    - (6732763578777600 : R) * w1 ^ 5 * e1n ^ 3 * a2
    - (41560269004800 : R) * w1 ^ 5 * e1n ^ 2 * e3 ^ 2
    + (2274921358295040 : R) * w1 ^ 5 * e1n * e3 * a1
    - (39495538704384 : R) * w1 ^ 5 * e1n * b2
    - (28239310173634560 : R) * w1 ^ 5 * a2 * a0
    - (14119655086817280 : R) * w1 ^ 5 * a1 ^ 2
    + (1645786652590080 : R) * w1 ^ 4 * e1n ^ 2 * e3 * a2
    - (470655169560576 : R) * w1 ^ 4 * e1n ^ 2 * b3
    + (2257594859520 : R) * w1 ^ 4 * e1n * e3 ^ 3
    - (68696638385356800 : R) * w1 ^ 4 * e1n * a2 * a1
    - (141351107788800 : R) * w1 ^ 4 * e3 ^ 2 * a1
    + (14627977297920 : R) * w1 ^ 4 * e3 * b2
    - (718396218408960 : R) * w1 ^ 3 * e1n ^ 3 * b4
    - (8430590916034560 : R) * w1 ^ 3 * e1n ^ 2 * a2 ^ 2
    - (69387579555840 : R) * w1 ^ 3 * e1n * e3 ^ 2 * a2
    + (193089300332544 : R) * w1 ^ 3 * e1n * e3 * b3
    - (23795466240 : R) * w1 ^ 3 * e3 ^ 4
    + (6338790162432000 : R) * w1 ^ 3 * e3 * a2 * a1
    - (1354132755578880 : R) * w1 ^ 3 * a2 * b2
    - (2031199133368320 : R) * w1 ^ 3 * a1 * b3
    - (2708265511157760 : R) * w1 ^ 3 * a0 * b4
    - (351274621501440 : R) * w1 ^ 2 * e1n ^ 4 * b5
    + (253551606497280 : R) * w1 ^ 2 * e1n ^ 2 * e3 * b4
    - (1204370130862080 : R) * w1 ^ 2 * e1n * e3 * a2 ^ 2
    - (8531036360146944 : R) * w1 ^ 2 * e1n * a2 * b3
    - (11374715146862592 : R) * w1 ^ 2 * e1n * a1 * b4
    - (14218393933578240 : R) * w1 ^ 2 * e1n * a0 * b5
    - (1652085227520 : R) * w1 ^ 2 * e3 ^ 3 * a2
    - (17553572757504 : R) * w1 ^ 2 * e3 ^ 2 * b3
    - (30806520189419520 : R) * w1 ^ 2 * a2 ^ 2 * a1
    - (66909451714560 : R) * w1 * e1n ^ 5 * b6
    + (89212602286080 : R) * w1 * e1n ^ 3 * e3 * b5
    - (5476714700341248 : R) * w1 * e1n ^ 2 * a2 * b4
    - (6845893375426560 : R) * w1 * e1n ^ 2 * a1 * b5
    - (8215072050511872 : R) * w1 * e1n ^ 2 * a0 * b6
    - (22537920577536 : R) * w1 * e1n * e3 ^ 2 * b4
    + (22819644584755200 : R) * w1 * e1n * a2 ^ 3
    + (140862003609600 : R) * w1 * e3 ^ 2 * a2 ^ 2
    + (1263857238540288 : R) * w1 * e3 * a2 * b3
    + (1685142984720384 : R) * w1 * e3 * a1 * b4
    + (2106428730900480 : R) * w1 * e3 * a0 * b5
    - (4336723722240 : R) * e1n ^ 6 * b7
    + (8921260228608 : R) * e1n ^ 4 * e3 * b6
    - (760654819491840 : R) * e1n ^ 3 * a2 * b5
    - (912785783390208 : R) * e1n ^ 3 * a1 * b6
    - (1064916747288576 : R) * e1n ^ 3 * a0 * b7
    - (4695400120320 : R) * e1n ^ 2 * e3 ^ 2 * b5
    + (561714328240128 : R) * e1n * e3 * a2 * b4
    + (702142910300160 : R) * e1n * e3 * a1 * b5
    + (842571492360192 : R) * e1n * e3 * a0 * b6
    + (385263599616 : R) * e3 ^ 3 * b4
    - (1521309638983680 : R) * e3 * a2 ^ 3
    - (14624633760251904 : R) * a2 ^ 2 * b3
    - (38999023360671744 : R) * a2 * a1 * b4
    - (48748779200839680 : R) * a2 * a0 * b5
    - (24374389600419840 : R) * a1 ^ 2 * b5
    - (58498535041007616 : R) * a1 * a0 * b6
    - (34124145440587776 : R) * a0 ^ 2 * b7

end Max11DegreeRoutes
