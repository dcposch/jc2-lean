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
/-- Order-`64` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order64610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 : R) : R :=
    - (14193574012800 : R) * w1 ^ 11 * e1n ^ 2
    + (7517337347520 : R) * w1 ^ 10 * e1n * e3
    - (6522826527360 : R) * w1 ^ 10 * a1
    - (472460881052160 : R) * w1 ^ 9 * e1n * a2
    - (972141730560 : R) * w1 ^ 9 * e3 ^ 2
    + (118697068638720 : R) * w1 ^ 8 * e3 * a2
    - (44079842304 : R) * w1 ^ 8 * b3
    - (7470716977152 : R) * w1 ^ 7 * e1n * b4
    - (3492560186818560 : R) * w1 ^ 7 * a2 ^ 2
    - (185211525058560 : R) * w1 ^ 6 * e1n ^ 2 * b5
    + (2681795837952 : R) * w1 ^ 6 * e3 * b4
    - (597166856552448 : R) * w1 ^ 5 * e1n ^ 3 * b6
    + (87158364733440 : R) * w1 ^ 5 * e1n * e3 * b5
    - (236973232226304 : R) * w1 ^ 5 * a2 * b4
    - (296216540282880 : R) * w1 ^ 5 * a1 * b5
    - (355459848339456 : R) * w1 ^ 5 * a0 * b6
    - (654574236825600 : R) * w1 ^ 4 * e1n ^ 4 * b7
    + (284365169786880 : R) * w1 ^ 4 * e1n ^ 2 * e3 * b6
    - (4706551695605760 : R) * w1 ^ 4 * e1n * a2 * b5
    - (5647862034726912 : R) * w1 ^ 4 * e1n * a1 * b6
    - (6589172373848064 : R) * w1 ^ 4 * e1n * a0 * b7
    - (9684262748160 : R) * w1 ^ 4 * e3 ^ 2 * b5
    + (279285007712256 : R) * w1 ^ 3 * e1n ^ 3 * e3 * b7
    - (9698348948520960 : R) * w1 ^ 3 * e1n ^ 2 * a2 * b6
    - (11314740439941120 : R) * w1 ^ 3 * e1n ^ 2 * a1 * b7
    - (39910901022720 : R) * w1 ^ 3 * e1n * e3 ^ 2 * b6
    + (965446501662720 : R) * w1 ^ 3 * e3 * a2 * b5
    + (1158535801995264 : R) * w1 ^ 3 * e3 * a1 * b6
    + (1351625102327808 : R) * w1 ^ 3 * e3 * a0 * b7
    - (5901413641224192 : R) * w1 ^ 2 * e1n ^ 3 * a2 * b7
    - (36428479266816 : R) * w1 ^ 2 * e1n ^ 2 * e3 ^ 2 * b7
    + (2281964458475520 : R) * w1 ^ 2 * e1n * e3 * a2 * b6
    + (2662291868221440 : R) * w1 ^ 2 * e1n * e3 * a1 * b7
    + (1565133373440 : R) * w1 ^ 2 * e3 ^ 3 * b6
    - (21327590900367360 : R) * w1 ^ 2 * a2 ^ 2 * b5
    - (51186218160881664 : R) * w1 ^ 2 * a2 * a1 * b6
    - (59717254521028608 : R) * w1 ^ 2 * a2 * a0 * b7
    - (29858627260514304 : R) * w1 ^ 2 * a1 ^ 2 * b7
    + (1124078788804608 : R) * w1 * e1n ^ 2 * e3 * a2 * b7
    + (1541946212352 : R) * w1 * e1n * e3 ^ 3 * b7
    - (24645216151535616 : R) * w1 * e1n * a2 ^ 2 * b6
    - (57505504353583104 : R) * w1 * e1n * a2 * a1 * b7
    - (101420642598912 : R) * w1 * e3 ^ 2 * a2 * b6
    - (118324083032064 : R) * w1 * e3 ^ 2 * a1 * b7
    - (4792125362798592 : R) * e1n ^ 2 * a2 ^ 2 * b7
    - (39441361010688 : R) * e1n * e3 ^ 2 * a2 * b7
    - (13525843968 : R) * e3 ^ 4 * b7
    + (1263857238540288 : R) * e3 * a2 ^ 2 * b6
    + (2949000223260672 : R) * e3 * a2 * a1 * b7

end Max11DegreeRoutes
