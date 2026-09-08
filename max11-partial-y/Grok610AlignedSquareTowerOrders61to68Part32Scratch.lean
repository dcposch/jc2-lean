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
/-- Frozen order-`63` coefficient of the MixedPair jet (`h^9` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder63610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : R) : R :=
    (7517337347520 : R) * w1 ^ 10 * e1 * e3
    + (205018291296000 : R) * w1 ^ 9 * e1 ^ 3
    - (472460881052160 : R) * w1 ^ 9 * e1 * a2
    - (7470716977152 : R) * w1 ^ 7 * e1 * b4
    + (87158364733440 : R) * w1 ^ 5 * e1 * e3 * b5
    + (710912924467200 : R) * w1 ^ 4 * e1 ^ 3 * b5
    - (4706551695605760 : R) * w1 ^ 4 * e1 * a2 * b5
    - (5647862034726912 : R) * w1 ^ 4 * e1 * a1 * b6
    - (6589172373848064 : R) * w1 ^ 4 * e1 * a0 * b7
    - (39910901022720 : R) * w1 ^ 3 * e1 * e3 ^ 2 * b6
    - (187346464800768 : R) * w1 ^ 2 * e1 ^ 3 * e3 * b6
    + (2281964458475520 : R) * w1 ^ 2 * e1 * e3 * a2 * b6
    + (2662291868221440 : R) * w1 ^ 2 * e1 * e3 * a1 * b7
    + (3042619277967360 : R) * w1 ^ 2 * e1 * e3 * a0 * b8
    - (66909451714560 : R) * w1 * e1 ^ 5 * b6
    + (2890488314068992 : R) * w1 * e1 ^ 3 * a2 * b6
    + (3372236366413824 : R) * w1 * e1 ^ 3 * a1 * b7
    + (3853984418758656 : R) * w1 * e1 ^ 3 * a0 * b8
    + (1541946212352 : R) * w1 * e1 * e3 ^ 3 * b7
    - (24645216151535616 : R) * w1 * e1 * a2 ^ 2 * b6
    - (57505504353583104 : R) * w1 * e1 * a2 * a1 * b7
    - (65720576404094976 : R) * w1 * e1 * a2 * a0 * b8
    - (32860288202047488 : R) * w1 * e1 * a1 ^ 2 * b8
    + (2312919318528 : R) * e1 ^ 3 * e3 ^ 2 * b7
    - (39441361010688 : R) * e1 * e3 ^ 2 * a2 * b7
    - (45075841155072 : R) * e1 * e3 ^ 2 * a1 * b8

end Max11DegreeRoutes
