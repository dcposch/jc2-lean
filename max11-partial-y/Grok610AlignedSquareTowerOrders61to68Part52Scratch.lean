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
/-- Frozen order-`67` coefficient of the MixedPair jet (`h^13` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder67610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 : R) : R :=
    - (2328373457879040 : R) * w1 ^ 7 * e1 * a0
    + (2274921358295040 : R) * w1 ^ 5 * e1 * e3 * a1
    - (39495538704384 : R) * w1 ^ 5 * e1 * b2
    + (4937359957770240 : R) * w1 ^ 4 * e1 ^ 3 * a1
    + (2257594859520 : R) * w1 ^ 4 * e1 * e3 ^ 3
    - (68696638385356800 : R) * w1 ^ 4 * e1 * a2 * a1
    - (3441844224000 : R) * w1 ^ 3 * e1 ^ 3 * e3 ^ 2
    - (69387579555840 : R) * w1 ^ 3 * e1 * e3 ^ 2 * a2
    + (193089300332544 : R) * w1 ^ 3 * e1 * e3 * b3
    - (26674292736000 : R) * w1 ^ 2 * e1 ^ 5 * e3
    + (557578764288000 : R) * w1 ^ 2 * e1 ^ 3 * e3 * a2
    + (570491114618880 : R) * w1 ^ 2 * e1 ^ 3 * b3
    - (1204370130862080 : R) * w1 ^ 2 * e1 * e3 * a2 ^ 2
    - (8531036360146944 : R) * w1 ^ 2 * e1 * a2 * b3
    - (11374715146862592 : R) * w1 ^ 2 * e1 * a1 * b4
    - (14218393933578240 : R) * w1 ^ 2 * e1 * a0 * b5
    - (7113144729600 : R) * w1 * e1 ^ 7
    + (408891093811200 : R) * w1 * e1 ^ 5 * a2
    - (6423307364597760 : R) * w1 * e1 ^ 3 * a2 ^ 2
    - (22537920577536 : R) * w1 * e1 * e3 ^ 2 * b4
    + (22819644584755200 : R) * w1 * e1 * a2 ^ 3
    - (22537920577536 : R) * e1 ^ 3 * e3 * b4
    + (561714328240128 : R) * e1 * e3 * a2 * b4
    + (702142910300160 : R) * e1 * e3 * a1 * b5
    + (842571492360192 : R) * e1 * e3 * a0 * b6

end Max11DegreeRoutes
