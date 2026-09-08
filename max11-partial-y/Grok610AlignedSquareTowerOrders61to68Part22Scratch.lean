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
/-- Frozen order-`61` coefficient of the MixedPair jet (`h^7` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder61610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) : R :=
    (69754744080 : R) * w1 ^ 13 * e1
    + (2918248819200 : R) * w1 ^ 8 * e1 * b5
    - (49389740015616 : R) * w1 ^ 6 * e1 * e3 * b6
    - (597166856552448 : R) * w1 ^ 5 * e1 ^ 3 * b6
    + (2823931017363456 : R) * w1 ^ 5 * e1 * a2 * b6
    + (3294586186924032 : R) * w1 ^ 5 * e1 * a1 * b7
    + (3765241356484608 : R) * w1 ^ 5 * e1 * a0 * b8
    + (36862151639040 : R) * w1 ^ 4 * e1 * e3 ^ 2 * b7
    + (279285007712256 : R) * w1 ^ 3 * e1 ^ 3 * e3 * b7
    - (2514386764431360 : R) * w1 ^ 3 * e1 * e3 * a2 * b7
    - (2873584873635840 : R) * w1 ^ 3 * e1 * e3 * a1 * b8
    + (175637310750720 : R) * w1 ^ 2 * e1 ^ 5 * b7
    - (5901413641224192 : R) * w1 ^ 2 * e1 ^ 3 * a2 * b7
    - (6744472732827648 : R) * w1 ^ 2 * e1 ^ 3 * a1 * b8
    - (3083892424704 : R) * w1 ^ 2 * e1 * e3 ^ 3 * b8
    + (35940940220989440 : R) * w1 ^ 2 * e1 * a2 ^ 2 * b7
    + (82150720505118720 : R) * w1 ^ 2 * e1 * a2 * a1 * b8
    - (11013901516800 : R) * w1 * e1 ^ 3 * e3 ^ 2 * b8
    + (142740163657728 : R) * w1 * e1 * e3 ^ 2 * a2 * b8
    - (3304170455040 : R) * e1 ^ 5 * e3 * b8
    + (142740163657728 : R) * e1 ^ 3 * e3 * a2 * b8
    - (1217047711186944 : R) * e1 * e3 * a2 ^ 2 * b8

end Max11DegreeRoutes
