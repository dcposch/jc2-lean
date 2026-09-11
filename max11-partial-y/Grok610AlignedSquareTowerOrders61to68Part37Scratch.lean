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
/-- Frozen order-`64` coefficient of the MixedPair jet (`h^10` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder64610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 : R) : R :=
    - (6522826527360 : R) * w1 ^ 10 * a1
    - (972141730560 : R) * w1 ^ 9 * e3 ^ 2
    - (118279783440000 : R) * w1 ^ 8 * e1 ^ 2 * e3
    + (118697068638720 : R) * w1 ^ 8 * e3 * a2
    - (44079842304 : R) * w1 ^ 8 * b3
    - (516534771916800 : R) * w1 ^ 7 * e1 ^ 4
    + (5177815799869440 : R) * w1 ^ 7 * e1 ^ 2 * a2
    - (3492560186818560 : R) * w1 ^ 7 * a2 ^ 2
    + (2681795837952 : R) * w1 ^ 6 * e3 * b4
    + (313770113040384 : R) * w1 ^ 5 * e1 ^ 2 * b4
    - (236973232226304 : R) * w1 ^ 5 * a2 * b4
    - (296216540282880 : R) * w1 ^ 5 * a1 * b5
    - (355459848339456 : R) * w1 ^ 5 * a0 * b6
    - (9684262748160 : R) * w1 ^ 4 * e3 ^ 2 * b5
    - (299331757670400 : R) * w1 ^ 3 * e1 ^ 2 * e3 * b5
    + (965446501662720 : R) * w1 ^ 3 * e3 * a2 * b5
    + (1158535801995264 : R) * w1 ^ 3 * e3 * a1 * b6
    + (1351625102327808 : R) * w1 ^ 3 * e3 * a0 * b7
    - (351274621501440 : R) * w1 ^ 2 * e1 ^ 4 * b5
    + (8557366719283200 : R) * w1 ^ 2 * e1 ^ 2 * a2 * b5
    + (10268840063139840 : R) * w1 ^ 2 * e1 ^ 2 * a1 * b6
    + (11980313406996480 : R) * w1 ^ 2 * e1 ^ 2 * a0 * b7
    + (1565133373440 : R) * w1 ^ 2 * e3 ^ 3 * b6
    - (21327590900367360 : R) * w1 ^ 2 * a2 ^ 2 * b5
    - (51186218160881664 : R) * w1 ^ 2 * a2 * a1 * b6
    - (59717254521028608 : R) * w1 ^ 2 * a2 * a0 * b7
    - (29858627260514304 : R) * w1 ^ 2 * a1 ^ 2 * b7
    - (68248290881175552 : R) * w1 ^ 2 * a1 * a0 * b8
    + (17842520457216 : R) * w1 * e1 ^ 2 * e3 ^ 2 * b6
    - (101420642598912 : R) * w1 * e3 ^ 2 * a2 * b6
    - (118324083032064 : R) * w1 * e3 ^ 2 * a1 * b7
    - (135227523465216 : R) * w1 * e3 ^ 2 * a0 * b8
    + (8921260228608 : R) * e1 ^ 4 * e3 * b6
    - (304261927796736 : R) * e1 ^ 2 * e3 * a2 * b6
    - (354972249096192 : R) * e1 ^ 2 * e3 * a1 * b7
    - (405682570395648 : R) * e1 ^ 2 * e3 * a0 * b8
    - (13525843968 : R) * e3 ^ 4 * b7
    + (1263857238540288 : R) * e3 * a2 ^ 2 * b6
    + (2949000223260672 : R) * e3 * a2 * a1 * b7
    + (3370285969440768 : R) * e3 * a2 * a0 * b8
    + (1685142984720384 : R) * e3 * a1 ^ 2 * b8

end Max11DegreeRoutes
