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
/-- Order-`66` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder66610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) : R :=
    - (148106859264 : R) * w1n ^ 11 * e1 * b8
    + (51719855616 : R) * w1n ^ 10 * e3 * b8
    - (51319026734976 : R) * w1n ^ 8 * e1 ^ 2 * b7
    + (12256645040640 : R) * w1n ^ 8 * a2 * b7
    + (14007594332160 : R) * w1n ^ 8 * a1 * b8
    + (26066807230464 : R) * w1n ^ 7 * e1 * e3 * b7
    - (3201186852864 : R) * w1n ^ 6 * e3 ^ 2 * b7
    - (597166856552448 : R) * w1n ^ 5 * e1 ^ 3 * b6
    + (2823931017363456 : R) * w1n ^ 5 * e1 * a2 * b6
    + (3294586186924032 : R) * w1n ^ 5 * e1 * a1 * b7
    + (3765241356484608 : R) * w1n ^ 5 * e1 * a0 * b8
    + (284365169786880 : R) * w1n ^ 4 * e1 ^ 2 * e3 * b6
    - (627540226080768 : R) * w1n ^ 4 * e3 * a2 * b6
    - (732130263760896 : R) * w1n ^ 4 * e3 * a1 * b7
    - (836720301441024 : R) * w1n ^ 4 * e3 * a0 * b8
    - (39910901022720 : R) * w1n ^ 3 * e1 * e3 ^ 2 * b6
    - (351274621501440 : R) * w1n ^ 2 * e1 ^ 4 * b5
    + (8557366719283200 : R) * w1n ^ 2 * e1 ^ 2 * a2 * b5
    + (10268840063139840 : R) * w1n ^ 2 * e1 ^ 2 * a1 * b6
    + (11980313406996480 : R) * w1n ^ 2 * e1 ^ 2 * a0 * b7
    + (1565133373440 : R) * w1n ^ 2 * e3 ^ 3 * b6
    - (21327590900367360 : R) * w1n ^ 2 * a2 ^ 2 * b5
    - (51186218160881664 : R) * w1n ^ 2 * a2 * a1 * b6
    - (59717254521028608 : R) * w1n ^ 2 * a2 * a0 * b7
    - (29858627260514304 : R) * w1n ^ 2 * a1 ^ 2 * b7
    - (68248290881175552 : R) * w1n ^ 2 * a1 * a0 * b8
    + (89212602286080 : R) * w1n * e1 ^ 3 * e3 * b5
    - (1521309638983680 : R) * w1n * e1 * e3 * a2 * b5
    - (1825571566780416 : R) * w1n * e1 * e3 * a1 * b6
    - (2129833494577152 : R) * w1n * e1 * e3 * a0 * b7
    - (4695400120320 : R) * e1 ^ 2 * e3 ^ 2 * b5
    + (39007939461120 : R) * e3 ^ 2 * a2 * b5
    + (46809527353344 : R) * e3 ^ 2 * a1 * b6
    + (54611115245568 : R) * e3 ^ 2 * a0 * b7

end Max11DegreeRoutes
