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
/-- Order-`64` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder64610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b8 b7 b6 : R) : R :=
    - (302796245606400 : R) * w1n ^ 7 * e1 ^ 3 * b8
    + (804347194540032 : R) * w1n ^ 7 * e1 * a2 * b8
    + (169565897539584 : R) * w1n ^ 6 * e1 ^ 2 * e3 * b8
    - (197558960062464 : R) * w1n ^ 6 * e3 * a2 * b8
    - (29489721311232 : R) * w1n ^ 5 * e1 * e3 ^ 2 * b8
    - (654574236825600 : R) * w1n ^ 4 * e1 ^ 4 * b7
    + (8957502848286720 : R) * w1n ^ 4 * e1 ^ 2 * a2 * b7
    + (10237146112327680 : R) * w1n ^ 4 * e1 ^ 2 * a1 * b8
    + (1560302714880 : R) * w1n ^ 4 * e3 ^ 3 * b8
    - (9883758560772096 : R) * w1n ^ 4 * a2 ^ 2 * b7
    - (22591448138907648 : R) * w1n ^ 4 * a2 * a1 * b8
    + (279285007712256 : R) * w1n ^ 3 * e1 ^ 3 * e3 * b7
    - (2514386764431360 : R) * w1n ^ 3 * e1 * e3 * a2 * b7
    - (2873584873635840 : R) * w1n ^ 3 * e1 * e3 * a1 * b8
    - (36428479266816 : R) * w1n ^ 2 * e1 ^ 2 * e3 ^ 2 * b7
    + (147905103790080 : R) * w1n ^ 2 * e3 ^ 2 * a2 * b7
    + (169034404331520 : R) * w1n ^ 2 * e3 ^ 2 * a1 * b8
    - (66909451714560 : R) * w1n * e1 ^ 5 * b6
    + (2890488314068992 : R) * w1n * e1 ^ 3 * a2 * b6
    + (3372236366413824 : R) * w1n * e1 ^ 3 * a1 * b7
    + (3853984418758656 : R) * w1n * e1 ^ 3 * a0 * b8
    + (1541946212352 : R) * w1n * e1 * e3 ^ 3 * b7
    - (24645216151535616 : R) * w1n * e1 * a2 ^ 2 * b6
    - (57505504353583104 : R) * w1n * e1 * a2 * a1 * b7
    - (65720576404094976 : R) * w1n * e1 * a2 * a0 * b8
    - (32860288202047488 : R) * w1n * e1 * a1 ^ 2 * b8
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
