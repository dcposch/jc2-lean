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
/-- Order-`67` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder67610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b8 b7 b6 : R) : R :=
    (67814496 : R) * w1n ^ 13 * b8
    - (148106859264 : R) * w1n ^ 11 * e1b * b8
    + (51719855616 : R) * w1n ^ 10 * e3b * b8
    + (24980690262528 : R) * w1n ^ 9 * e1b ^ 2 * b8
    - (13033403615232 : R) * w1n ^ 8 * e1b * e3b * b8
    + (12256645040640 : R) * w1n ^ 8 * a2b * b7
    - (302796245606400 : R) * w1n ^ 7 * e1b ^ 3 * b8
    + (1655035379712 : R) * w1n ^ 7 * e3b ^ 2 * b8
    - (39221264130048 : R) * w1n ^ 7 * a1 * b7
    - (44824301862912 : R) * w1n ^ 7 * a0 * b8
    + (169565897539584 : R) * w1n ^ 6 * e1b ^ 2 * e3b * b8
    - (1555776810491904 : R) * w1n ^ 6 * e1b * a2b * b7
    + (673276357877760 : R) * w1n ^ 5 * e1b ^ 4 * b8
    - (29489721311232 : R) * w1n ^ 5 * e1b * e3b ^ 2 * b8
    + (3294586186924032 : R) * w1n ^ 5 * e1b * a1 * b7
    + (3765241356484608 : R) * w1n ^ 5 * e1b * a0 * b8
    + (366065131880448 : R) * w1n ^ 5 * e3b * a2b * b7
    - (332482152038400 : R) * w1n ^ 4 * e1b ^ 3 * e3b * b8
    + (8957502848286720 : R) * w1n ^ 4 * e1b ^ 2 * a2b * b7
    + (1560302714880 : R) * w1n ^ 4 * e3b ^ 3 * b8
    - (732130263760896 : R) * w1n ^ 4 * e3b * a1 * b7
    - (836720301441024 : R) * w1n ^ 4 * e3b * a0 * b8
    - (323395683287040 : R) * w1n ^ 3 * e1b ^ 5 * b8
    + (53197144326144 : R) * w1n ^ 3 * e1b ^ 2 * e3b ^ 2 * b8
    - (11314740439941120 : R) * w1n ^ 3 * e1b ^ 2 * a1 * b7
    - (12931131931361280 : R) * w1n ^ 3 * e1b ^ 2 * a0 * b8
    - (2514386764431360 : R) * w1n ^ 3 * e1b * e3b * a2b * b7
    + (15640233326936064 : R) * w1n ^ 3 * a2b ^ 2 * b6
    + (111515752857600 : R) * w1n ^ 2 * e1b ^ 4 * e3b * b8
    - (5901413641224192 : R) * w1n ^ 2 * e1b ^ 3 * a2b * b7
    - (3083892424704 : R) * w1n ^ 2 * e1b * e3b ^ 3 * b8
    + (2662291868221440 : R) * w1n ^ 2 * e1b * e3b * a1 * b7
    + (3042619277967360 : R) * w1n ^ 2 * e1b * e3b * a0 * b8
    + (147905103790080 : R) * w1n ^ 2 * e3b ^ 2 * a2b * b7
    - (51186218160881664 : R) * w1n ^ 2 * a2b * a1 * b6
    - (59717254521028608 : R) * w1n ^ 2 * a2b * a0 * b7
    + (25607321026560 : R) * w1n * e1b ^ 6 * b8
    - (11013901516800 : R) * w1n * e1b ^ 3 * e3b ^ 2 * b8
    + (3372236366413824 : R) * w1n * e1b ^ 3 * a1 * b7
    + (3853984418758656 : R) * w1n * e1b ^ 3 * a0 * b8
    + (1124078788804608 : R) * w1n * e1b ^ 2 * e3b * a2b * b7
    - (24645216151535616 : R) * w1n * e1b * a2b ^ 2 * b6
    + (48950673408 : R) * w1n * e3b ^ 4 * b8
    - (118324083032064 : R) * w1n * e3b ^ 2 * a1 * b7
    - (135227523465216 : R) * w1n * e3b ^ 2 * a0 * b8
    + (34124145440587776 : R) * w1n * a1 ^ 2 * b6
    + (79623006028038144 : R) * w1n * a1 * a0 * b7
    + (45498860587450368 : R) * w1n * a0 ^ 2 * b8
    - (3304170455040 : R) * e1b ^ 5 * e3b * b8
    + (281019697201152 : R) * e1b ^ 4 * a2b * b7
    + (293704040448 : R) * e1b ^ 2 * e3b ^ 3 * b8
    - (354972249096192 : R) * e1b ^ 2 * e3b * a1 * b7
    - (405682570395648 : R) * e1b ^ 2 * e3b * a0 * b8
    - (39441361010688 : R) * e1b * e3b ^ 2 * a2b * b7
    + (22749430293725184 : R) * e1b * a2b * a1 * b6
    + (26541002009346048 : R) * e1b * a2b * a0 * b7
    + (1263857238540288 : R) * e3b * a2b ^ 2 * b6

end Max11DegreeRoutes
