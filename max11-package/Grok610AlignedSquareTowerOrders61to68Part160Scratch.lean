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

section AlignedSquareTowerScale610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- Mixed orders `55` through `60` of the `μ = 0` `q₈`-peeled jet (the `h¹` through `h⁶` terms).  Not extracted as named frozen heads in this batch; recorded so the order-`61` identity is exact. -/
def alignedSquareMuZeroQ8Prefix5560610 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 b8n b7 b6 b5 : R) : R :=
    - (26372304 : R) * h ^ 6 * w1 ^ 15
    - (3242498688 : R) * h ^ 6 * w1 ^ 10 * b5
    - (1102449553920 : R) * h ^ 6 * w1 ^ 9 * e1n * b6
    - (51319026734976 : R) * h ^ 6 * w1 ^ 8 * e1n ^ 2 * b7
    + (389099842560 : R) * h ^ 6 * w1 ^ 8 * e3 * b6
    + (26066807230464 : R) * h ^ 6 * w1 ^ 7 * e1n * e3 * b7
    - (33618226397184 : R) * h ^ 6 * w1 ^ 7 * a2 * b6
    - (39221264130048 : R) * h ^ 6 * w1 ^ 7 * a1 * b7
    - (1555776810491904 : R) * h ^ 6 * w1 ^ 6 * e1n * a2 * b7
    - (3201186852864 : R) * h ^ 6 * w1 ^ 6 * e3 ^ 2 * b7
    + (366065131880448 : R) * h ^ 6 * w1 ^ 5 * e3 * a2 * b7
    - (9883758560772096 : R) * h ^ 6 * w1 ^ 4 * a2 ^ 2 * b7
    + (24980690262528 : R) * h ^ 5 * w1 ^ 9 * e1n ^ 2 * b8n
    - (13033403615232 : R) * h ^ 5 * w1 ^ 8 * e1n * e3 * b8n
    + (14007594332160 : R) * h ^ 5 * w1 ^ 8 * a1 * b8n
    + (804347194540032 : R) * h ^ 5 * w1 ^ 7 * e1n * a2 * b8n
    + (1655035379712 : R) * h ^ 5 * w1 ^ 7 * e3 ^ 2 * b8n
    - (197558960062464 : R) * h ^ 5 * w1 ^ 6 * e3 * a2 * b8n
    + (5647862034726912 : R) * h ^ 5 * w1 ^ 5 * a2 ^ 2 * b8n
    + (884317824 : R) * h ^ 4 * w1 ^ 11 * b6
    + (407293862976 : R) * h ^ 4 * w1 ^ 10 * e1n * b7
    - (142910127360 : R) * h ^ 4 * w1 ^ 9 * e3 * b7
    + (12256645040640 : R) * h ^ 4 * w1 ^ 8 * a2 * b7
    - (148106859264 : R) * h ^ 3 * w1 ^ 11 * e1n * b8n
    + (51719855616 : R) * h ^ 3 * w1 ^ 10 * e3 * b8n
    - (4409798215680 : R) * h ^ 3 * w1 ^ 9 * a2 * b8n
    - (243596808 : R) * h ^ 2 * w1 ^ 12 * b7
    + (67814496 : R) * h * w1 ^ 13 * b8n

end AlignedSquareTowerScale610

end Max11DegreeRoutes
