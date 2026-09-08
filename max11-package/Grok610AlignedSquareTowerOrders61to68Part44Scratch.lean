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
/-- Order-`65` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder65610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) : R :=
    (24980690262528 : R) * w1n ^ 9 * e1 ^ 2 * b8
    - (4409798215680 : R) * w1n ^ 9 * a2 * b8
    - (13033403615232 : R) * w1n ^ 8 * e1 * e3 * b8
    + (1655035379712 : R) * w1n ^ 7 * e3 ^ 2 * b8
    + (445110481041408 : R) * w1n ^ 6 * e1 ^ 3 * b7
    - (1555776810491904 : R) * w1n ^ 6 * e1 * a2 * b7
    - (1778030640562176 : R) * w1n ^ 6 * e1 * a1 * b8
    - (232231555325952 : R) * w1n ^ 5 * e1 ^ 2 * e3 * b7
    + (366065131880448 : R) * w1n ^ 5 * e3 * a2 * b7
    + (418360150720512 : R) * w1n ^ 5 * e3 * a1 * b8
    + (36862151639040 : R) * w1n ^ 4 * e1 * e3 ^ 2 * b7
    + (538621086302208 : R) * w1n ^ 3 * e1 ^ 4 * b6
    - (9698348948520960 : R) * w1n ^ 3 * e1 ^ 2 * a2 * b6
    - (11314740439941120 : R) * w1n ^ 3 * e1 ^ 2 * a1 * b7
    - (12931131931361280 : R) * w1n ^ 3 * e1 ^ 2 * a0 * b8
    - (1724545105920 : R) * w1n ^ 3 * e3 ^ 3 * b7
    + (15640233326936064 : R) * w1n ^ 3 * a2 ^ 2 * b6
    + (36493877762850816 : R) * w1n ^ 3 * a2 * a1 * b7
    + (41707288871829504 : R) * w1n ^ 3 * a2 * a0 * b8
    + (20853644435914752 : R) * w1n ^ 3 * a1 ^ 2 * b8
    - (187346464800768 : R) * w1n ^ 2 * e1 ^ 3 * e3 * b6
    + (2281964458475520 : R) * w1n ^ 2 * e1 * e3 * a2 * b6
    + (2662291868221440 : R) * w1n ^ 2 * e1 * e3 * a1 * b7
    + (3042619277967360 : R) * w1n ^ 2 * e1 * e3 * a0 * b8
    + (17842520457216 : R) * w1n * e1 ^ 2 * e3 ^ 2 * b6
    - (101420642598912 : R) * w1n * e3 ^ 2 * a2 * b6
    - (118324083032064 : R) * w1n * e3 ^ 2 * a1 * b7
    - (135227523465216 : R) * w1n * e3 ^ 2 * a0 * b8
    + (13381890342912 : R) * e1 ^ 5 * b5
    - (760654819491840 : R) * e1 ^ 3 * a2 * b5
    - (912785783390208 : R) * e1 ^ 3 * a1 * b6
    - (1064916747288576 : R) * e1 ^ 3 * a0 * b7
    - (417368899584 : R) * e1 * e3 ^ 3 * b6
    + (9478929289052160 : R) * e1 * a2 ^ 2 * b5
    + (22749430293725184 : R) * e1 * a2 * a1 * b6
    + (26541002009346048 : R) * e1 * a2 * a0 * b7
    + (13270501004673024 : R) * e1 * a1 ^ 2 * b7
    + (30332573724966912 : R) * e1 * a1 * a0 * b8

end Max11DegreeRoutes
