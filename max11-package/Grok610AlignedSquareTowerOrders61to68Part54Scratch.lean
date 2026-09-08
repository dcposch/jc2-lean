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
/-- Order-`67` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder67610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : R) : R :=
    (67814496 : R) * w1n ^ 13 * b8
    + (407293862976 : R) * w1n ^ 10 * e1 * b7
    - (142910127360 : R) * w1n ^ 9 * e3 * b7
    + (100543399317504 : R) * w1n ^ 7 * e1 ^ 2 * b6
    - (33618226397184 : R) * w1n ^ 7 * a2 * b6
    - (39221264130048 : R) * w1n ^ 7 * a1 * b7
    - (44824301862912 : R) * w1n ^ 7 * a0 * b8
    - (49389740015616 : R) * w1n ^ 6 * e1 * e3 * b6
    + (5810557648896 : R) * w1n ^ 5 * e3 ^ 2 * b6
    + (710912924467200 : R) * w1n ^ 4 * e1 ^ 3 * b5
    - (4706551695605760 : R) * w1n ^ 4 * e1 * a2 * b5
    - (5647862034726912 : R) * w1n ^ 4 * e1 * a1 * b6
    - (6589172373848064 : R) * w1n ^ 4 * e1 * a0 * b7
    - (299331757670400 : R) * w1n ^ 3 * e1 ^ 2 * e3 * b5
    + (965446501662720 : R) * w1n ^ 3 * e3 * a2 * b5
    + (1158535801995264 : R) * w1n ^ 3 * e3 * a1 * b6
    + (1351625102327808 : R) * w1n ^ 3 * e3 * a0 * b7
    + (35215500902400 : R) * w1n ^ 2 * e1 * e3 ^ 2 * b5
    + (160582684114944 : R) * w1n * e1 ^ 4 * b4
    - (5476714700341248 : R) * w1n * e1 ^ 2 * a2 * b4
    - (6845893375426560 : R) * w1n * e1 ^ 2 * a1 * b5
    - (8215072050511872 : R) * w1n * e1 ^ 2 * a0 * b6
    - (1043422248960 : R) * w1n * e3 ^ 3 * b5
    + (22749430293725184 : R) * w1n * a2 ^ 2 * b4
    + (56873575734312960 : R) * w1n * a2 * a1 * b5
    + (68248290881175552 : R) * w1n * a2 * a0 * b6
    + (34124145440587776 : R) * w1n * a1 ^ 2 * b6
    + (79623006028038144 : R) * w1n * a1 * a0 * b7
    + (45498860587450368 : R) * w1n * a0 ^ 2 * b8
    - (22537920577536 : R) * e1 ^ 3 * e3 * b4
    + (561714328240128 : R) * e1 * e3 * a2 * b4
    + (702142910300160 : R) * e1 * e3 * a1 * b5
    + (842571492360192 : R) * e1 * e3 * a0 * b6

end Max11DegreeRoutes
