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
/-- Frozen order-`65` coefficient of the MixedPair jet (`h^11` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder65610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 : R) : R :=
    (1068273617748480 : R) * w1 ^ 8 * e1 * a1
    + (21307883950080 : R) * w1 ^ 7 * e1 * e3 ^ 2
    + (259751681280000 : R) * w1 ^ 6 * e1 ^ 3 * e3
    - (1714090051215360 : R) * w1 ^ 6 * e1 * e3 * a2
    + (18102121906176 : R) * w1 ^ 6 * e1 * b3
    + (208859712122880 : R) * w1 ^ 5 * e1 ^ 5
    - (6732763578777600 : R) * w1 ^ 5 * e1 ^ 3 * a2
    + (30711438336983040 : R) * w1 ^ 5 * e1 * a2 ^ 2
    - (139453383573504 : R) * w1 ^ 4 * e1 * e3 * b4
    - (718396218408960 : R) * w1 ^ 3 * e1 ^ 3 * b4
    + (6951214811971584 : R) * w1 ^ 3 * e1 * a2 * b4
    + (8689018514964480 : R) * w1 ^ 3 * e1 * a1 * b5
    + (10426822217957376 : R) * w1 ^ 3 * e1 * a0 * b6
    + (35215500902400 : R) * w1 ^ 2 * e1 * e3 ^ 2 * b5
    + (89212602286080 : R) * w1 * e1 ^ 3 * e3 * b5
    - (1521309638983680 : R) * w1 * e1 * e3 * a2 * b5
    - (1825571566780416 : R) * w1 * e1 * e3 * a1 * b6
    - (2129833494577152 : R) * w1 * e1 * e3 * a0 * b7
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
