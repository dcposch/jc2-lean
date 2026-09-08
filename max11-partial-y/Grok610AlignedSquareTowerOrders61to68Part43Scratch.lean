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
/-- Order-`65` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder65610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) : R :=
    (13381890342912 : R) * e1 ^ 5 * b5
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
