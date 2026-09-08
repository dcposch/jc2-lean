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

/-- Order-`62` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder62610 {R : Type*} [CommRing R] (e1 e3 a2 a1 b8 b7 : R) : R :=
    - (4336723722240 : R) * e1 ^ 6 * b7
    + (281019697201152 : R) * e1 ^ 4 * a2 * b7
    + (321165368229888 : R) * e1 ^ 4 * a1 * b8
    + (293704040448 : R) * e1 ^ 2 * e3 ^ 3 * b8
    - (4792125362798592 : R) * e1 ^ 2 * a2 ^ 2 * b7
    - (10953429400682496 : R) * e1 ^ 2 * a2 * a1 * b8
    - (1669475598336 : R) * e3 ^ 3 * a2 * b8
    + (13270501004673024 : R) * a2 ^ 3 * b7
    + (45498860587450368 : R) * a2 ^ 2 * a1 * b8

end Max11DegreeRoutes
