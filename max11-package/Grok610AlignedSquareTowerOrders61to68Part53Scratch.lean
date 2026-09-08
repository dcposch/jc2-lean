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

/-- Order-`67` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder67610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b6 b5 b4 : R) : R :=
    - (22537920577536 : R) * e1 ^ 3 * e3 * b4
    + (561714328240128 : R) * e1 * e3 * a2 * b4
    + (702142910300160 : R) * e1 * e3 * a1 * b5
    + (842571492360192 : R) * e1 * e3 * a0 * b6

end Max11DegreeRoutes
