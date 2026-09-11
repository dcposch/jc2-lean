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

/-- Order-`66` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder66610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b7 b6 b5 : R) : R :=
    - (4695400120320 : R) * e1 ^ 2 * e3 ^ 2 * b5
    + (39007939461120 : R) * e3 ^ 2 * a2 * b5
    + (46809527353344 : R) * e3 ^ 2 * a1 * b6
    + (54611115245568 : R) * e3 ^ 2 * a0 * b7

end Max11DegreeRoutes
