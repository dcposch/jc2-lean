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

/-- Order-`64` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder64610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b8 b7 b6 : R) : R :=
    (8921260228608 : R) * e1 ^ 4 * e3 * b6
    - (304261927796736 : R) * e1 ^ 2 * e3 * a2 * b6
    - (354972249096192 : R) * e1 ^ 2 * e3 * a1 * b7
    - (405682570395648 : R) * e1 ^ 2 * e3 * a0 * b8
    - (13525843968 : R) * e3 ^ 4 * b7
    + (1263857238540288 : R) * e3 * a2 ^ 2 * b6
    + (2949000223260672 : R) * e3 * a2 * a1 * b7
    + (3370285969440768 : R) * e3 * a2 * a0 * b8
    + (1685142984720384 : R) * e3 * a1 ^ 2 * b8

end Max11DegreeRoutes
