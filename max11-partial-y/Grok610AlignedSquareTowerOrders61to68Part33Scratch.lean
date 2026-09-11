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

/-- Order-`63` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder63610 {R : Type*} [CommRing R] (e1 e3 a2 a1 b8 b7 : R) : R :=
    (2312919318528 : R) * e1 ^ 3 * e3 ^ 2 * b7
    - (39441361010688 : R) * e1 * e3 ^ 2 * a2 * b7
    - (45075841155072 : R) * e1 * e3 ^ 2 * a1 * b8

end Max11DegreeRoutes
