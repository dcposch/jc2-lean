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

/-- Order-`67` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order67610 {R : Type*} [CommRing R] (w1 e1n e3 a1 a0 b8n : R) : R :=
    (25607321026560 : R) * w1 * e1n ^ 6 * b8n
    + (3853984418758656 : R) * w1 * e1n ^ 3 * a0 * b8n
    + (45498860587450368 : R) * w1 * a0 ^ 2 * b8n
    - (3304170455040 : R) * e1n ^ 5 * e3 * b8n
    + (321165368229888 : R) * e1n ^ 4 * a1 * b8n
    - (405682570395648 : R) * e1n ^ 2 * e3 * a0 * b8n
    + (30332573724966912 : R) * e1n * a1 * a0 * b8n

end Max11DegreeRoutes
