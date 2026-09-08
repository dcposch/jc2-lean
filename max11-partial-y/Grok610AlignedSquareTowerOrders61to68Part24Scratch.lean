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

/-- Order-`61` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder61610 {R : Type*} [CommRing R] (w1n e1 e3 a2 b8 : R) : R :=
    (25607321026560 : R) * w1n * e1 ^ 6 * b8
    - (1338189034291200 : R) * w1n * e1 ^ 4 * a2 * b8
    + (17342929884413952 : R) * w1n * e1 ^ 2 * a2 ^ 2 * b8
    - (32860288202047488 : R) * w1n * a2 ^ 3 * b8
    - (3304170455040 : R) * e1 ^ 5 * e3 * b8
    + (142740163657728 : R) * e1 ^ 3 * e3 * a2 * b8
    - (1217047711186944 : R) * e1 * e3 * a2 ^ 2 * b8

end Max11DegreeRoutes
