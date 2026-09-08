import Grok610DegreeZeroOrder71GrandchildScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderThreeHead610

variable {R : Type*} [CommRing R]

/-- Eight-term residual after the five-term cofactor eliminates `q53`
from the mixed `q41'` head. -/
def degreeZeroPostCollapseQ41ZeroMixedFiveReduced610
    (w1 a42 p32 p21 p1 q41n q3 u2 : R) : R :=
  (4536 : R) * a42 * p32 ^ 2 * q3 - 7776 * p1 * p32 * q3 +
    16524 * p21 ^ 2 * q3 - 19278 * p21 * p32 * q3 * w1 +
    1729 * p32 ^ 5 - 1911 * p32 ^ 4 * u2 + 2016 * p32 ^ 3 * q41n +
    4914 * p32 ^ 2 * q3 * w1 ^ 2

end DegreeZeroOrderThreeHead610

end Max11DegreeRoutes
