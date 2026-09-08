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

/-- Frozen order-`72` coefficient on `p32 = p21 = p1 = 0`. -/
def degreeZeroPostCollapseP32P21P1ZeroOrderThree610
    (w1 a42 p0 q41 q3 : R) : R :=
  -3080652018941952*a42^4*q3 + 13007197413310464*a42^4*q41*w1 + 19510796119965696*a42^3*q3*w1^2 - 36131103925862400*a42^3*q41*w1^3 - 20323745958297600*a42^2*q3*w1^4 + 28001605542543360*a42^2*q41*w1^5 - 29249267520503808*a42*p0*q3 + 45498860587450368*a42*p0*q41*w1 + 7000401385635840*a42*q3*w1^6 - 8222693691064320*a42*q41*w1^7 + 17062072720293888*p0*q3*w1^2 - 16430144101023744*p0*q41*w1^3 - 770877533537280*q3*w1^8 + 818462566471680*q41*w1^9

end DegreeZeroOrderThreeHead610

end Max11DegreeRoutes
