import Grok610DegreeZeroOrder72Part02Scratch
import Grok610DegreeZeroOrder72Part03Scratch

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

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetOrderThree610_p32P21P1Zero
    (w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R)
    (hp32 : p32 = 0) (hp21 : p21 = 0) (hp1 : p1 = 0) :
    degreeZeroPostCollapseJetOrderThree610 w1 a42 p32 p21 p1 p0 s2 u2
        b63 q53 q41 q3 q2 q1 lambda =
      degreeZeroPostCollapseP32P21P1ZeroOrderThree610 w1 a42 p0 q41
        q3 := by
  simp only [degreeZeroPostCollapseJetOrderThree610,
    degreeZeroPostCollapseP32P21P1ZeroOrderThree610, hp32, hp21, hp1]
  ring

end DegreeZeroOrderThreeHead610

end Max11DegreeRoutes
