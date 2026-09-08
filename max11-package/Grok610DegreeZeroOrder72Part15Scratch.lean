import Grok610DegreeZeroOrder72Part06Scratch
import Grok610DegreeZeroOrder72Part07Scratch

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
theorem degreeZeroPostCollapseJetQuotient610_p32P21Scale
    (h w1 a42 p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) :
    degreeZeroPostCollapseJetQuotient610 h w1 a42 (h * p32n) (h * p21n)
        p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda =
      h ^ 2 *
          degreeZeroPostCollapseP32P21ZeroOrderTwoHead610 w1 a42 p32n
            p21n p1 q53 q41 q3 +
        h ^ 3 *
          degreeZeroPostCollapseP32P21ZeroOrderThreeHead610 w1 a42 p32n
            p21n p1 p0 u2 b63 q53 q41 q3 q2 +
        h ^ 4 *
          degreeZeroPostCollapseP32P21ZeroOrderThreePlus610 h w1 a42
            p32n p21n p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda := by
  simp only [degreeZeroPostCollapseJetQuotient610,
    degreeZeroPostCollapseP32P21ZeroOrderTwoHead610,
    degreeZeroPostCollapseJetOrderOneLinear610,
    degreeZeroPostCollapseP32P21ZeroOrderTwo610,
    degreeZeroPostCollapseP32P21ZeroOrderThreeHead610,
    degreeZeroPostCollapseP32P21ZeroOrderThreePlus610]
  ring

end DegreeZeroOrderThreeHead610

end Max11DegreeRoutes
