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

section DegreeZeroOrderThreeSplit610

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
set_option maxHeartbeats 4000000 in
/-- The order-`71` eight-term residual on `p21 = 0` is
`-24374389600419840 p1^2 q53`. -/
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_p21Zero
    (w1 a42 p21 p1 q53 q41n q3n u2 : F) (hp21 : p21 = 0) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42 p21 p1 q53
        q41n q3n u2 =
      -(24374389600419840 : F) * p1 ^ 2 * q53 := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610,
    degreeZeroPostCollapseP32ZeroOrderOne610,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderTwo610, hp21]
  ring

end DegreeZeroOrderThreeSplit610

end Max11DegreeRoutes
