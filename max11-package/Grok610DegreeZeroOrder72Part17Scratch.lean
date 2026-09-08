import Grok610DegreeZeroOrder72Part10Scratch
import Grok610DegreeZeroOrder72Part11Scratch

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

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseQ41ZeroMixedOrderOne610_factor
    (w1 a42 p32 p21 p1 q53 q41n q3 u2 : R) :
    degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21 p1 q53
        q41n q3 u2 =
      (3761479876608 : R) *
        degreeZeroPostCollapseQ41ZeroMixedOrderOneCofactor610 w1 a42
          p32 p21 p1 q53 q41n q3 u2 := by
  simp only [degreeZeroPostCollapseQ41ZeroMixedOrderOne610,
    degreeZeroPostCollapseQ41ZeroMixedOrderOneCofactor610]
  ring

end DegreeZeroOrderThreeHead610

end Max11DegreeRoutes
