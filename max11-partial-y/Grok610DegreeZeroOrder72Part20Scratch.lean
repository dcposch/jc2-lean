import Grok610DegreeZeroOrder72Part11Scratch
import Grok610DegreeZeroOrder72Part12Scratch

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
theorem degreeZeroPostCollapseQ41ZeroMixedFiveReduced610_identity
    (w1 a42 p32 p21 p1 q53 q41n q3 u2 : R) :
    (10 : R) * p32 ^ 2 *
          degreeZeroPostCollapseQ41ZeroMixedOrderOneCofactor610 w1 a42
            p32 p21 p1 q53 q41n q3 u2 -
        (7560 * p21 * p32 ^ 2 - 5460 * p32 ^ 3 * w1) *
          (10 * p32 ^ 2 * q53 + (18 * p32 * w1 - 27 * p21) * q3) =
      (10 : R) * p32 ^ 2 *
        degreeZeroPostCollapseQ41ZeroMixedFiveReduced610 w1 a42 p32
          p21 p1 q41n q3 u2 := by
  simp only [degreeZeroPostCollapseQ41ZeroMixedOrderOneCofactor610,
    degreeZeroPostCollapseQ41ZeroMixedFiveReduced610]
  ring

end DegreeZeroOrderThreeHead610

end Max11DegreeRoutes
