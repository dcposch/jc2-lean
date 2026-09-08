import Grok610DegreeZeroOrder72Part10Scratch

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
theorem degreeZeroPostCollapseQ41ZeroMixedOrderOne610_headEq
    (h w1 a42 p32 p21 p1 q53 q41n q3 u2 : R) :
    degreeZeroPostCollapseJetHead610 p32 (h * q41n) +
        h *
          degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53
            (h * q41n) q3 u2 =
      h *
          degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21
            p1 q53 q41n q3 u2 +
        h ^ 2 *
          (45498860587450368 * a42 * p21 * p32 * q41n -
            49290432303071232 * a42 * p32 ^ 2 * q41n * w1 -
            38999023360671744 * p1 * p21 * q41n +
            45498860587450368 * p1 * p32 * q41n * w1 +
            22749430293725184 * p21 ^ 2 * q41n * w1 -
            49290432303071232 * p21 * p32 * q41n * w1 ^ 2 +
            26014394826620928 * p32 ^ 2 * q41n * w1 ^ 3) := by
  simp only [degreeZeroPostCollapseJetHead610,
    degreeZeroPostCollapseJetOrderOne610,
    degreeZeroPostCollapseQ41ZeroMixedOrderOne610]
  ring

end DegreeZeroOrderThreeHead610

end Max11DegreeRoutes
