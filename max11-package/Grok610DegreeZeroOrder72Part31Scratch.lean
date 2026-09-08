import Grok610DegreeZeroOrder72Part17Scratch

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

/-- Honest vanishing of the mixed `q41'` cofactor. -/
theorem degreeZeroPostCollapseQ41ZeroMixedOrderOne610_split
    (w1 a42 p32 p21 p1 q53 q41n q3 u2 : F)
    (hhead :
      degreeZeroPostCollapseQ41ZeroMixedOrderOne610 w1 a42 p32 p21 p1
        q53 q41n q3 u2 = 0) :
    degreeZeroPostCollapseQ41ZeroMixedOrderOneCofactor610 w1 a42 p32
        p21 p1 q53 q41n q3 u2 = 0 := by
  rw [degreeZeroPostCollapseQ41ZeroMixedOrderOne610_factor] at hhead
  exact (mul_eq_zero.mp hhead).resolve_left (by norm_num)

end DegreeZeroOrderThreeSplit610

end Max11DegreeRoutes
