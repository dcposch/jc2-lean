import Grok610DegreeZeroOrder72Part33Scratch

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

/-- Honest scalar split of the order-`71` eight-term residual at
`p21 = 0`. -/
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_p21Zero_split
    (w1 a42 p21 p1 q53 q41n q3n u2 : F)
    (hhead :
      degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610 w1 a42 p21 p1
        q53 q41n q3n u2 = 0)
    (hp21 : p21 = 0) : p1 = 0 ∨ q53 = 0 := by
  rw [degreeZeroPostCollapseP32Q41Q3ZeroOrderTwoHead610_p21Zero w1 a42
    p21 p1 q53 q41n q3n u2 hp21] at hhead
  rcases mul_eq_zero.mp hhead with hprod | hq53
  · rcases mul_eq_zero.mp hprod with hconstant | hp1sq
    · exact (by norm_num : (-24374389600419840 : F) ≠ 0).elim hconstant
    · exact Or.inl
        ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hp1sq)
  · exact Or.inr hq53

end DegreeZeroOrderThreeSplit610

end Max11DegreeRoutes
