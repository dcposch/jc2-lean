import Grok610DegreeZeroOrder72Part20Scratch

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

/-- On the five-term locus the mixed cofactor is `p32^2` times the
eight-term residual. -/
theorem degreeZeroPostCollapseQ41ZeroMixedFiveReduced610_of_five
    (w1 a42 p32 p21 p1 q53 q41n q3 u2 : F)
    (hfive :
      (10 : F) * p32 ^ 2 * q53 + (18 * p32 * w1 - 27 * p21) * q3 = 0)
    (hcof :
      degreeZeroPostCollapseQ41ZeroMixedOrderOneCofactor610 w1 a42 p32
        p21 p1 q53 q41n q3 u2 = 0) :
    p32 = 0 ∨
      degreeZeroPostCollapseQ41ZeroMixedFiveReduced610 w1 a42 p32 p21
          p1 q41n q3 u2 = 0 := by
  have hident :=
    degreeZeroPostCollapseQ41ZeroMixedFiveReduced610_identity w1 a42
      p32 p21 p1 q53 q41n q3 u2
  have hprod : (10 : F) * p32 ^ 2 *
      degreeZeroPostCollapseQ41ZeroMixedFiveReduced610 w1 a42 p32 p21
        p1 q41n q3 u2 = 0 := by
    rw [hcof, hfive] at hident
    simpa using hident.symm
  rcases mul_eq_zero.mp hprod with htenp | height
  · rcases mul_eq_zero.mp htenp with hten | hp32sq
    · exact (by norm_num : (10 : F) ≠ 0).elim hten
    · exact Or.inl
        ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hp32sq)
  · exact Or.inr height

end DegreeZeroOrderThreeSplit610

end Max11DegreeRoutes
