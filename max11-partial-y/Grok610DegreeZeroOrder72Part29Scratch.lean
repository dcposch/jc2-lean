import Grok610DegreeZeroOrder72Part101Scratch

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

section DegreeZeroOrderThreeEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseQ41ZeroMixedOrderOneCofactor610_eval
    (w1 a42 p32 p21 p1 q53 q41n q3 u2 : k[X]) (a : k) :
    (degreeZeroPostCollapseQ41ZeroMixedOrderOneCofactor610 w1 a42 p32
        p21 p1 q53 q41n q3 u2).eval a =
      degreeZeroPostCollapseQ41ZeroMixedOrderOneCofactor610 (w1.eval a)
        (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a)
        (q53.eval a) (q41n.eval a) (q3.eval a) (u2.eval a) := by
  simp only [degreeZeroPostCollapseQ41ZeroMixedOrderOneCofactor610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat]

end DegreeZeroOrderThreeEval610

end Max11DegreeRoutes
