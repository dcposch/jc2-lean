import Grok610DegreeZeroOrder72Part06Scratch

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

theorem degreeZeroPostCollapseP32P21ZeroOrderThreeHead610_eval
    (w1 a42 p32n p21n p1 p0 u2 b63 q53 q41 q3 q2 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32P21ZeroOrderThreeHead610 w1 a42 p32n p21n
        p1 p0 u2 b63 q53 q41 q3 q2).eval a =
      degreeZeroPostCollapseP32P21ZeroOrderThreeHead610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
        (p0.eval a) (u2.eval a) (b63.eval a) (q53.eval a) (q41.eval a)
        (q3.eval a) (q2.eval a) := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderThreeHead610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]

end DegreeZeroOrderThreeEval610

end Max11DegreeRoutes
