import Grok610DegreeZeroOrder74Part08Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32Q41Q3P21P1ZeroOrderFour610_eval
    (w1 a42 p32n p0 q53 q41n q3n q2 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32Q41Q3P21P1ZeroOrderFour610 w1 a42 p32n p0
        q53 q41n q3n q2).eval a =
      degreeZeroPostCollapseP32Q41Q3P21P1ZeroOrderFour610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p0.eval a) (q53.eval a)
        (q41n.eval a) (q3n.eval a) (q2.eval a) := by
  simp only [degreeZeroPostCollapseP32Q41Q3P21P1ZeroOrderFour610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
