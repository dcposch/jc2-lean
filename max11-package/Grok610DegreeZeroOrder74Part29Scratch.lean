import Grok610DegreeZeroOrder74Part09Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32Q41Q3P21P1ZeroOrderFive610_eval
    (w1 a42 p32n p0 u2 b63 q1 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32Q41Q3P21P1ZeroOrderFive610 w1 a42 p32n p0
        u2 b63 q1).eval a =
      degreeZeroPostCollapseP32Q41Q3P21P1ZeroOrderFive610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p0.eval a) (u2.eval a)
        (b63.eval a) (q1.eval a) := by
  simp only [degreeZeroPostCollapseP32Q41Q3P21P1ZeroOrderFive610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
