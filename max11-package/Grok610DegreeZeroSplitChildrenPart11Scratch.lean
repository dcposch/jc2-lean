import Grok610DegreeZeroSplitChildrenPart06Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderOneEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32ZeroOrderOne610_eval
    (w1 p21 p1 q41 q3 : k[X]) (a : k) :
    (degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3).eval a =
      degreeZeroPostCollapseP32ZeroOrderOne610 (w1.eval a) (p21.eval a)
        (p1.eval a) (q41.eval a) (q3.eval a) := by
  simp only [degreeZeroPostCollapseP32ZeroOrderOne610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]

end DegreeZeroOrderOneEval610

end Max11DegreeRoutes
