import Grok610DegreeZeroSplitChildrenPart04Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderOneEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseJetOrderOne610_eval
    (w1 a42 p32 p21 p1 q53 q41 q3 u2 : k[X]) (a : k) :
    (degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53 q41 q3
        u2).eval a =
      degreeZeroPostCollapseJetOrderOne610 (w1.eval a) (a42.eval a)
        (p32.eval a) (p21.eval a) (p1.eval a) (q53.eval a) (q41.eval a)
        (q3.eval a) (u2.eval a) := by
  simp only [degreeZeroPostCollapseJetOrderOne610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

end DegreeZeroOrderOneEval610

end Max11DegreeRoutes
