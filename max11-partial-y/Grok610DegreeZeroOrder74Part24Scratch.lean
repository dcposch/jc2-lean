import Grok610DegreeZeroOrder74Part04Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32P21ZeroOrderFive610_eval
    (w1 a42 p32n p21n p1 p0 s2 u2 b63 q1 : k[X]) (lambda a : k) :
    (degreeZeroPostCollapseP32P21ZeroOrderFive610 w1 a42 p32n p21n p1 p0
        s2 u2 b63 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32P21ZeroOrderFive610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21n.eval a) (p1.eval a)
        (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a) (q1.eval a)
        lambda := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderFive610,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_C]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
