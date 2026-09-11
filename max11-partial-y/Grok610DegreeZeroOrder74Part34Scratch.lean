import Grok610DegreeZeroOrder74Part27Scratch
import Grok610DegreeZeroOrder74Part17Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610_eval_root
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q1 : k[X]) (lambda a : k)
    (hroot : h.eval a = 0) :
    (degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610 h w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFive610 (w1.eval a)
        (a42.eval a) (p32n.eval a) (p21.eval a) (p1.eval a)
        (p0.eval a) (s2.eval a) (u2.eval a) (b63.eval a) (q1.eval a)
        lambda := by
  rw [degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610_eval, hroot,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610_zero]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
