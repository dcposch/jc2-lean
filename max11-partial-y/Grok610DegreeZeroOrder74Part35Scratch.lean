import Grok610DegreeZeroOrder74Part31Scratch
import Grok610DegreeZeroOrder74Part19Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveEval610

variable {k : Type*} [CommRing k]

theorem degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610_eval_root
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 : k[X])
    (lambda a : k) (hroot : h.eval a = 0) :
    (degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610 h w1 a42 p32 p21
        p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 (Polynomial.C lambda)).eval
      a =
      degreeZeroPostCollapseQ41ZeroMixedOrderThree610 (w1.eval a)
        (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a) (p0.eval a)
        (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a)
        (q41n.eval a) (q3.eval a) (q2.eval a) (q1.eval a) lambda := by
  rw [degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610_eval, hroot,
    degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610_zero]

end DegreeZeroOrderFiveEval610

end Max11DegreeRoutes
