import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart07Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuJetFactor610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the order-`59` head. -/
theorem bridgeMuJetHead610_eval
    (w1 a41 p32 s1 u2 b62 q53 p2 q41 q3 : k[X]) (lambda : k) (x : k) :
    (bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 p2 q41 q3
        (Polynomial.C lambda)).eval x =
      bridgeMuJetHead610 (w1.eval x) (a41.eval x) (p32.eval x)
        (s1.eval x) (u2.eval x) (b62.eval x) (q53.eval x)
        (p2.eval x) (q41.eval x) (q3.eval x) lambda := by
  simp only [bridgeMuJetHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_C]

end BridgeMuJetFactor610

end Max11DegreeRoutes
