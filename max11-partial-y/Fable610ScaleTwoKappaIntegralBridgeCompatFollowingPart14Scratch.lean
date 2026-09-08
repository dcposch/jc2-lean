import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart09Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuJetFactor610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the order-`61` deep head. -/
theorem bridgeMuDeepHead610_eval
    (w1 p32 u2 b63 p21 q42 q31 : k[X]) (lambda : k) (x : k) :
    (bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31
        (Polynomial.C lambda)).eval x =
      bridgeMuDeepHead610 (w1.eval x) (p32.eval x) (u2.eval x)
        (b63.eval x) (p21.eval x) (q42.eval x) (q31.eval x)
        lambda := by
  simp only [bridgeMuDeepHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_C]

end BridgeMuJetFactor610

end Max11DegreeRoutes
