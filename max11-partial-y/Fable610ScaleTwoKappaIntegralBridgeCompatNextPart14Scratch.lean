import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart09Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the order-`54` head. -/
theorem bridgeLambdaDeepHead610_eval
    (a41 s1 b62 p2 q41 : k[X]) (x : k) :
    (bridgeLambdaDeepHead610 a41 s1 b62 p2 q41).eval x =
      bridgeLambdaDeepHead610 (a41.eval x) (s1.eval x) (b62.eval x)
        (p2.eval x) (q41.eval x) := by
  simp only [bridgeLambdaDeepHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

end BridgeLambdaJetFactor610

end Max11DegreeRoutes
