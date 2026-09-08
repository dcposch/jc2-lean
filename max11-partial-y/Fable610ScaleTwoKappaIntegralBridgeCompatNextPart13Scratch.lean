import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart07Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the order-`52` head. -/
theorem bridgeLambdaJetHead610_eval
    (p31 u1 q4 : k[X]) (x : k) :
    (bridgeLambdaJetHead610 p31 u1 q4).eval x =
      bridgeLambdaJetHead610 (p31.eval x) (u1.eval x) (q4.eval x) := by
  simp only [bridgeLambdaJetHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

end BridgeLambdaJetFactor610

end Max11DegreeRoutes
