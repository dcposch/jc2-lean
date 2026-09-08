import Fable610ScaleTwoKappaIntegralBridgeCompatPart13Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the order-`48` head. -/
theorem bridgeKappaJetHead610_eval
    (a41 p31 s1 u1 q52 q4 : k[X]) (x : k) :
    (bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4).eval x =
      bridgeKappaJetHead610 (a41.eval x) (p31.eval x) (s1.eval x)
        (u1.eval x) (q52.eval x) (q4.eval x) := by
  simp only [bridgeKappaJetHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

end BridgeKappaJetFactor610

end Max11DegreeRoutes
