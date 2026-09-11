import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart02Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart07Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart08Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- On the fifteenth-face jet the cleared `λ` defect factors exactly as
`h⁵²` times its factored order-`52` head plus `h` times the tail. -/
theorem bridgeClearedLambdaDefect610_jet_factored
    (h w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedLambdaDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h * p31) p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62)
        (h ^ 2 * q52) q4 q3 q2 q1 lambda =
      h ^ 52 *
        (bridgeLambdaJetHead610 p31 u1 q4 +
          h * bridgeLambdaJetTail610 h w1 a41 p31 s1 u1 b62 q52 p2 p1
            p0 q4 q3 q2 q1 (Polynomial.C lambda)) := by
  unfold bridgeClearedLambdaDefect610 bridgeLambdaJetHead610 bridgeLambdaJetTail610
  ring

end BridgeLambdaJetFactor610

end Max11DegreeRoutes
