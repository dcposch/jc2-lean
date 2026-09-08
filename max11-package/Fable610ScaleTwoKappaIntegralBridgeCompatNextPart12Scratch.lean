import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart09Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart10Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- On the globally merged deeper jet the cleared `λ` defect factors
exactly as `h⁵⁴` times its order-`54` head plus `h` times the deep
tail. -/
theorem bridgeClearedLambdaDefect610_deepJet_factored
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedLambdaDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1) (h ^ 6 * u2) (h ^ 4 * b62)
        (h ^ 3 * q53) (h * q41) q3 q2 q1 lambda =
      h ^ 54 *
        (bridgeLambdaDeepHead610 a41 s1 b62 p2 q41 +
          h * bridgeLambdaDeepTail610 h w1 a41 p32 s1 u2 b62 q53 p2 p1
            p0 q41 q3 q2 q1 (Polynomial.C lambda)) := by
  unfold bridgeClearedLambdaDefect610 bridgeLambdaDeepHead610 bridgeLambdaDeepTail610
  ring

end BridgeLambdaJetFactor610

end Max11DegreeRoutes
