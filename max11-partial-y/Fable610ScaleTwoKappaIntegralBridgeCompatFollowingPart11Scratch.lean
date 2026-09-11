import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart101Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart08Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- On the globally merged jet the cleared `μ` defect factors exactly
as `h⁵⁹` times its factored order-`59` head plus `h` times the
tail. -/
theorem bridgeClearedMuDefect610_jet_factored
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedMuDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1) (h ^ 6 * u2) (h ^ 4 * b62)
        (h ^ 3 * q53) (h * q41) q3 q2 q1 lambda =
      h ^ 59 *
        (bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 p2 q41 q3
            (Polynomial.C lambda) +
          h * bridgeMuJetTail610 h w1 a41 p32 s1 u2 b62 q53 p2 p1
            p0 q41 q3 q2 q1 (Polynomial.C lambda)) := by
  unfold bridgeClearedMuDefect610 bridgeMuJetHead610 bridgeMuJetTail610
  ring

end BridgeMuJetFactor610

end Max11DegreeRoutes
