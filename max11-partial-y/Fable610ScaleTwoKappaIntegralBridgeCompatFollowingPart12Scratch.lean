import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart02Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart09Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart10Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- On the sibling-child deeper jet the cleared `μ` defect factors
exactly as `h⁶¹` times its order-`61` head plus `h` times the deep
tail. -/
theorem bridgeClearedMuDefect610_deepJet_factored
    (h w1 a42 p32 s2 u2 b63 q54 p21 p1 p0 q42 q31 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedMuDefect610 h (h ^ 5 * w1) (h ^ 4 * a42)
        (h ^ 2 * p32) (h * p21) p1 p0 (h ^ 8 * s2) (h ^ 6 * u2)
        (h ^ 5 * b63) (h ^ 4 * q54) (h ^ 2 * q42) (h * q31) q2 q1
        lambda =
      h ^ 61 *
        (bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31
            (Polynomial.C lambda) +
          h * bridgeMuDeepTail610 h w1 a42 p32 s2 u2 b63 q54 p21 p1
            p0 q42 q31 q2 q1 (Polynomial.C lambda)) := by
  unfold bridgeClearedMuDefect610 bridgeMuDeepHead610 bridgeMuDeepTail610
  ring

end BridgeMuJetFactor610

end Max11DegreeRoutes
