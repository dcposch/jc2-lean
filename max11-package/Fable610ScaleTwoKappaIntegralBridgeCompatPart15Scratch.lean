import Fable610ScaleTwoKappaIntegralBridgeCompatPart13Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart14Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- On the fifteenth-face jet the cleared `κ` defect factors exactly as
`h⁴⁸` times its factored order-`48` head plus `h` times the tail. -/
theorem bridgeClearedKappaDefect610_jet_factored
    (h w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedKappaDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h * p31) p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62)
        (h ^ 2 * q52) q4 q3 q2 q1 lambda =
      h ^ 48 *
        (bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4 +
          h * bridgeKappaJetTail610 h w1 a41 p31 s1 u1 b62 q52 p2 p1
            p0 q4 q3 q2 q1 (Polynomial.C lambda)) := by
  unfold bridgeClearedKappaDefect610 bridgeKappaJetHead610 bridgeKappaJetTail610
  ring

end BridgeKappaJetFactor610

end Max11DegreeRoutes
