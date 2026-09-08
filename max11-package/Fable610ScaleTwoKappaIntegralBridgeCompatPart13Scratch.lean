import Fable610ScaleTwoKappaIntegralBridgeCompatPart05Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaJet610

variable {R : Type*} [CommRing R]

/-- Order-`48` head of the jet-substituted cleared `κ` defect: the
coefficient of `h⁴⁸` after the fifteenth-face jet `p₅ = h⁵ w₁`,
`p₄ = h³ a₄₁`, `p₃ = h p₃₁`, `q₈ = h⁷ s₁`, `q₇ = h⁵ u₁`, `q₆ = h⁴ b₆₂`,
`q₅ = h² q₅₂` is substituted into `bridgeClearedKappaDefect610`,
kept in its fully factored form. -/
def bridgeKappaJetHead610 (a41 p31 s1 u1 q52 q4 : R) : R :=
  (4837294080 : R) * p31 *
    ((264 : R) * p31 ^ 2 * s1 + (693 : R) * a41 * p31 * u1 -
      (935 : R) * a41 * p31 ^ 2 - (432 : R) * a41 * q4 -
      (270 : R) * p31 * q52)

end BridgeKappaJet610

end Max11DegreeRoutes
