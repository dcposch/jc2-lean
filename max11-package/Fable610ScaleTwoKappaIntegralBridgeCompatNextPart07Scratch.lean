import LowScale46SourceBridge

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaJet610

variable {R : Type*} [CommRing R]

/-- Order-`52` head of the jet-substituted cleared `λ` defect: the
coefficient of `h⁵²` after the fifteenth-face jet `p₅ = h⁵ w₁`,
`p₄ = h³ a₄₁`, `p₃ = h p₃₁`, `q₈ = h⁷ s₁`, `q₇ = h⁵ u₁`, `q₆ = h⁴ b₆₂`,
`q₅ = h² q₅₂` is substituted into `bridgeClearedLambdaDefect610`,
kept in its fully factored form. -/
def bridgeLambdaJetHead610 (p31 u1 q4 : R) : R :=
  (531441 : R) * p31 ^ 2 *
    ((105 : R) * p31 * u1 - (100 : R) * p31 ^ 2 - (108 : R) * q4)

end BridgeLambdaJet610

end Max11DegreeRoutes
