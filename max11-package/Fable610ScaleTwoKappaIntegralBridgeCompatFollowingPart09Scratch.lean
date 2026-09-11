import LowScale46SourceBridge

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuJet610

variable {R : Type*} [CommRing R]

/-- Order-`61` head of the sibling-child deep jet: the coefficient of
`h⁶¹` after the deeper jet `p₄ = h⁴ a₄₂`, `p₂ = h p₂₁`, `q₈ = h⁸ s₂`,
`q₆ = h⁵ b₆₃`, `q₅ = h⁴ q₅₄`, `q₄ = h² q₄₂`, `q₃ = h q₃₁` is
substituted into `bridgeClearedMuDefect610`, kept factored as
`32768 p₃₂` times its cofactor. -/
def bridgeMuDeepHead610
    (w1 p32 u2 b63 p21 q42 q31 lam : R) : R :=
  (32768 : R) * p32 *
    ((100 : R) * p32 ^ 3 * w1
      + (15 : R) * p32 ^ 3 * lam
      + (48 : R) * p32 ^ 2 * b63
      - (200 : R) * p32 ^ 2 * p21
      - (140 : R) * p32 ^ 2 * u2 * w1
      + (168 : R) * p32 * p21 * u2
      + (96 : R) * p32 * q42 * w1
      - (48 : R) * p32 * q31
      - (128 : R) * p21 * q42)

end BridgeMuJet610

end Max11DegreeRoutes
