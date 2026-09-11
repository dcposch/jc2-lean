import LowScale46SourceBridge

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuJet610

variable {R : Type*} [CommRing R]

/-- Order-`59` head of the jet-substituted cleared `μ` defect: the
coefficient of `h⁵⁹` after the globally merged jet `p₅ = h⁵ w₁`,
`p₄ = h³ a₄₁`, `p₃ = h² p₃₂`, `q₈ = h⁷ s₁`, `q₇ = h⁶ u₂`,
`q₆ = h⁴ b₆₂`, `q₅ = h³ q₅₃`, `q₄ = h q₄₁` is substituted into
`bridgeClearedMuDefect610`, kept factored through its content
`4096`. -/
def bridgeMuJetHead610
    (w1 a41 p32 s1 u2 b62 q53 p2 q41 q3 lam : R) : R :=
  (4096 : R) *
    ((840 : R) * a41 ^ 6 * w1
      + (63 : R) * a41 ^ 6 * lam
      - (1260 : R) * a41 ^ 5 * p32
      - (1008 : R) * a41 ^ 5 * s1 * w1
      + (196 : R) * a41 ^ 5 * u2
      - (4200 : R) * a41 ^ 4 * p2 * w1
      - (420 : R) * a41 ^ 4 * p2 * lam
      + (1120 : R) * a41 ^ 4 * p32 * s1
      + (840 : R) * a41 ^ 4 * b62 * w1
      - (200 : R) * a41 ^ 4 * q53
      + (5600 : R) * a41 ^ 3 * p2 * p32
      + (4480 : R) * a41 ^ 3 * p2 * s1 * w1
      - (1120 : R) * a41 ^ 3 * p2 * u2
      - (960 : R) * a41 ^ 3 * p32 * b62
      - (640 : R) * a41 ^ 3 * q41 * w1
      + (192 : R) * a41 ^ 3 * q3
      + (4800 : R) * a41 ^ 2 * p2 ^ 2 * w1
      + (720 : R) * a41 ^ 2 * p2 ^ 2 * lam
      - (3840 : R) * a41 ^ 2 * p2 * p32 * s1
      - (2880 : R) * a41 ^ 2 * p2 * b62 * w1
      + (960 : R) * a41 ^ 2 * p2 * q53
      + (768 : R) * a41 ^ 2 * p32 * q41
      - (4800 : R) * a41 * p2 ^ 2 * p32
      - (3840 : R) * a41 * p2 ^ 2 * s1 * w1
      + (1344 : R) * a41 * p2 ^ 2 * u2
      + (2304 : R) * a41 * p2 * p32 * b62
      + (1536 : R) * a41 * p2 * q41 * w1
      - (768 : R) * a41 * p2 * q3
      - (640 : R) * p2 ^ 3 * w1
      - (192 : R) * p2 ^ 3 * lam
      + (1536 : R) * p2 ^ 2 * p32 * s1
      + (1152 : R) * p2 ^ 2 * b62 * w1
      - (640 : R) * p2 ^ 2 * q53
      - (1024 : R) * p2 * p32 * q41)

end BridgeMuJet610

end Max11DegreeRoutes
