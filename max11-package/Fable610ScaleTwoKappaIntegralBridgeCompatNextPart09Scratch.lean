import LowScale46SourceBridge

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaJet610

variable {R : Type*} [CommRing R]

/-- Order-`54` head of the merged-jet cleared `λ` defect: the
coefficient of `h⁵⁴` after the globally merged deeper jet
`p₃ = h² p₃₂`, `q₇ = h⁶ u₂`, `q₅ = h³ q₅₃`, `q₄ = h q₄₁` is
substituted into `bridgeClearedLambdaDefect610`, kept factored through
its content `39366`. -/
def bridgeLambdaDeepHead610 (a41 s1 b62 p2 q41 : R) : R :=
  (39366 : R) *
    ((792 : R) * a41 ^ 5 * s1 - (770 : R) * a41 ^ 6 -
      (810 : R) * a41 ^ 4 * b62 + (4950 : R) * a41 ^ 4 * p2 -
      (4320 : R) * a41 ^ 3 * p2 * s1 + (810 : R) * a41 ^ 3 * q41 +
      (3645 : R) * a41 ^ 2 * b62 * p2 - (8100 : R) * a41 ^ 2 * p2 ^ 2 +
      (4860 : R) * a41 * p2 ^ 2 * s1 - (2916 : R) * a41 * p2 * q41 -
      (2187 : R) * b62 * p2 ^ 2 + (2025 : R) * p2 ^ 3)

end BridgeLambdaJet610

end Max11DegreeRoutes
