import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart09Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free reduction of the vanishing order-`54` head modulo
`3 s₁ = 5 a₄₁` and the `p₃₁`-killed `U`-load alone. -/
theorem bridgeLambda_deepReduction610
    (a41 s1 b62 p2 q41 : F)
    (hhead : bridgeLambdaDeepHead610 a41 s1 b62 p2 q41 = 0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hU : (10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2 = 0) :
    (100 : F) * a41 ^ 6 - (1575 : F) * a41 ^ 4 * p2 +
        (810 : F) * a41 ^ 3 * q41 + (4860 : F) * a41 ^ 2 * p2 ^ 2 -
      (2916 : F) * a41 * p2 * q41 - (1620 : F) * p2 ^ 3 = 0 := by
  simp only [bridgeLambdaDeepHead610] at hhead
  linear_combination (1 / 39366 : F) * hhead -
    (12 : F) * a41 * ((22 : F) * a41 ^ 4 - (120 : F) * a41 ^ 2 * p2 +
      (135 : F) * p2 ^ 2) * hs -
    (9 / 2 : F) * ((10 : F) * a41 ^ 4 - (45 : F) * a41 ^ 2 * p2 +
      (27 : F) * p2 ^ 2) * hU

end BridgeLambdaScalars610

end Max11DegreeRoutes
