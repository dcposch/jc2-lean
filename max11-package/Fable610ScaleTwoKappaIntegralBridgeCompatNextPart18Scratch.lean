import Fable610ScaleTwoKappaIntegralBridgeCompatScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- On the pinned complement child the chamber-free sextic relation
factors as `a₄₁³ (324 q₄₁ - 35 a₄₁³) = 0` — the honest split
`a₄₁ = 0 ∨ 324 q₄₁ = 35 a₄₁³`. -/
theorem bridgeLambda_complementSplit610
    (a41 p2 q41 : F)
    (hG : (100 : F) * a41 ^ 6 - (1575 : F) * a41 ^ 4 * p2 +
        (810 : F) * a41 ^ 3 * q41 + (4860 : F) * a41 ^ 2 * p2 ^ 2 -
      (2916 : F) * a41 * p2 * q41 - (1620 : F) * p2 ^ 3 = 0)
    (hpin : (6 : F) * p2 - a41 ^ 2 = 0) :
    a41 = 0 ∨ (324 : F) * q41 = (35 : F) * a41 ^ 3 := by
  have hprod : a41 ^ 3 * ((324 : F) * q41 - (35 : F) * a41 ^ 3) = 0 := by
    linear_combination hG +
      ((3 : F) * a41 * ((5 : F) * a41 ^ 3 + (162 : F) * q41) -
        (225 / 2 : F) * a41 ^ 2 * ((6 : F) * p2 - a41 ^ 2) +
        (15 / 2 : F) * ((6 : F) * p2 - a41 ^ 2) ^ 2) * hpin
  rcases mul_eq_zero.mp hprod with h3 | hlin
  · left
    by_contra hne
    exact pow_ne_zero 3 hne h3
  · right
    linear_combination hlin

end BridgeLambdaScalars610

end Max11DegreeRoutes
