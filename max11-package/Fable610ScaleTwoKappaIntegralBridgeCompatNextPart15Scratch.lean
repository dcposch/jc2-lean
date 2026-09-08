import Fable610ScaleTwoKappaIntegralBridgeCompatNextPart07Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free kill: modulo the tenth-face root laws alone the
vanishing order-`52` head forces `7971615 p₃₁⁴ = 0`, hence
`p₃₁ = 0`. -/
theorem bridgeLambda_chamberFree_kill610
    (p31 u1 q4 : F)
    (hhead : bridgeLambdaJetHead610 p31 u1 q4 = 0)
    (hu : (3 : F) * u1 = (5 : F) * p31)
    (hq4 : (9 : F) * q4 = (5 : F) * p31 ^ 2) :
    p31 = 0 := by
  simp only [bridgeLambdaJetHead610] at hhead
  have h4 : p31 ^ 4 = 0 := by
    linear_combination (1 / 7971615 : F) * hhead -
      (7 / 3 : F) * p31 ^ 3 * hu + (4 / 5 : F) * p31 ^ 2 * hq4
  by_contra hne
  exact pow_ne_zero 4 hne h4

end BridgeLambdaScalars610

end Max11DegreeRoutes
