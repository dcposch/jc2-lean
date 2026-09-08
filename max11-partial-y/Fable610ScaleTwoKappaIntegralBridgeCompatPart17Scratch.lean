import Fable610ScaleTwoKappaIntegralBridgeCompatPart13Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free reduction of the vanishing order-`48` head modulo the
tenth-face root laws alone: the head reduces to the exact factored
relation `a₄₁ p₃₁³ = 0`. -/
theorem bridgeKappa_chamberFree_split610
    (a41 p31 s1 u1 q52 q4 : F)
    (hhead : bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4 = 0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hu : (3 : F) * u1 = (5 : F) * p31)
    (hq52 : (9 : F) * q52 = (10 : F) * a41 * p31)
    (hq4 : (9 : F) * q4 = (5 : F) * p31 ^ 2) :
    a41 * p31 ^ 3 = 0 := by
  simp only [bridgeKappaJetHead610] at hhead
  linear_combination (1 / 580475289600 : F) * hhead -
      (11 / 15 : F) * p31 ^ 3 * hs -
      (77 / 40 : F) * a41 * p31 ^ 2 * hu +
      (1 / 4 : F) * p31 ^ 2 * hq52 + (2 / 5 : F) * a41 * p31 * hq4

end BridgeKappaScalars610

end Max11DegreeRoutes
