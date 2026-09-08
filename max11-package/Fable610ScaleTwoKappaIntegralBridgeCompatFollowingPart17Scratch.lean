import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart09Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- On the collapsed sibling child the vanishing order-`61` deep head
factors as `p₃₂` times its cofactor — the honest split `p₃₂ = 0`
(whence `u₂ = 0` through the retained tie) or the first `λ`-loaded
tie on the quotient jet. -/
theorem bridgeMu_siblingDeepSplit610
    (w1 p32 u2 b63 p21 q42 q31 lam : F)
    (hhead : bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31 lam = 0)
    (htie : (3 : F) * u2 = (5 : F) * p32) :
    (p32 = 0 ∧ u2 = 0) ∨
      (45 : F) * lam * p32 ^ 3 + (144 : F) * b63 * p32 ^ 2 +
          (240 : F) * p21 * p32 ^ 2 + (288 : F) * p32 * q42 * w1 -
        (400 : F) * p32 ^ 3 * w1 - (144 : F) * p32 * q31 -
          (384 : F) * p21 * q42 = 0 := by
  simp only [bridgeMuDeepHead610] at hhead
  have hprod : p32 *
      ((100 : F) * p32 ^ 3 * w1 + (15 : F) * p32 ^ 3 * lam +
        (48 : F) * p32 ^ 2 * b63 - (200 : F) * p32 ^ 2 * p21 -
        (140 : F) * p32 ^ 2 * u2 * w1 + (168 : F) * p32 * p21 * u2 +
        (96 : F) * p32 * q42 * w1 - (48 : F) * p32 * q31 -
        (128 : F) * p21 * q42) = 0 := by
    linear_combination (1 / 32768 : F) * hhead
  rcases mul_eq_zero.mp hprod with hp32z | hF
  · left
    refine ⟨hp32z, ?_⟩
    linear_combination (1 / 3 : F) * htie + (5 / 3 : F) * hp32z
  · right
    linear_combination (3 : F) * hF +
      (-(168 : F) * p21 * p32 + (140 : F) * p32 ^ 2 * w1) * htie

end BridgeMuScalars610

end Max11DegreeRoutes
