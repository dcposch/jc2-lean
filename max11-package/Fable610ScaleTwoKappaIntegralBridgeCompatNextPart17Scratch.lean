import Fable610ScaleTwoKappaIntegralBridgeCompatScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- On the sibling child the retained `q₄₁` tie reduces the
chamber-free sextic relation to `10 a₄₁⁶ - 99 a₄₁⁴ p₂ + 324 a₄₁² p₂²
- 324 p₂³ = 0`; the `a₄₁ = 0` branch forces `p₂ = 0` and the quartic
branch is killed by the resultant certificate `167832 p₂⁴`, so the
child collapses to `a₄₁ = 0 ∧ p₂ = 0`. -/
theorem bridgeLambda_siblingCollapse610
    (a41 p2 q41 : F)
    (hG : (100 : F) * a41 ^ 6 - (1575 : F) * a41 ^ 4 * p2 +
        (810 : F) * a41 ^ 3 * q41 + (4860 : F) * a41 ^ 2 * p2 ^ 2 -
      (2916 : F) * a41 * p2 * q41 - (1620 : F) * p2 ^ 3 = 0)
    (hq41 : (81 : F) * q41 - (90 : F) * a41 * p2 +
      (5 : F) * a41 ^ 3 = 0)
    (hsplit : a41 = 0 ∨
      (4 : F) * a41 ^ 4 - (35 : F) * p2 * a41 ^ 2 +
        (90 : F) * p2 ^ 2 = 0) :
    a41 = 0 ∧ p2 = 0 := by
  have hf1 : (10 : F) * a41 ^ 6 - (99 : F) * a41 ^ 4 * p2 +
      (324 : F) * a41 ^ 2 * p2 ^ 2 - (324 : F) * p2 ^ 3 = 0 := by
    linear_combination (1 / 5 : F) * hG -
      (2 / 5 : F) * a41 * ((5 : F) * a41 ^ 2 - (18 : F) * p2) * hq41
  rcases hsplit with ha41 | hquart
  · refine ⟨ha41, ?_⟩
    have hp3 : p2 ^ 3 = 0 := by
      linear_combination (-(1 : F) / 324) * hf1 +
        (((10 : F) * a41 ^ 5 - (99 : F) * a41 ^ 3 * p2 +
          (324 : F) * a41 * p2 ^ 2) / 324) * ha41
    by_contra hne
    exact pow_ne_zero 3 hne hp3
  · have hp4 : p2 ^ 4 = 0 := by
      linear_combination
        (((52 : F) * a41 ^ 2 - (2543 : F) * p2) / 167832) * hf1 +
        ((-(130 : F) * a41 ^ 4 + (6507 : F) * a41 ^ 2 * p2 -
          (7290 : F) * p2 ^ 2) / 167832) * hquart
    have hp2z : p2 = 0 := by
      by_contra hne
      exact pow_ne_zero 4 hne hp4
    have ha4 : a41 ^ 4 = 0 := by
      linear_combination (1 / 4 : F) * hquart +
        (((35 : F) * a41 ^ 2 - (90 : F) * p2) / 4) * hp2z
    have ha41z : a41 = 0 := by
      by_contra hne
      exact pow_ne_zero 4 hne ha4
    exact ⟨ha41z, hp2z⟩

end BridgeLambdaScalars610

end Max11DegreeRoutes
