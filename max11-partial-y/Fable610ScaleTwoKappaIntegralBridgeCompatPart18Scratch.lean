import Fable610ScaleTwoTerminalIntegralClosureScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- On the `p₃₁ ≠ 0` complement child the factored root relation
forces `a₄₁ = 0`, the retained core forces `w₁ = 0`, and the two
remaining ground relations collapse to the pins `80 p₂ = 9 λ p₃₁` and
`16 b₆₂ = -5 λ p₃₁`. -/
theorem bridgeKappa_complement_pins610
    (w1 a41 p31 p2 b62 lam : F) (hnz : p31 ≠ 0)
    (hzero : a41 * p31 ^ 3 = 0)
    (hcore : (5 : F) * a41 ^ 2 + (2 : F) * p31 * w1 = 0)
    (hp2n : (80 : F) * p2 - (9 : F) * lam * p31 -
      (8 : F) * p31 * w1 = 0)
    (hb62n : (144 : F) * b62 + (45 : F) * lam * p31 -
      (152 : F) * p31 * w1 = 0) :
    a41 = 0 ∧ w1 = 0 ∧ (80 : F) * p2 = (9 : F) * lam * p31 ∧
      (16 : F) * b62 = -(5 : F) * lam * p31 := by
  have ha : a41 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (pow_ne_zero 3 hnz)
  have hpw : p31 * w1 = 0 := by
    linear_combination (1 / 2 : F) * hcore - (5 / 2 : F) * a41 * ha
  have hw : w1 = 0 := by
    rcases mul_eq_zero.mp hpw with h | h
    · exact absurd h hnz
    · exact h
  refine ⟨ha, hw, ?_, ?_⟩
  · linear_combination hp2n + (8 : F) * p31 * hw
  · linear_combination (1 / 9 : F) * hb62n + (152 / 9 : F) * p31 * hw

end BridgeKappaScalars610

end Max11DegreeRoutes
