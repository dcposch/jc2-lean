import Fable610ScaleTwoTerminalIntegralBridgeScratch

/-! # Ground splits after the `(6,10)` terminal integral bridge

The peeled `ι` relation leaves two factored ground packets.  This file
normalizes those factors without expanding the weight-fifty source identity.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section TerminalIntegralGroundSplits610

variable {F : Type*} [Field F] [CharZero F]

/-- The complementary terminal packet has a small exact normal form.  If the
factor `p₃₁` vanishes, its two loaded rows already pin `p₂` and `b₆₂`.  If it
does not vanish, the peeled `ι` cofactor can be cancelled and the same rows
pin `p₂` and `b₆₂` in terms of `λp₃₁` and `p₃₁w₁`. -/
theorem terminalIotaComplement_groundSplit610
    (a41 p2 p31 w1 b62 lam : F)
    (hP : (240 : F) * p2 - 40 * a41 ^ 2 - 27 * lam * p31 -
      40 * p31 * w1 = 0)
    (hB : (144 : F) * b62 - 120 * a41 ^ 2 + 45 * lam * p31 -
      200 * p31 * w1 = 0)
    (hIota : p31 ^ 2 * (5 * a41 ^ 2 + 2 * p31 * w1) = 0) :
    (p31 = 0 ∧ 6 * p2 - a41 ^ 2 = 0 ∧ 6 * b62 - 5 * a41 ^ 2 = 0) ∨
      (p31 ≠ 0 ∧ 5 * a41 ^ 2 + 2 * p31 * w1 = 0 ∧
        80 * p2 - 9 * lam * p31 - 8 * p31 * w1 = 0 ∧
        144 * b62 + 45 * lam * p31 - 152 * p31 * w1 = 0) := by
  by_cases hp31 : p31 = 0
  · left
    subst p31
    simp only [mul_zero, zero_mul, sub_zero] at hP hB
    refine ⟨rfl, ?_, ?_⟩
    · linear_combination (1 / 40 : F) * hP
    · linear_combination (1 / 24 : F) * hB
  · right
    have hp31sq : p31 ^ 2 ≠ 0 := pow_ne_zero 2 hp31
    have hcore : 5 * a41 ^ 2 + 2 * p31 * w1 = 0 :=
      (mul_eq_zero.mp hIota).resolve_left hp31sq
    refine ⟨hp31, hcore, ?_, ?_⟩
    · linear_combination (1 / 3 : F) * hP + (8 / 3 : F) * hcore
    · linear_combination hB + 24 * hcore

/-- The deeper `p₃₁ = 0` sibling of the peeled `ι` relation splits into the
zero `a₄₁` child and one explicit quartic factor. -/
theorem terminalIotaLeft_groundSplit610
    (a41 p2 : F)
    (hIota : a41 * (4 * a41 ^ 4 - 35 * p2 * a41 ^ 2 + 90 * p2 ^ 2) = 0) :
    a41 = 0 ∨ 4 * a41 ^ 4 - 35 * p2 * a41 ^ 2 + 90 * p2 ^ 2 = 0 := by
  exact mul_eq_zero.mp hIota

end TerminalIntegralGroundSplits610

#print axioms terminalIotaComplement_groundSplit610
#print axioms terminalIotaLeft_groundSplit610

end Max11DegreeRoutes
