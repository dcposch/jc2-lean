import LowScale68SecondaryLaterDeepFiveToSixEndgame

/-! # The row-one face in the later-deep five-to-six chamber

This module closes the two spurious families left by the I4/I3/row-zero
classification.  The only surviving top packet is `e = 0`, `a*b = 3*d`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSixRowOne68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The usual top-product/derivative formula remains valid when the degree
bound on the differentiated factor is zero. -/
theorem coeff_mul_mul_derivative_at_bounds_nonneg68
    (p q r : k[X]) (u v w : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hr : r.natDegree ≤ w) :
    (p * q * derivative r).coeff (u + v + w - 1) =
      p.coeff u * q.coeff v * r.coeff w * (w : k) := by
  by_cases hw : 0 < w
  · exact coeff_mul_mul_derivative_at_bounds68 p q r u v w hw hp hq hr
  · have hw0 : w = 0 := Nat.eq_zero_of_not_pos hw
    subst w
    rw [eq_C_of_natDegree_le_zero hr, derivative_C]
    simp

end LaterDeepFiveToSixRowOne68
end Max11DegreeRoutes
