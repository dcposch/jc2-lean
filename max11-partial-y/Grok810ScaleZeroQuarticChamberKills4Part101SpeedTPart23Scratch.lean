import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4600 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + 2 * e)
    (q2 : b + g = d + e)
    (q3 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4601 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 2 * c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4602 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ c + d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4603 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4604 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 3 * b + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4605 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4606 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4607 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 5 * b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4608 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4609 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ d + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4610 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a ≤ b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4611 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4612 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4613 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4614 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4615 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4616 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a < a + 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    3 * a < a + 2 * b + d ∧ a + c < a + 2 * b + d ∧ 2 * b < a + 2 * b + d ∧ e < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4617 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ f + g)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4618 (a b d f g : Nat)
    (q0 : 2 * a ≤ 2 * b + f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4619 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + c + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4620 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + d + f)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4621 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + 2 * e)
    (q2 : b + g = d + e)
    (q3 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4622 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 2 * c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4623 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ c + d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4624 (a b c d g : Nat)
    (q0 : 2 * a ≤ 3 * b + c)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4625 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 3 * b + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4626 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4627 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4628 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 5 * b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4629 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4630 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ d + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4631 (a b d g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4632 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4633 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4634 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4635 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4636 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a ≤ b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4637 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ f)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4638 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4639 (a b c d g : Nat)
    (q0 : 2 * a < a + 2 * b + d)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 2 * b + d ∧ c < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4640 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4641 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4642 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4643 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4644 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4645 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4646 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4647 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4648 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4649 (a b c d f : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4650 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4651 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4652 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4653 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4654 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + d < a + b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a + d < a + b + c + d ∧ 3 * a + b + c < a + b + c + d ∧ 2 * a + 3 * b < a + b + c + d ∧ 3 * a + f < a + b + c + d ∧ 2 * a + c + d < a + b + c + d ∧ a + 2 * b + d < a + b + c + d ∧ a + b + 2 * c < a + b + c + d ∧ 3 * b + c < a + b + c + d ∧ a + c + f < a + b + c + d ∧ 2 * b + f < a + b + c + d ∧ b + 2 * d < a + b + c + d ∧ 2 * c + d < a + b + c + d ∧ d + g < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4655 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4656 (a b c d f : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4657 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4658 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a ≤ b)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4659 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4660 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4661 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + d < a + b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + b + c + d ∧ 2 * a + b + c < a + b + c + d ∧ a + 3 * b < a + b + c + d ∧ 2 * a + f < a + b + c + d ∧ a + c + d < a + b + c + d ∧ 2 * b + d < a + b + c + d ∧ b + 2 * c < a + b + c + d ∧ c + f < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4662 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4663 (a b c d f : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4664 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4665 (a b c d f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4666 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4667 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4668 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4669 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4670 (a b c d f : Nat)
    (q0 : 2 * a + d < a + b + c + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + b + c + d ∧ a + b + c < a + b + c + d ∧ 3 * b < a + b + c + d ∧ a + f < a + b + c + d ∧ c + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4671 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4672 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4673 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + b + c < 2 * a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4674 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4675 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4676 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + b + c < 2 * a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4677 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4678 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4679 (a b c d f : Nat)
    (q0 : 2 * a + b + c < 2 * a + 4 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4680 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ d + g)
    (q2 : a + 2 * f = 2 * g)
    (q3 : d < a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4681 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 6 * a ≤ e + f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4682 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 6 * a ≤ b + c + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4683 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4684 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ d + g)
    (q2 : a + 2 * f = 2 * g)
    (q3 : d < a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4685 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ e + f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4686 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ b + c + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4687 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4688 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ d + g)
    (q2 : a + 2 * f = 2 * g)
    (q3 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4689 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ e + f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4690 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ b + c + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4691 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ b + e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4692 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4693 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + g)
    (q2 : a + 2 * f = 2 * g)
    (q3 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4694 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ e + f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4695 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4696 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4697 (a b d f g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4698 (a b d e f : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : e = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4699 (a b c d e f : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4700 (a b d e f : Nat)
    (q0 : 2 * a ≤ b + e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4701 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 7 * a ≤ f + g)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4702 (a b c d f g : Nat)
    (q0 : 7 * a ≤ b + c + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4703 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 7 * a ≤ b + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4704 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 7 * a ≤ c + d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4705 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 7 * a ≤ 3 * b + e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4706 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a < a + 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    6 * a < a + 2 * b + d ∧ 4 * a + c < a + 2 * b + d ∧ 3 * a + 2 * b < a + 2 * b + d ∧ 2 * a + b + d < a + 2 * b + d ∧ 2 * a + 2 * c < a + 2 * b + d ∧ a + 2 * b + c < a + 2 * b + d ∧ 4 * b < a + 2 * b + d ∧ 2 * a + g < a + 2 * b + d ∧ a + b + f < a + 2 * b + d ∧ a + 2 * d < a + 2 * b + d ∧ b + c + d < a + 2 * b + d ∧ 3 * c < a + 2 * b + d ∧ c + g < a + 2 * b + d ∧ d + f < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4707 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ f + g)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4708 (a b c d f g : Nat)
    (q0 : 6 * a ≤ b + c + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4709 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ b + 2 * e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4710 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 6 * a ≤ c + d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4711 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 6 * a ≤ 3 * b + e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4712 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a < a + 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    5 * a < a + 2 * b + d ∧ 3 * a + c < a + 2 * b + d ∧ 2 * a + 2 * b < a + 2 * b + d ∧ a + b + d < a + 2 * b + d ∧ a + 2 * c < a + 2 * b + d ∧ 2 * b + c < a + 2 * b + d ∧ a + g < a + 2 * b + d ∧ b + f < a + 2 * b + d ∧ 2 * d < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4713 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ f + g)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4714 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + c + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4715 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4716 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ c + d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b)
    (q6 : e = 0) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4717 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ 3 * b + e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4718 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ d + e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4719 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a < a + 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a < a + 2 * b + d ∧ 2 * a + c < a + 2 * b + d ∧ a + 2 * b < a + 2 * b + d ∧ b + d < a + 2 * b + d ∧ 2 * c < a + 2 * b + d ∧ g < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4720 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ f + g)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4721 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + c + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4722 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4723 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ c + d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4724 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b + e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4725 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ d + e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4726 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ b + e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4727 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a < a + 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d ∧ a + c < a + 2 * b + d ∧ 2 * b < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4728 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f + g)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4729 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + c + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4730 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4731 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ c + d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b)
    (q5 : e = 0) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4732 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 3 * b + e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4733 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4734 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4735 (a b c e f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4736 (a b c e f g : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4737 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ d + e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4738 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4739 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ 2 * b + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4740 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4741 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4742 (a b c e f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4743 (a b c e f g : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4744 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ d + e)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4745 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : a ≤ b)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4746 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 2 * b + d)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4747 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4748 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4749 (a b c e f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4750 (a b c e f g : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4751 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4752 (a b c e f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4753 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ 2 * b + d)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4754 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4755 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4756 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4757 (a b c e f g : Nat)
    (q0 : 2 * a + b < a + 2 * b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4758 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4759 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4760 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4761 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4762 (a b c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4763 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + b + c < a + 2 * b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4764 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4765 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4766 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4767 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4768 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4769 (a b c e f g : Nat)
    (q0 : 2 * a + b + c < a + 2 * b + e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4770 (a b c e f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4771 (a b c e f g : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4772 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ d + e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4773 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4774 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ 2 * b + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4775 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4776 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + b + c < 2 * a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4777 (a b c e f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4778 (a b c e f g : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4779 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ d + e)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4780 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : a ≤ b)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4781 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 2 * b + d)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4782 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4783 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + b + c < 2 * a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4784 (a b c e f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4785 (a b c e f g : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4786 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4787 (a b c e f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4788 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ 2 * b + d)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4789 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4790 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4791 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4792 (a b c e f g : Nat)
    (q0 : 2 * a + b + c < 2 * a + 4 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4793 (a b c e f g : Nat)
    (q0 : 6 * a ≤ b + c + e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4794 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 6 * a ≤ 2 * c + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4795 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4796 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4797 (a b c e f g : Nat)
    (q0 : 5 * a ≤ b + c + e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4798 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ 2 * c + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4799 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a < a + 3 * b := by
  omega

end Max11DegreeRoutes
