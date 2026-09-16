import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0600 (a b c e g : Nat)
    (q0 : 4 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    4 * a < b + 2 * c ∧ 2 * a + c < b + 2 * c ∧ a + 2 * b < b + 2 * c ∧ a + e < b + 2 * c ∧ 2 * c < b + 2 * c ∧ g < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0601 (a b c d e g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0602 (a b c e f g : Nat)
    (q0 : 4 * a ≤ e + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : f = 0)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0603 (a b c d e g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0604 (a b c e f g : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0605 (a b c d e g : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0606 (a b c d e g : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0607 (a b c e g : Nat)
    (q0 : 4 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0608 (a b c e g : Nat)
    (q0 : 4 * a ≤ b + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0609 (a b c d e g : Nat)
    (q0 : 4 * a ≤ c + d)
    (q1 : 5 * a > 2 * d)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0610 (a b c e g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0611 (a b c e g : Nat)
    (q0 : 3 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c ∧ a + c < b + 2 * c ∧ 2 * b < b + 2 * c ∧ e < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0612 (a b c d e g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : d = 0)
    (q3 : e < a + c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0613 (a b c e f g : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : f = 0)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0614 (a b c d e g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0615 (a b c e f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : f = 0)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0616 (a b c d e g : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0617 (a b c d e g : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : d = 0)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0618 (a b c e g : Nat)
    (q0 : 3 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0619 (a b c e g : Nat)
    (q0 : 3 * a ≤ b + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0620 (a b c d e g : Nat)
    (q0 : 3 * a ≤ c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0621 (a b c e g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a ≤ b)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0622 (a b c e f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : f = 0)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0623 (a b c e g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0624 (a b c e g : Nat)
    (q0 : 2 * a < b + 2 * c)
    (q1 : c + g = 2 * e)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    2 * a < b + 2 * c ∧ c < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0625 (a b c d e g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : c + g = 2 * e)
    (q2 : d = 0)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0626 (a b c e f g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : c + g = 2 * e)
    (q2 : e < a + c)
    (q3 : f = 0)
    (q4 : g = 2 * c) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0627 (a b c e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    4 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0628 (a b c e g : Nat)
    (q0 : 4 * a + b < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0629 (a b c d e g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : c + g = 2 * e)
    (q2 : d = 0)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0630 (a b c e f g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : c + g = 2 * e)
    (q2 : e < a + c)
    (q3 : f = 0)
    (q4 : g = 2 * c) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0631 (a b c e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0632 (a b c e g : Nat)
    (q0 : 3 * a + b < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ b + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0633 (a b c d e g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : c + g = 2 * e)
    (q2 : d = 0)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0634 (a b c e f g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : c + g = 2 * e)
    (q2 : e < a + c)
    (q3 : f = 0)
    (q4 : g = 2 * c) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0635 (a b c e g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0636 (a b c e g : Nat)
    (q0 : 2 * a + b < 3 * c)
    (q1 : c + g = 2 * e)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    2 * a + b < 3 * c ∧ b + c < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0637 (a b c : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c) :
    4 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0638 (a b c : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c) :
    4 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0639 (a b c e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c) :
    4 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0640 (a b c e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    4 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0641 (a b c e g : Nat)
    (q0 : 4 * a + b + c < 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 3 * a + 3 * b < 4 * c ∧ 3 * a + b + e < 4 * c ∧ 2 * a + b + 2 * c < 4 * c ∧ a + 3 * b + c < 4 * c ∧ 5 * b < 4 * c ∧ a + b + c + e < 4 * c ∧ 3 * b + e < 4 * c ∧ b + 3 * c < 4 * c ∧ b + c + g < 4 * c ∧ b + 2 * e < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0642 (a b c : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c) :
    3 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0643 (a b c : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c) :
    3 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0644 (a b c e : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c) :
    3 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0645 (a b c e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    3 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0646 (a b c e g : Nat)
    (q0 : 3 * a + b + c < 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a + b + c < 4 * c ∧ 2 * a + 3 * b < 4 * c ∧ 2 * a + b + e < 4 * c ∧ a + b + 2 * c < 4 * c ∧ 3 * b + c < 4 * c ∧ b + c + e < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0647 (a b c : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a ≤ 4 * b) :
    2 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0648 (a b c : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c) :
    2 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0649 (a b c e : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c) :
    2 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0650 (a b c e g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    2 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0651 (a b c e g : Nat)
    (q0 : 2 * a + b + c < 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a + b + c < 4 * c ∧ a + 3 * b < 4 * c ∧ a + b + e < 4 * c ∧ b + 2 * c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0652 (a b c f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b)
    (q4 : g < a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0653 (a b c f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b)
    (q4 : g < a + 2 * b) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0654 (a b c f g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0655 (a b c f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0656 (a b c e g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : e = 0)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0657 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0658 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0659 (a b c f g : Nat)
    (q0 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0660 (a b c e g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : e = 0)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0661 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : g < 2 * a + c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0662 (a b c f g : Nat)
    (q0 : 3 * a + b < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0663 (a b c e g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : e = 0)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0664 (a b c f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : g < 2 * a + c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0665 (a b c f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < c + g)
    (q4 : g = 2 * c) :
    2 * a + b < 3 * c ∧ b + c < 3 * c ∧ f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0666 (a b c f g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0667 (a b c f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0668 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0669 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0670 (a b c f g : Nat)
    (q0 : 4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 3 * a + 3 * b < 4 * c ∧ 4 * a + f < 4 * c ∧ 2 * a + b + 2 * c < 4 * c ∧ a + 3 * b + c < 4 * c ∧ 5 * b < 4 * c ∧ 2 * a + c + f < 4 * c ∧ a + 2 * b + f < 4 * c ∧ b + 3 * c < 4 * c ∧ b + c + g < 4 * c ∧ 2 * c + f < 4 * c ∧ f + g < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0671 (a b c f g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : g = 2 * c) :
    3 * a + b + c < 4 * c ∧ 3 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0672 (a b c f g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g = 2 * c) :
    3 * a + b + c < 4 * c ∧ 3 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0673 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a + b + c < 4 * c ∧ 3 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0674 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a + b + c < 4 * c ∧ 3 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0675 (a b c f g : Nat)
    (q0 : 3 * a + b + c < 4 * c ∧ 3 * a + f < 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a + b + c < 4 * c ∧ 2 * a + 3 * b < 4 * c ∧ 3 * a + f < 4 * c ∧ a + b + 2 * c < 4 * c ∧ 3 * b + c < 4 * c ∧ a + c + f < 4 * c ∧ 2 * b + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0676 (a b c f g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a + b + f < c + g)
    (q2 : a ≤ 4 * b)
    (q3 : g = 2 * c) :
    2 * a + b + c < 4 * c ∧ 2 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0677 (a b c f g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g = 2 * c) :
    2 * a + b + c < 4 * c ∧ 2 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0678 (a b c f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    2 * a + b + c < 4 * c ∧ 2 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0679 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    2 * a + b + c < 4 * c ∧ 2 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0680 (a b c f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b + c < 4 * c ∧ 2 * a + f < 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < c + g)
    (q4 : g = 2 * c) :
    2 * a + b + c < 4 * c ∧ a + 3 * b < 4 * c ∧ 2 * a + f < 4 * c ∧ b + 2 * c < 4 * c ∧ c + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0681 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 6 * a ≤ e + f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0682 (a b c d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 6 * a ≤ b + c + e)
    (q3 : c = 0)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0683 (a b c d g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 6 * a ≤ 2 * c + d)
    (q3 : c = 0)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0684 (a b c d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 6 * a ≤ 3 * b + c)
    (q2 : c = 0)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0685 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + g < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0686 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ e + f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0687 (a b c d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ b + c + e)
    (q3 : c = 0)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0688 (a b c d g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ 2 * c + d)
    (q3 : c = 0)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0689 (a b c d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a ≤ 3 * b + c)
    (q2 : c = 0)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0690 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a < a + 3 * b)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0691 (a b c d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ 2 * c + d)
    (q3 : c = 0)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0692 (a b c d g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ c + d)
    (q3 : c = 0)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0693 (a b e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 3 * a < a + 3 * b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0694 (a b c d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ 2 * c + d)
    (q3 : c = 0)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0695 (a b c d g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ c + d)
    (q3 : c = 0)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0696 (a b c d g : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : c = 0)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0697 (a b c d g : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : c = 0)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0698 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0699 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b)
    (q3 : d + e < b + g)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0700 (a b d e : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : d < a + b) :
    2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0701 (a b d e : Nat)
    (q0 : 2 * a + b + e < 2 * a + 4 * b)
    (q1 : d < a + b) :
    2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0702 (a b d e f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 6 * a ≤ e + f)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0703 (a b c e g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a > e)
    (q3 : 6 * a ≤ b + c + e)
    (q4 : c = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0704 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0705 (a b d e f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a ≤ e + f)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0706 (a b c d e g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ b + c + e)
    (q3 : c = 0)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0707 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    4 * a < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0708 (a b d e f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ e + f)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0709 (a b c e g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ b + c + e)
    (q3 : c = 0)
    (q4 : e = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0710 (a b c d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ 2 * c + d)
    (q2 : c = 0)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0711 (a b : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a < a + 3 * b) :
    3 * a < a + 3 * b ∧ 2 * b < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0712 (a b e f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ e + f)
    (q2 : e = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0713 (a b f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ 2 * b + f)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0714 (a b c d e g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ b + c + e)
    (q2 : c = 0)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0715 (a b c d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ 2 * c + d)
    (q2 : c = 0)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0716 (a b f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ f)
    (q2 : f < 2 * a + b)
    (q3 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0717 (a b f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 2 * b + f)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0718 (a b c d e g : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : c = 0)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0719 (a b f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0720 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * f < 2 * g)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0721 (a b f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * f < 2 * g)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0722 (a b f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : f < 2 * a + b)
    (q3 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0723 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0724 (a b f g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : g = a + 2 * b) :
    3 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0725 (a b d f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    3 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0726 (a b f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : f < 2 * a + b)
    (q3 : g = a + 2 * b) :
    3 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0727 (a b f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : f < 2 * a + b)
    (q3 : g = a + 2 * b) :
    3 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0728 (a b d f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + f < 2 * a + 4 * b)
    (q2 : a + 2 * f < 2 * g)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0729 (a b f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a ≤ 4 * b)
    (q2 : g = a + 2 * b) :
    2 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0730 (a c : Nat)
    (q0 : 0 < a)
    (q1 : c = 0) :
    ¬ (3 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0731 (a b d f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    2 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0732 (a b f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : f < 2 * a + b)
    (q3 : g = a + 2 * b) :
    2 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0733 (a b f g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g = a + 2 * b) :
    2 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0734 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * a + 4 * b)
    (q2 : d < a + b) :
    a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0735 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 6 * a ≤ d + g)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0736 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ e + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0737 (a b d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ 2 * b + d)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0738 (a b e f g : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0739 (a b c e f : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 6 * a ≤ b + c + e)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0740 (a b d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 6 * a ≤ b + 2 * d)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0741 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 6 * a ≤ 2 * c + d)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0742 (a b c e f : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 6 * a ≤ 3 * b + c)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0743 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    5 * a < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0744 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ d + g)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0745 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ e + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0746 (a b d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 2 * b + d)
    (q3 : 5 * a > 2 * d)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0747 (a b e f g : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0748 (a b c e f : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a ≤ b + c + e)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0749 (a b d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ b + 2 * d)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0750 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ 2 * c + d)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0751 (a b c e f : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a ≤ 3 * b + c)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0752 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    4 * a < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0753 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ d + g)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0754 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ e + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0755 (a b d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ 2 * b + d)
    (q3 : 5 * a > 2 * d)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0756 (a b e f g : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0757 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + c + e)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : c = 0)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0758 (a b d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ b + 2 * d)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0759 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 2 * c + d)
    (q3 : 5 * a > 2 * d)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0760 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b + c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : c = 0)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0761 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + e)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0762 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ c + d)
    (q3 : 5 * a > 2 * d)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0763 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0764 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a < a + 3 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    3 * a < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0765 (a b d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + g)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0766 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ e + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0767 (a b d e f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0768 (a b e f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0769 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c + e)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : c = 0)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0770 (a b d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + 2 * d)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0771 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ 2 * c + d)
    (q3 : 5 * a > 2 * d)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0772 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 3 * b + c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : c = 0)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0773 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + e)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0774 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ c + d)
    (q3 : 5 * a > 2 * d)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0775 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : a ≤ b)
    (q4 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0776 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0777 (a b c e f g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0)
    (q6 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0778 (a b d e f g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0)
    (q5 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0779 (a b e f g : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0780 (a b d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : a ≤ 2 * b + d)
    (q4 : d = 0)
    (q5 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0781 (a b e f g : Nat)
    (q0 : 2 * a ≤ 2 * b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0782 (a b c e f g : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : c = 0)
    (q5 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0783 (a b d e f g : Nat)
    (q0 : 2 * a ≤ b + 2 * d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0)
    (q5 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0784 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : c = 0)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0785 (a b c e f g : Nat)
    (q0 : 2 * a ≤ 3 * b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : c = 0)
    (q5 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0786 (a b e f g : Nat)
    (q0 : 2 * a ≤ b + e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0787 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : c = 0)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0788 (a b e f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0789 (a b e f g : Nat)
    (q0 : 2 * a ≤ f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0790 (a b c e f g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * a ≤ b + c)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : c = 0)
    (q6 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0791 (a b d e f g : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0)
    (q5 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0792 (a b e f g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    3 * a + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0793 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : c = 0)
    (q4 : e + g < 2 * a + b + f) :
    ¬ (7 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0794 (a b d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : d = 0)
    (q4 : e + g < 2 * a + b + f) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0795 (a b e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    3 * a + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0796 (a b e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    3 * a + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0797 (a b e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    3 * a + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0798 (a b e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + f < a + 2 * b + e)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0799 (a b e f g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    2 * a + f < a + 2 * b + e := by
  omega

end Max11DegreeRoutes
