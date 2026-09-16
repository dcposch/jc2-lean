import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3600 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a + b < a + 2 * b + c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    3 * a + b < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3601 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 3 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3602 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 3 * a ≤ c + f)
    (q3 : a + 2 * f = 2 * g) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3603 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : d = 0)
    (q5 : e + g < 2 * a + b + f)
    (q6 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3604 (a b c e f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3605 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ 2 * b + d)
    (q4 : 5 * a > 2 * d)
    (q5 : a + 2 * b = 2 * c)
    (q6 : a + 2 * f = 2 * g)
    (q7 : d = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3606 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ b + 2 * c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3607 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ f)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3608 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ b + c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3609 (a b c e f g : Nat)
    (q0 : 2 * a + b < a + 2 * b + c)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3610 (a b c e f g : Nat)
    (q0 : 2 * f < e + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    3 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3611 (a b c e f g : Nat)
    (q0 : 2 * f < e + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    3 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3612 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * f = 2 * g)
    (q4 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3613 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    3 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3614 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    3 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3615 (a b c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    3 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3616 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a + b + c < a + 2 * b + e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3617 (a b c e f g : Nat)
    (q0 : 2 * f < e + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    2 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3618 (a b c e f g : Nat)
    (q0 : 2 * f < e + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    2 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3619 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * f = 2 * g)
    (q4 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3620 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 9 * a ≤ 4 * e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3621 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3622 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3623 (a b c e f g : Nat)
    (q0 : 2 * a + b + c < a + 2 * b + e)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3624 (a b c e f g : Nat)
    (q0 : 2 * f < e + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a ≤ 4 * b) :
    a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3625 (a b c e f g : Nat)
    (q0 : 2 * f < e + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ 4 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3626 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * f = 2 * g)
    (q4 : d = 0) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3627 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 7 * a ≤ 4 * e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3628 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 9 * a ≤ 4 * f)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3629 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    a + b + c < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3630 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + b + c < a + 2 * b + e) :
    a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3631 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3632 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ c + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3633 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f)
    (q7 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3634 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ 3 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3635 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a > 2 * d)
    (q4 : 5 * a ≤ 2 * b + d)
    (q5 : a + 2 * b = 2 * c)
    (q6 : a + 2 * f = 2 * g)
    (q7 : d = 0) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3636 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a ≤ b + 2 * c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3637 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a + b + c < 2 * a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3638 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 4 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3639 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 4 * a ≤ c + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3640 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ d + e)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f)
    (q7 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3641 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a ≤ b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3642 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ 2 * b + d)
    (q4 : 5 * a > 2 * d)
    (q5 : a + 2 * b = 2 * c)
    (q6 : a + 2 * f = 2 * g)
    (q7 : d = 0) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3643 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ b + 2 * c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3644 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a + b + c < 2 * a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3645 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 3 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3646 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 3 * a ≤ c + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3647 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : d = 0)
    (q5 : e + g < 2 * a + b + f)
    (q6 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3648 (a b c e f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3649 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ 2 * b + d)
    (q4 : 5 * a > 2 * d)
    (q5 : a + 2 * b = 2 * c)
    (q6 : a + 2 * f = 2 * g)
    (q7 : d = 0) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3650 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ b + 2 * c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3651 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ f)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3652 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ b + c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3653 (a b c e f g : Nat)
    (q0 : 2 * a + b + c < 2 * a + 4 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3654 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 6 * a ≤ d + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3655 (a b c e f g : Nat)
    (q0 : 6 * a ≤ e + f)
    (q1 : b + g = c + f)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3656 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d = 0)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3657 (a b c e f g : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : a + b + f < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3658 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 6 * a ≤ b + 2 * d)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d = 0)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3659 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 6 * a ≤ 2 * c + d)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3660 (a b c e f g : Nat)
    (q0 : 6 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3661 (a b c e f g : Nat)
    (q0 : 5 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    5 * a < b + 2 * c ∧ 3 * a + c < b + 2 * c ∧ 2 * a + 2 * b < b + 2 * c ∧ 2 * a + e < b + 2 * c ∧ a + 2 * c < b + 2 * c ∧ 2 * b + c < b + 2 * c ∧ a + g < b + 2 * c ∧ b + f < b + 2 * c ∧ c + e < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3662 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 5 * a ≤ d + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3663 (a b c e f g : Nat)
    (q0 : 5 * a ≤ e + f)
    (q1 : b + g = c + f)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3664 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d = 0)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3665 (a b c e f g : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : a + b + f < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3666 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 5 * a ≤ b + 2 * d)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3667 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 5 * a ≤ 2 * c + d)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3668 (a b c e f g : Nat)
    (q0 : 5 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3669 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3670 (a b c e f g : Nat)
    (q0 : 4 * a ≤ e + f)
    (q1 : b + g = c + f)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3671 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d = 0)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3672 (a b c e f g : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : a + b + f < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3673 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 4 * a ≤ b + 2 * d)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3674 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3675 (a b c e f g : Nat)
    (q0 : 4 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3676 (a b c e f g : Nat)
    (q0 : 4 * a ≤ b + e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3677 (a b c e f g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3678 (a b c e f g : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : b + g = c + f)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3679 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3680 (a b c e f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + b + f < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3681 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 3 * a ≤ b + 2 * d)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3682 (a b c e f g : Nat)
    (q0 : 3 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3683 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 3 * a ≤ c + d)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3684 (a b c e f g : Nat)
    (q0 : a + b + f < c + g)
    (q1 : a ≤ b)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3685 (a b c e f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3686 (a b c e f g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3687 (a b c e g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3688 (a b c e g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3689 (a b c d e f g : Nat)
    (q0 : a + b + f < c + g)
    (q1 : b + g = c + f)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3690 (a b c e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3691 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3692 (a b c e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3693 (a b c e f g : Nat)
    (q0 : 3 * a + b + c < 2 * c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a + b + c < 2 * c + e ∧ 2 * a + 3 * b < 2 * c + e ∧ 3 * a + f < 2 * c + e ∧ 2 * a + b + e < 2 * c + e ∧ a + b + 2 * c < 2 * c + e ∧ 3 * b + c < 2 * c + e ∧ a + c + f < 2 * c + e ∧ 2 * b + f < 2 * c + e ∧ b + c + e < 2 * c + e ∧ e + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3694 (a b c e g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3695 (a b c e g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3696 (a b c d e f g : Nat)
    (q0 : a + b + f < c + g)
    (q1 : b + g = c + f)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3697 (a b c e g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3698 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3699 (a b c e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3700 (a b c e f g : Nat)
    (q0 : 2 * a + b + c < 2 * c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a + b + c < 2 * c + e ∧ a + 3 * b < 2 * c + e ∧ 2 * a + f < 2 * c + e ∧ a + b + e < 2 * c + e ∧ b + 2 * c < 2 * c + e ∧ c + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3701 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ b + g)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3702 (a c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + f < c + d)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3703 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3704 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3705 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ b + 2 * c)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3706 (a c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a + d < c + 2 * d)
    (q2 : a + f < c + d)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d ∧ 3 * a + f < c + 2 * d ∧ 2 * a + c + d < c + 2 * d ∧ a + c + f < c + 2 * d ∧ a + d + e < c + 2 * d ∧ 2 * c + d < c + 2 * d ∧ d + g < c + 2 * d ∧ e + f < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3707 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ b + g)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3708 (a c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ d + e)
    (q2 : a + f < c + d)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3709 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : a ≤ b)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3710 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ 2 * b + d)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3711 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ b + 2 * c)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3712 (a c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + d < c + 2 * d)
    (q2 : a + f < c + d)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d ∧ 2 * a + f < c + 2 * d ∧ a + c + d < c + 2 * d ∧ c + f < c + 2 * d ∧ d + e < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3713 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ b + g)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3714 (a c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ c + f)
    (q2 : a + f < c + d)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3715 (a c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + f < c + d)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3716 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * d < a + 2 * c)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : g = 2 * c) :
    2 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3717 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : g = 2 * c) :
    2 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3718 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3719 (a c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ f)
    (q2 : a + f < c + d)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3720 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * a ≤ b + c)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3721 (a c d f g : Nat)
    (q0 : 2 * a + d < c + 2 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : a + f < c + d)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < c + 2 * d ∧ a + f < c + 2 * d ∧ c + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3722 (a c d f g : Nat)
    (q0 : 6 * a ≤ d + g)
    (q1 : c + d < a + f)
    (q2 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3723 (a c d e f g : Nat)
    (q0 : 6 * a ≤ e + f)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3724 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3725 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 6 * a ≤ 2 * b + f)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g)
    (q6 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3726 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 6 * a ≤ b + c + e)
    (q3 : b = 0)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : d + f < c + g)
    (q7 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3727 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 6 * a ≤ b + 2 * d)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3728 (a c d f : Nat)
    (q0 : 6 * a ≤ 2 * c + d)
    (q1 : c + d < a + f) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3729 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 6 * a ≤ 3 * b + c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3730 (a c d e f g : Nat)
    (q0 : 5 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    5 * a < c + f ∧ 3 * a + c < c + f ∧ 2 * a + e < c + f ∧ a + 2 * c < c + f ∧ a + g < c + f ∧ c + e < c + f ∧ 2 * d < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3731 (a c d f g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : c + d < a + f)
    (q2 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3732 (a c d e f g : Nat)
    (q0 : 5 * a ≤ e + f)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3733 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3734 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ 2 * b + f)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g)
    (q6 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3735 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ b + c + e)
    (q3 : b = 0)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : d + f < c + g)
    (q7 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3736 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a ≤ b + 2 * d)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3737 (a c d f : Nat)
    (q0 : 5 * a ≤ 2 * c + d)
    (q1 : c + d < a + f) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3738 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a ≤ 3 * b + c)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3739 (a c d e f g : Nat)
    (q0 : 4 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a < c + f ∧ 2 * a + c < c + f ∧ a + e < c + f ∧ 2 * c < c + f ∧ g < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3740 (a c d f g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : c + d < a + f)
    (q2 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3741 (a c d e f g : Nat)
    (q0 : 4 * a ≤ e + f)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3742 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3743 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a ≤ 2 * b + f)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g)
    (q6 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3744 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ b + c + e)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3745 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3746 (a c d f : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : c + d < a + f) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3747 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 3 * b + c)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3748 (a b c d e f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ b + e)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + f = d + e)
    (q6 : c + g = a + 2 * d)
    (q7 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3749 (a c d f g : Nat)
    (q0 : 4 * a ≤ c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3750 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3751 (a c d e f g : Nat)
    (q0 : 3 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a < c + f ∧ a + c < c + f ∧ e < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3752 (a c d f g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : c + d < a + f)
    (q2 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3753 (a c d e f g : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3754 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3755 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3756 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ b + c + e)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3757 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3758 (a c d f : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : c + d < a + f) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3759 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ 3 * b + c)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3760 (a b c d e f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ b + e)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + f = d + e)
    (q6 : c + g = a + 2 * d)
    (q7 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3761 (a c d f g : Nat)
    (q0 : 3 * a ≤ c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3762 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : a ≤ b)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3763 (a c d f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3764 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3765 (a c d f g : Nat)
    (q0 : 2 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a < c + f ∧ c < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3766 (a c d f g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : c + d < a + f)
    (q2 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3767 (a c d e f g : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3768 (a b c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a ≤ 2 * b + d)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3769 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3770 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3771 (a b c d f g : Nat)
    (q0 : 2 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3772 (a c d f : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : c + d < a + f) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3773 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 3 * b + c)
    (q1 : 2 * d < a + 2 * c)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3774 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ b + e)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3775 (a c d f g : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3776 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * d < a + 2 * c)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3777 (a c d f g : Nat)
    (q0 : 2 * a ≤ f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3778 (a b c d f g : Nat)
    (q0 : 2 * a ≤ b + c)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a > 2 * b)
    (q3 : b = 0)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3779 (a c d f g : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3780 (a b c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : b = 0)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    ¬ (5 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3781 (a c d f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3782 (a c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3783 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3784 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3785 (a c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3786 (a c d e f g : Nat)
    (q0 : 3 * a + d < a + 2 * d)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3787 (a b c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : b = 0)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    ¬ (3 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3788 (a c d f g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3789 (a c d f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3790 (a c d e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3791 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3792 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3793 (a c d f g : Nat)
    (q0 : 2 * a + d < a + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3794 (a b c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : b = 0)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    ¬ (a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3795 (a c d f g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3796 (a c d f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3797 (a c d e f g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3798 (a c d f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3799 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    a + d < a + 2 * d := by
  omega

end Max11DegreeRoutes
