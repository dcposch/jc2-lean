import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4800 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4801 (a b c e f g : Nat)
    (q0 : 4 * a ≤ b + c + e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4802 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 2 * c + d)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4803 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4804 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ c + d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0)
    (q7 : e + g < 2 * a + b + f) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4805 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4806 (a b c e f g : Nat)
    (q0 : 3 * a ≤ b + c + e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4807 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4808 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4809 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4810 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4811 (a b c e f g : Nat)
    (q0 : 2 * a < a + 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4812 (a b c e f g : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4813 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4814 (a b c e f g : Nat)
    (q0 : 2 * a ≤ 3 * b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4815 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4816 (a b c e f g : Nat)
    (q0 : 2 * a ≤ b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4817 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 7 * a ≤ f + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4818 (a b c e f g : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4819 (a b c e f g : Nat)
    (q0 : 7 * a ≤ b + c + g)
    (q1 : a + b + f = 2 * e)
    (q2 : e + g < 2 * a + b + f) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4820 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 6 * a ≤ b + 2 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4821 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 7 * a ≤ b + d + f)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4822 (a b c e f g : Nat)
    (q0 : 7 * a ≤ b + 2 * e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4823 (a b c e f g : Nat)
    (q0 : 7 * a ≤ 2 * c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4824 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 7 * a ≤ c + d + e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4825 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 7 * a ≤ 3 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4826 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ 3 * b + c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4827 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 7 * a ≤ 3 * b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4828 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 7 * a ≤ 2 * b + c + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4829 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 7 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4830 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 7 * a ≤ 5 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    6 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4831 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a < b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    6 * a < b + c + e ∧ 4 * a + c < b + c + e ∧ 3 * a + 2 * b < b + c + e ∧ 3 * a + e < b + c + e ∧ 2 * a + 2 * c < b + c + e ∧ a + 2 * b + c < b + c + e ∧ 4 * b < b + c + e ∧ 2 * a + g < b + c + e ∧ a + b + f < b + c + e ∧ a + c + e < b + c + e ∧ 2 * b + e < b + c + e ∧ 3 * c < b + c + e ∧ c + g < b + c + e ∧ 2 * e < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4832 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ f + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4833 (a b c e f g : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4834 (a b c e f g : Nat)
    (q0 : 6 * a ≤ b + c + g)
    (q1 : a + b + f = 2 * e)
    (q2 : e + g < 2 * a + b + f) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4835 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ b + 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4836 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 6 * a ≤ b + d + f)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4837 (a b c e f g : Nat)
    (q0 : 6 * a ≤ b + 2 * e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4838 (a b c e f g : Nat)
    (q0 : 6 * a ≤ 2 * c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4839 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 6 * a ≤ c + d + e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4840 (a b c d e f : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4841 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 3 * b + c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4842 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ 3 * b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4843 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 6 * a ≤ 2 * b + c + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4844 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4845 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ 5 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    5 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4846 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a < b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    5 * a < b + c + e ∧ 3 * a + c < b + c + e ∧ 2 * a + 2 * b < b + c + e ∧ 2 * a + e < b + c + e ∧ a + 2 * c < b + c + e ∧ 2 * b + c < b + c + e ∧ a + g < b + c + e ∧ b + f < b + c + e ∧ c + e < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4847 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ f + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4848 (a b c e f g : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4849 (a b c e f g : Nat)
    (q0 : 5 * a ≤ b + c + g)
    (q1 : a + b + f = 2 * e)
    (q2 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4850 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ b + 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4851 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ b + d + f)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4852 (a b c e f g : Nat)
    (q0 : 5 * a ≤ b + 2 * e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4853 (a b c e f g : Nat)
    (q0 : 5 * a ≤ 2 * c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4854 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ c + d + e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4855 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ 3 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4856 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b + c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4857 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 3 * b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4858 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ 2 * b + c + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4859 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4860 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : a ≤ b)
    (q5 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4861 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4862 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0)
    (q7 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4863 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4864 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0)
    (q7 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4865 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4866 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a < b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    4 * a < b + c + e ∧ 2 * a + c < b + c + e ∧ a + 2 * b < b + c + e ∧ a + e < b + c + e ∧ 2 * c < b + c + e ∧ g < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4867 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ f + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4868 (a b c e f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4869 (a b c e f g : Nat)
    (q0 : 4 * a ≤ b + c + g)
    (q1 : a + b + f = 2 * e)
    (q2 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4870 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4871 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + d + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4872 (a b c e f g : Nat)
    (q0 : 4 * a ≤ b + 2 * e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4873 (a b c e f g : Nat)
    (q0 : 4 * a ≤ 2 * c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4874 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ c + d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4875 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 3 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4876 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 3 * b + c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4877 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4878 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4879 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4880 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 5 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4881 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4882 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ d + e)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4883 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : a ≤ b)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4884 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0)
    (q7 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4885 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4886 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4887 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ c + d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0)
    (q7 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4888 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4889 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a < b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    3 * a < b + c + e ∧ a + c < b + c + e ∧ 2 * b < b + c + e ∧ e < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4890 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4891 (a b c e f g : Nat)
    (q0 : 2 * a ≤ 2 * b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4892 (a b c e f g : Nat)
    (q0 : 3 * a ≤ b + c + g)
    (q1 : a + b + f = 2 * e)
    (q2 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4893 (a b c d e f : Nat)
    (q0 : 2 * a ≤ b + 2 * d)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4894 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + d + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4895 (a b c e f g : Nat)
    (q0 : 3 * a ≤ b + 2 * e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4896 (a b c e f g : Nat)
    (q0 : 3 * a ≤ 2 * c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4897 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ c + d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4898 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : a ≤ d)
    (q5 : d = 0) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4899 (a b c e f g : Nat)
    (q0 : 2 * a ≤ 3 * b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4900 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 3 * b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4901 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4902 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4903 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 5 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4904 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4905 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4906 (a b c e f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4907 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + b + f = 2 * e)
    (q6 : d = 0)
    (q7 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4908 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4909 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4910 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b + f = 2 * e)
    (q5 : d = 0) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4911 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : a ≤ b)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4912 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4913 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < b + c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4914 (a b c e f g : Nat)
    (q0 : 2 * a < b + c + e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + b + f = 2 * e)
    (q5 : e + g < 2 * a + b + f) :
    2 * a < b + c + e ∧ c < b + c + e := by
  omega

end Max11DegreeRoutes
