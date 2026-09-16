import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0800 (a b c e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : c = 0)
    (q4 : e + g < 2 * a + b + f) :
    ¬ (5 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0801 (a b d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : d = 0)
    (q4 : e + g < 2 * a + b + f) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0802 (a b e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    2 * a + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0803 (a b e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    2 * a + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0804 (a b e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : e + g < 2 * a + b + f) :
    2 * a + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0805 (a b e f g : Nat)
    (q0 : 2 * a + f < a + 2 * b + e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : e + g < 2 * a + b + f) :
    a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0806 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 6 * a ≤ d + g)
    (q2 : d = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0807 (a b e f g : Nat)
    (q0 : 6 * a ≤ e + f)
    (q1 : e + f < a + b + g)
    (q2 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0808 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : d = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0809 (a b c d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 6 * a ≤ 2 * c + d)
    (q3 : c = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0810 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0811 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a ≤ d + g)
    (q2 : d = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0812 (a b e f g : Nat)
    (q0 : 5 * a ≤ e + f)
    (q1 : e + f < a + b + g)
    (q2 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0813 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : d = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0814 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a ≤ b + 2 * d)
    (q2 : d = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0815 (a b c d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 2 * c + d)
    (q3 : c = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0816 (a b c f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a ≤ 3 * b + c)
    (q2 : c = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0817 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ d + g)
    (q2 : d = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0818 (a b e f g : Nat)
    (q0 : 4 * a ≤ e + f)
    (q1 : e + f < a + b + g)
    (q2 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0819 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : d = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0820 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ b + 2 * d)
    (q2 : d = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0821 (a b c d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ 2 * c + d)
    (q2 : 5 * a > 2 * d)
    (q3 : c = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0822 (a b c d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ c + d)
    (q2 : 5 * a > 2 * d)
    (q3 : c = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0823 (a b e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ e + f)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0824 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ b + 2 * d)
    (q2 : d = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0825 (a b c d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ 2 * c + d)
    (q2 : 5 * a > 2 * d)
    (q3 : c = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0826 (a b c d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ c + d)
    (q2 : 5 * a > 2 * d)
    (q3 : c = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0827 (a b e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ e + f)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0828 (a b d f g : Nat)
    (q0 : 2 * a ≤ b + 2 * d)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : d = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0829 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : c = 0)
    (q3 : d = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0830 (a b c d f g : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : c = 0)
    (q3 : d = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0831 (a b d f g : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : d = 0)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0832 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0833 (a b e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : e + f < a + b + g)
    (q4 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0834 (a b e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : a + 2 * f < 2 * g)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0835 (a b e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0836 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b)
    (q3 : e + f < a + b + g)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0837 (a b e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g = a + 2 * b) :
    3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0838 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : e + f < a + b + g)
    (q3 : g = a + 2 * b) :
    3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0839 (a b e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * f < 2 * g)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0840 (a b e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0841 (a b e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g = a + 2 * b) :
    2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0842 (a b e f g : Nat)
    (q0 : 0 < a)
    (q1 : 4 * e < a + 2 * b + 2 * g)
    (q2 : 7 * a ≤ 4 * e)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g = a + 2 * b) :
    2 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0843 (a b e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * a + 4 * b)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : g = a + 2 * b) :
    a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0844 (a b : Nat)
    (q0 : 0 < a)
    (q1 : b = 0) :
    ¬ (5 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0845 (a c d g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : c + g < a + 2 * d) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0846 (a d : Nat)
    (q0 : 5 * a > 2 * d)
    (q1 : 9 * a ≤ 4 * d) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0847 (a d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 5 * a > 2 * d)
    (q2 : a + d = f) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0848 (a d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0849 (a c d f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + d = f)
    (q4 : c + g < a + 2 * d) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0850 (a b : Nat)
    (q0 : 0 < a)
    (q1 : b = 0) :
    ¬ (3 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0851 (a c d g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : c + g < a + 2 * d) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0852 (a d : Nat)
    (q0 : 0 < a)
    (q1 : 7 * a ≤ 4 * d) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0853 (a d f : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * f)
    (q2 : a + d = f) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0854 (a d g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : 3 * a + 2 * d = 2 * g) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0855 (a c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < a + 2 * d)
    (q2 : 3 * a + 2 * d = 2 * g)
    (q3 : a + d = f)
    (q4 : c + g < a + 2 * d) :
    2 * a + d < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0856 (a c d f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + d = f)
    (q4 : c + g < a + 2 * d) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0857 (a d f : Nat)
    (q0 : 5 * a > 2 * d)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + d = f) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0858 (a d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 5 * a > 2 * d)
    (q2 : a + d = f) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0859 (a d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + d = f) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0860 (a c d f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 4 * a + d < a + d + f)
    (q2 : 5 * a > 2 * d)
    (q3 : a + d = f)
    (q4 : c + g < a + 2 * d) :
    4 * a + d < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + c + f < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0861 (a c d f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + d = f)
    (q4 : c + g < a + 2 * d) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0862 (a d f : Nat)
    (q0 : 0 < a)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + d = f) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0863 (a d f : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * f) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0864 (a d f g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : 3 * a + 2 * d = 2 * g)
    (q3 : a + d = f) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0865 (a c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < a + d + f)
    (q3 : a + d = f)
    (q4 : c + g < a + 2 * d) :
    3 * a + d < a + d + f ∧ 2 * a + f < a + d + f ∧ a + c + d < a + d + f ∧ c + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0866 (a b c d e f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : c + f < a + 3 * b)
    (q5 : d < a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0867 (a b c d e f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : c + f < a + 3 * b)
    (q5 : d < a + b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0868 (a b c d e f : Nat)
    (q0 : 3 * a + b < a + 2 * b + c)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : c + f < a + 3 * b)
    (q5 : d < a + b) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0869 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0870 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0871 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0872 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b < a + 2 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0873 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 4 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0874 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a + b < a + 2 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0875 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0876 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0877 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b + c < 2 * a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0878 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 4 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0879 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a + b + c < 2 * a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0880 (a b c d e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0881 (a b c d e f : Nat)
    (q0 : 2 * a + b + c < 2 * a + 4 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0882 (a b c d e g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : d < a + b)
    (q5 : g < a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0883 (a b c d e g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : d < a + b)
    (q5 : g < a + 2 * b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0884 (a b c d e g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : d < a + b)
    (q5 : g < a + 2 * b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0885 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 5 * a < a + 3 * b)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0886 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 4 * a < a + 3 * b)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0887 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 9 * a ≤ 4 * d)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0888 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b)
    (q4 : d + e < b + g)
    (q5 : d < a + b)
    (q6 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0889 (a b c d e : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0890 (a b c d e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b)
    (q4 : 4 * e < a + 2 * b + 2 * g)
    (q5 : d < a + b)
    (q6 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0891 (a b c d e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b + c < 2 * a + 4 * b)
    (q2 : 2 * c < a + 2 * b)
    (q3 : d + e < b + g)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0892 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0893 (a b c d g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0894 (a b c d g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0895 (a b c d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0896 (a b c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0897 (a b c d e g : Nat)
    (q0 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + b + e < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ d + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0898 (a b c d g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0899 (a b c d e g : Nat)
    (q0 : 3 * a + b < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a + b < 3 * c ∧ 2 * a + d < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ b + e < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0900 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0901 (a b c d g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    2 * a + b < 3 * c ∧ a + d < 3 * c ∧ b + c < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0902 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    4 * a + b + c < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0903 (a b c d g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    4 * a + b + c < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0904 (a b c d g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    4 * a + b + c < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0905 (a b c d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c) :
    4 * a + b + c < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0906 (a b c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    4 * a + b + c < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0907 (a b c d e g : Nat)
    (q0 : 4 * a + b + c < 4 * c ∧ 3 * a + c + d < 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 3 * a + 3 * b < 4 * c ∧ 3 * a + b + e < 4 * c ∧ 3 * a + c + d < 4 * c ∧ 2 * a + 2 * b + d < 4 * c ∧ 2 * a + b + 2 * c < 4 * c ∧ a + 3 * b + c < 4 * c ∧ 5 * b < 4 * c ∧ 2 * a + d + e < 4 * c ∧ a + b + c + e < 4 * c ∧ a + b + 2 * d < 4 * c ∧ a + 2 * c + d < 4 * c ∧ 3 * b + e < 4 * c ∧ 2 * b + c + d < 4 * c ∧ b + 3 * c < 4 * c ∧ b + c + g < 4 * c ∧ b + 2 * e < 4 * c ∧ c + d + e < 4 * c ∧ 3 * d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0908 (a b c d g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    3 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0909 (a b c g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c) :
    3 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0910 (a b c d e g : Nat)
    (q0 : 3 * a + b + c < 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a + b + c < 4 * c ∧ 2 * a + 3 * b < 4 * c ∧ 2 * a + b + e < 4 * c ∧ 2 * a + c + d < 4 * c ∧ a + 2 * b + d < 4 * c ∧ a + b + 2 * c < 4 * c ∧ 3 * b + c < 4 * c ∧ a + d + e < 4 * c ∧ b + c + e < 4 * c ∧ b + 2 * d < 4 * c ∧ 2 * c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0911 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c) :
    2 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0912 (a b c g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c) :
    2 * a + b + c < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0913 (a b c d e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b + c < 4 * c)
    (q2 : 2 * e < c + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g)
    (q5 : e < a + c)
    (q6 : g < 2 * a + c)
    (q7 : g = 2 * c) :
    2 * a + b + c < 4 * c ∧ a + 3 * b < 4 * c ∧ a + b + e < 4 * c ∧ a + c + d < 4 * c ∧ 2 * b + d < 4 * c ∧ b + 2 * c < 4 * c ∧ d + e < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0914 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b)
    (q4 : d < a + b)
    (q5 : g < a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0915 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b)
    (q4 : d < a + b)
    (q5 : g < a + 2 * b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0916 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ d + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0917 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0918 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ d + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0919 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0920 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ d + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0921 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0922 (a b c d f g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0923 (a b c f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : c + g < a + b + f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0924 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0925 (a b c f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : c + g < a + b + f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0926 (a b c f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : c + g < a + b + f)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0927 (a b c f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : c + g < a + b + f)
    (q2 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0928 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + b + c < 2 * a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0929 (a b c f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : c + g < a + b + f)
    (q2 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0930 (a b c f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : c + g < a + b + f)
    (q2 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0931 (a b c d f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0932 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0933 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : c + f < b + g)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0934 (a b c d f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * f < 2 * g)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0935 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : a + 2 * f < 2 * g)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0936 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0937 (a b c d f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0938 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0939 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : c + f < b + g)
    (q3 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0940 (a b c d f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * f < 2 * g)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0941 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : a + 2 * f < 2 * g)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0942 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0943 (a b c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b)
    (q4 : a + 2 * f < 2 * g)
    (q5 : d < a + b)
    (q6 : f < 2 * a + b)
    (q7 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0944 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a ≤ 4 * b)
    (q3 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0945 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : c + f < b + g)
    (q3 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0946 (a b c d f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + 2 * f < 2 * g)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0947 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * f < 2 * g)
    (q3 : f < 2 * a + b)
    (q4 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0948 (a b c f g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : 2 * c < a + 2 * b)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0949 (a b c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b)
    (q2 : 2 * c < a + 2 * b)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + f < b + g)
    (q5 : d < a + b)
    (q6 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0950 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0951 (a b c d f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0952 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0953 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0954 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0955 (a b c d f g : Nat)
    (q0 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0956 (a b c d f g : Nat)
    (q0 : 3 * a + b < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a + b < 3 * c ∧ 2 * a + d < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0957 (a b c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + b + f < c + g)
    (q5 : g < 2 * a + c)
    (q6 : g = 2 * c) :
    2 * a + b < 3 * c ∧ a + d < 3 * c ∧ b + c < 3 * c ∧ f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0958 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0959 (a b c d f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0960 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0961 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0962 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0963 (a b c d f g : Nat)
    (q0 : 4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + b + f < c + g)
    (q5 : g < 2 * a + c)
    (q6 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 3 * a + 3 * b < 4 * c ∧ 4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c ∧ 2 * a + 2 * b + d < 4 * c ∧ 2 * a + b + 2 * c < 4 * c ∧ a + 3 * b + c < 4 * c ∧ 5 * b < 4 * c ∧ 2 * a + c + f < 4 * c ∧ a + 2 * b + f < 4 * c ∧ a + b + 2 * d < 4 * c ∧ a + 2 * c + d < 4 * c ∧ 2 * b + c + d < 4 * c ∧ b + 3 * c < 4 * c ∧ b + c + g < 4 * c ∧ b + d + f < 4 * c ∧ 2 * c + f < 4 * c ∧ 3 * d < 4 * c ∧ f + g < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0964 (a b c d f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a + b + c < 4 * c ∧ 3 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0965 (a b c d f g : Nat)
    (q0 : 3 * a + b + c < 4 * c ∧ 3 * a + f < 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a + b + c < 4 * c ∧ 2 * a + 3 * b < 4 * c ∧ 3 * a + f < 4 * c ∧ 2 * a + c + d < 4 * c ∧ a + 2 * b + d < 4 * c ∧ a + b + 2 * c < 4 * c ∧ 3 * b + c < 4 * c ∧ a + c + f < 4 * c ∧ 2 * b + f < 4 * c ∧ b + 2 * d < 4 * c ∧ 2 * c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0966 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    2 * a + b + c < 4 * c ∧ 2 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0967 (a b c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b + c < 4 * c ∧ 2 * a + f < 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + b + f < c + g)
    (q5 : g < 2 * a + c)
    (q6 : g = 2 * c) :
    2 * a + b + c < 4 * c ∧ a + 3 * b < 4 * c ∧ 2 * a + f < 4 * c ∧ a + c + d < 4 * c ∧ 2 * b + d < 4 * c ∧ b + 2 * c < 4 * c ∧ c + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0968 (a b c e f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : c + f < a + 3 * b)
    (q5 : g < a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0969 (a b c e f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : c + f < a + 3 * b)
    (q5 : g < a + 2 * b) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0970 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 6 * a ≤ d + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + g < a + b + f)
    (q5 : d = 0)
    (q6 : f < 2 * a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0971 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + g < a + b + f)
    (q5 : f < 2 * a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0972 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ d + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + g < a + b + f)
    (q5 : d = 0)
    (q6 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0973 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0974 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + g < a + b + f)
    (q5 : f < 2 * a + b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0975 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ d + g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + g < a + b + f)
    (q5 : d = 0)
    (q6 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0976 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0977 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0978 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0979 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0980 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0981 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0982 (a b c d f g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0983 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a ≤ 2 * b + d)
    (q2 : d = 0)
    (q3 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0984 (a b c d f g : Nat)
    (q0 : 2 * a ≤ b + 2 * d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0985 (a b c d f : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d = 0)
    (q4 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0986 (a b c d f g : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0987 (a b c d f g : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0988 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b < a + 2 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + g < a + b + f)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0989 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0990 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b + c < 2 * a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + g < a + b + f)
    (q5 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0991 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0992 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 5 * a < a + 3 * b)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0993 (a b c d f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ c + d)
    (q3 : d = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0994 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 5 * a ≤ 4 * b)
    (q4 : a + 2 * f < 2 * g)
    (q5 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0995 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 7 * a ≤ 4 * c)
    (q4 : c + f < b + g)
    (q5 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0996 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : 2 * g < 5 * a + 2 * b)
    (q4 : e + f < a + b + g)
    (q5 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0997 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : 2 * g < 5 * a + 2 * b)
    (q4 : a + 2 * f < 2 * g)
    (q5 : f < 2 * a + b)
    (q6 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0998 (a b c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : 2 * g < 5 * a + 2 * b)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0999 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b)
    (q4 : e + f < a + b + g)
    (q5 : f < 2 * a + b)
    (q6 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega

end Max11DegreeRoutes
