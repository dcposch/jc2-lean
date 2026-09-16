import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3800 (a c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a + d < a + 2 * d)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    a + d < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3801 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3802 (a c d f g : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3803 (a c d e f g : Nat)
    (q0 : 5 * a ≤ d + e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3804 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3805 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3806 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3807 (a c d e f g : Nat)
    (q0 : 4 * a + d < a + d + f)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a + d < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3808 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3809 (a c d f g : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3810 (a c d e f g : Nat)
    (q0 : 4 * a ≤ d + e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3811 (a b c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a ≤ b)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3812 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3813 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3814 (a c d e f g : Nat)
    (q0 : 3 * a + d < a + d + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < a + d + f ∧ 2 * a + f < a + d + f ∧ a + c + d < a + d + f ∧ c + f < a + d + f ∧ d + e < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3815 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3816 (a c d f g : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3817 (a c d e f g : Nat)
    (q0 : 3 * a ≤ d + e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3818 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3819 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3820 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + 2 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3821 (a c d f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3822 (a b c d f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3823 (a c d f g : Nat)
    (q0 : 2 * a + d < a + d + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < a + d + f ∧ a + f < a + d + f ∧ c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3824 (a b c d f g : Nat)
    (q0 : 2 * a ≤ b + g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3825 (a c d f g : Nat)
    (q0 : 2 * a ≤ c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3826 (a c d e f g : Nat)
    (q0 : 2 * a ≤ d + e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3827 (a b c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a ≤ 3 * b)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3828 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3829 (a b c d f g : Nat)
    (q0 : 2 * a ≤ b + 2 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b = 0)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3830 (a c d f g : Nat)
    (q0 : 2 * a ≤ f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3831 (a b c d f g : Nat)
    (q0 : 2 * a ≤ b + c)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b = 0)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3832 (a c d f g : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3833 (a c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a + d < a + d + f)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    a + d < a + d + f ∧ f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3834 (a c d f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d) :
    4 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3835 (a c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    4 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3836 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3837 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    4 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3838 (a c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    4 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3839 (a c d e f g : Nat)
    (q0 : 4 * a + f < a + c + 2 * d)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a + f < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d ∧ f + g < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3840 (a c d f g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d) :
    3 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3841 (a c d f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3842 (a c d e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3843 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3844 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3845 (a c d e f g : Nat)
    (q0 : 3 * a + f < a + c + 2 * d)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + c + f < a + c + 2 * d ∧ a + d + e < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d ∧ e + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3846 (a c d f g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d) :
    2 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3847 (a c d f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3848 (a c d e f g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3849 (a c d f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3850 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3851 (a c d e f g : Nat)
    (q0 : 2 * a + f < a + c + 2 * d)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + f < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ c + f < a + c + 2 * d ∧ d + e < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3852 (a b d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 6 * a ≤ e + f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3853 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 6 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3854 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : e + g < a + d + f)
    (q6 : f < a + d) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3855 (a b d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ e + f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3856 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3857 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : e + g < a + d + f)
    (q6 : f < a + d) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3858 (a b d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ e + f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3859 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3860 (a b d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ b + e)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3861 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : e + g < a + d + f)
    (q6 : f < a + d) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3862 (a b d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ e + f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3863 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3864 (a b d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + e)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3865 (a b d e f g : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3866 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : 2 * d < b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3867 (a b d e f g : Nat)
    (q0 : 2 * a ≤ b + e)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3868 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3869 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b < a + 2 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : e + g < a + d + f)
    (q6 : f < a + d) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3870 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3871 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a + b < a + 2 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : e + g < a + d + f)
    (q6 : f < a + d) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3872 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3873 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3874 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + d < a + b + c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : e + g < a + d + f)
    (q6 : f < a + d) :
    4 * a + d < a + b + c + d ∧ 3 * a + b + c < a + b + c + d ∧ 2 * a + 3 * b < a + b + c + d ∧ 3 * a + f < a + b + c + d ∧ 2 * a + b + e < a + b + c + d ∧ 2 * a + c + d < a + b + c + d ∧ a + 2 * b + d < a + b + c + d ∧ a + b + 2 * c < a + b + c + d ∧ 3 * b + c < a + b + c + d ∧ a + c + f < a + b + c + d ∧ a + d + e < a + b + c + d ∧ 2 * b + f < a + b + c + d ∧ b + c + e < a + b + c + d ∧ b + 2 * d < a + b + c + d ∧ 2 * c + d < a + b + c + d ∧ d + g < a + b + c + d ∧ e + f < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3875 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3876 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a + d < a + b + c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : e + g < a + d + f)
    (q6 : f < a + d) :
    3 * a + d < a + b + c + d ∧ 2 * a + b + c < a + b + c + d ∧ a + 3 * b < a + b + c + d ∧ 2 * a + f < a + b + c + d ∧ a + b + e < a + b + c + d ∧ a + c + d < a + b + c + d ∧ 2 * b + d < a + b + c + d ∧ b + 2 * c < a + b + c + d ∧ c + f < a + b + c + d ∧ d + e < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3877 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3878 (a b c d e f g : Nat)
    (q0 : 2 * a + d < a + b + c + d)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : e + g < a + d + f)
    (q6 : f < a + d) :
    2 * a + d < a + b + c + d ∧ a + b + c < a + b + c + d ∧ 3 * b < a + b + c + d ∧ a + f < a + b + c + d ∧ b + e < a + b + c + d ∧ c + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3879 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3880 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b + c < 2 * a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : e + g < a + d + f)
    (q6 : f < a + d) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3881 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3882 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a + b + c < 2 * a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : e + g < a + d + f)
    (q6 : f < a + d) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3883 (a b c d e f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e + g < a + d + f)
    (q5 : f < a + d) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3884 (a b c d e f g : Nat)
    (q0 : 2 * a + b + c < 2 * a + 4 * b)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : e + g < a + d + f)
    (q6 : f < a + d) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3885 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 6 * a ≤ d + g)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3886 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3887 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 6 * a ≤ b + 2 * d)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3888 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 6 * a ≤ 2 * c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3889 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a < a + 3 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3890 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a ≤ d + g)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3891 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 4 * a ≤ 2 * b + d)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3892 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ b + 2 * d)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3893 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ 2 * c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3894 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a < a + 3 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3895 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ d + g)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3896 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 3 * a ≤ 2 * b + d)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3897 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 4 * a ≤ b + 2 * d)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3898 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 4 * a ≤ 2 * c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3899 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ c + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3900 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ d + g)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3901 (a b d e f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3902 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 3 * a ≤ b + 2 * d)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3903 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 3 * a ≤ 2 * c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3904 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ c + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3905 (a b d e f g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3906 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + d + f < e + g)
    (q4 : a ≤ 2 * b + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3907 (a b d e f g : Nat)
    (q0 : 2 * a ≤ b + 2 * d)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3908 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3909 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3910 (a b d e f g : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3911 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3912 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a ≤ 2 * b + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3913 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a + b < a + 2 * b + c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3914 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 4 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3915 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ 2 * b + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3916 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a + b < a + 2 * b + c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3917 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 3 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3918 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ 2 * b + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3919 (a b c d e f g : Nat)
    (q0 : 2 * a + b < a + 2 * b + c)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3920 (a b c d e f g : Nat)
    (q0 : 2 * f < e + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3921 (a b c d e f g : Nat)
    (q0 : 2 * f < e + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3922 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 9 * a ≤ 4 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3923 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3924 (a b c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3925 (a b c d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3926 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a + b + c < a + 2 * b + e ∧ 4 * a + d < a + 2 * b + e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3927 (a b c d e f g : Nat)
    (q0 : 2 * f < e + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3928 (a b c d e f g : Nat)
    (q0 : 2 * f < e + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3929 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 7 * a ≤ 4 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3930 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 9 * a ≤ 4 * e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3931 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3932 (a b c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3933 (a b c d e f g : Nat)
    (q0 : 2 * a + b + c < a + 2 * b + e ∧ 3 * a + d < a + 2 * b + e)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3934 (a b d e f g : Nat)
    (q0 : a + 2 * f = 2 * g)
    (q1 : a + d + f < e + g)
    (q2 : a ≤ 4 * b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3935 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + d + f < e + g) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3936 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3937 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 7 * a ≤ 4 * e)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3938 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 9 * a ≤ 4 * f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3939 (a b d e f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d + f < e + g) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3940 (a b c d e f g : Nat)
    (q0 : 2 * a + d < a + 2 * b + e)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3941 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3942 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a ≤ 2 * b + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3943 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a + b + c < 2 * a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3944 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 4 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3945 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ 2 * b + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3946 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a + b + c < 2 * a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3947 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 3 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a + d + f < e + g) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3948 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ 2 * b + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3949 (a b c d e f g : Nat)
    (q0 : 2 * a + b + c < 2 * a + 4 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : a + d + f < e + g) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3950 (a b c d e f g : Nat)
    (q0 : 6 * a ≤ e + f)
    (q1 : a + b + f < c + g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + e < b + g)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3951 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : d < a + b) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3952 (a b c d f g : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3953 (a b c d e f g : Nat)
    (q0 : 6 * a ≤ b + c + e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3954 (a b c d f g : Nat)
    (q0 : 6 * a ≤ b + 2 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : d < a + b) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3955 (a b c d f g : Nat)
    (q0 : 6 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3956 (a b c d e f g : Nat)
    (q0 : 5 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + e < b + g)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    5 * a < b + 2 * c ∧ 3 * a + c < b + 2 * c ∧ 2 * a + 2 * b < b + 2 * c ∧ 2 * a + e < b + 2 * c ∧ a + b + d < b + 2 * c ∧ a + 2 * c < b + 2 * c ∧ 2 * b + c < b + 2 * c ∧ a + g < b + 2 * c ∧ b + f < b + 2 * c ∧ c + e < b + 2 * c ∧ 2 * d < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3957 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ e + f)
    (q1 : a + b + f < c + g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + e < b + g)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3958 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : d < a + b) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3959 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3960 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ b + c + e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3961 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : d < a + b) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3962 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3963 (a b c d e f g : Nat)
    (q0 : 4 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + e < b + g)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    4 * a < b + 2 * c ∧ 2 * a + c < b + 2 * c ∧ a + 2 * b < b + 2 * c ∧ a + e < b + 2 * c ∧ b + d < b + 2 * c ∧ 2 * c < b + 2 * c ∧ g < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3964 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ e + f)
    (q1 : a + b + f < c + g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + e < b + g)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3965 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : d < a + b) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3966 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3967 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ b + c + e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3968 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : d < a + b) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3969 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3970 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ b + e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3971 (a b c d f g : Nat)
    (q0 : 4 * a ≤ c + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3972 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3973 (a b c d e f g : Nat)
    (q0 : 3 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + e < b + g)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    3 * a < b + 2 * c ∧ a + c < b + 2 * c ∧ 2 * b < b + 2 * c ∧ e < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3974 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : a + b + f < c + g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + e < b + g)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3975 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : d < a + b) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3976 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3977 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ b + c + e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3978 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : d < a + b) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3979 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3980 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ b + e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3981 (a b c d f g : Nat)
    (q0 : 3 * a ≤ c + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3982 (a b c d f g : Nat)
    (q0 : a + b + f < c + g)
    (q1 : a ≤ b)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3983 (a b c d f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3984 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3985 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3986 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3987 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3988 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3989 (a b c d e f g : Nat)
    (q0 : 4 * a + b < a + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + e < b + g)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3990 (a b c d f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3991 (a b c d e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3992 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3993 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3994 (a b c d e f g : Nat)
    (q0 : 3 * a + b < a + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3995 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3996 (a b c d e f g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3997 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3998 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3999 (a b c d f g : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega

end Max11DegreeRoutes
