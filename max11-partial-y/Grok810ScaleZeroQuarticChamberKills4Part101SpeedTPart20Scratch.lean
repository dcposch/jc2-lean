import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4000 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4001 (a b c d f g : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : a + b + f < c + g)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4002 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ d + e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4003 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4004 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4005 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + 2 * c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4006 (a b c d e f g : Nat)
    (q0 : 4 * a + d < a + b + c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + e < b + g)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    4 * a + d < a + b + c + d ∧ 3 * a + b + c < a + b + c + d ∧ 2 * a + 3 * b < a + b + c + d ∧ 3 * a + f < a + b + c + d ∧ 2 * a + b + e < a + b + c + d ∧ 2 * a + c + d < a + b + c + d ∧ a + 2 * b + d < a + b + c + d ∧ a + b + 2 * c < a + b + c + d ∧ 3 * b + c < a + b + c + d ∧ a + c + f < a + b + c + d ∧ a + d + e < a + b + c + d ∧ 2 * b + f < a + b + c + d ∧ b + c + e < a + b + c + d ∧ b + 2 * d < a + b + c + d ∧ 2 * c + d < a + b + c + d ∧ d + g < a + b + c + d ∧ e + f < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4007 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4008 (a b c d f g : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : a + b + f < c + g)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4009 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ d + e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4010 (a b c d f g : Nat)
    (q0 : a + b + f < c + g)
    (q1 : a ≤ b)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4011 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4012 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + 2 * c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4013 (a b c d e f g : Nat)
    (q0 : 3 * a + d < a + b + c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + e < b + g)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    3 * a + d < a + b + c + d ∧ 2 * a + b + c < a + b + c + d ∧ a + 3 * b < a + b + c + d ∧ 2 * a + f < a + b + c + d ∧ a + b + e < a + b + c + d ∧ a + c + d < a + b + c + d ∧ 2 * b + d < a + b + c + d ∧ b + 2 * c < a + b + c + d ∧ c + f < a + b + c + d ∧ d + e < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4014 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4015 (a b c d f g : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : a + b + f < c + g)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4016 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ d + e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4017 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4018 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4019 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + 2 * c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4020 (a b c d f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4021 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4022 (a b c d e f g : Nat)
    (q0 : 2 * a + d < a + b + c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + e < b + g)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    2 * a + d < a + b + c + d ∧ a + b + c < a + b + c + d ∧ 3 * b < a + b + c + d ∧ a + f < a + b + c + d ∧ b + e < a + b + c + d ∧ c + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4023 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4024 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4025 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4026 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4027 (a b c d e f g : Nat)
    (q0 : 4 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + e < b + g)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d ∧ 3 * a + b + e < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * b + f < a + c + 2 * d ∧ a + b + c + e < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 3 * b + e < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ b + c + g < a + c + 2 * d ∧ b + d + f < a + c + 2 * d ∧ b + 2 * e < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d ∧ f + g < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4028 (a b c d f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4029 (a b c d e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4030 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4031 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4032 (a b c d e f g : Nat)
    (q0 : 3 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + e < b + g)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d ∧ 2 * a + 3 * b < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d ∧ 2 * a + b + e < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + 2 * b + d < a + c + 2 * d ∧ a + b + 2 * c < a + c + 2 * d ∧ 3 * b + c < a + c + 2 * d ∧ a + c + f < a + c + 2 * d ∧ a + d + e < a + c + 2 * d ∧ 2 * b + f < a + c + 2 * d ∧ b + c + e < a + c + 2 * d ∧ b + 2 * d < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d ∧ e + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4033 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4034 (a b c d e f g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + e < b + g)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4035 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4036 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4037 (a b c d e f g : Nat)
    (q0 : 2 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + e < b + g)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d ∧ a + 3 * b < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d ∧ a + b + e < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ 2 * b + d < a + c + 2 * d ∧ b + 2 * c < a + c + 2 * d ∧ c + f < a + c + 2 * d ∧ d + e < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4038 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + b < d)
    (q3 : c + g = a + 2 * d) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4039 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ c + f)
    (q2 : a + b < d)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4040 (a b c d e g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + b < d)
    (q3 : b + g = d + e)
    (q4 : c + g = a + 2 * d) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4041 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + b < d)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4042 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + b < d)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4043 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + b < d)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4044 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a + d < c + 2 * d)
    (q2 : a + b < d)
    (q3 : b + g = c + f)
    (q4 : b + g = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a + d < c + 2 * d ∧ 3 * a + b + c < c + 2 * d ∧ 2 * a + 3 * b < c + 2 * d ∧ 3 * a + f < c + 2 * d ∧ 2 * a + b + e < c + 2 * d ∧ 2 * a + c + d < c + 2 * d ∧ a + 2 * b + d < c + 2 * d ∧ a + b + 2 * c < c + 2 * d ∧ 3 * b + c < c + 2 * d ∧ a + c + f < c + 2 * d ∧ a + d + e < c + 2 * d ∧ 2 * b + f < c + 2 * d ∧ b + c + e < c + 2 * d ∧ b + 2 * d < c + 2 * d ∧ 2 * c + d < c + 2 * d ∧ d + g < c + 2 * d ∧ e + f < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4045 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + b < d)
    (q3 : c + g = a + 2 * d) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4046 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + b < d)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4047 (a b c d e g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ d + e)
    (q2 : a + b < d)
    (q3 : b + g = d + e)
    (q4 : c + g = a + 2 * d) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4048 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : a + b < d)
    (q2 : a ≤ b)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4049 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + b < d)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4050 (a b c d g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + b < d)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4051 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + d < c + 2 * d)
    (q2 : a + b < d)
    (q3 : b + g = c + f)
    (q4 : b + g = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    3 * a + d < c + 2 * d ∧ 2 * a + b + c < c + 2 * d ∧ a + 3 * b < c + 2 * d ∧ 2 * a + f < c + 2 * d ∧ a + b + e < c + 2 * d ∧ a + c + d < c + 2 * d ∧ 2 * b + d < c + 2 * d ∧ b + 2 * c < c + 2 * d ∧ c + f < c + 2 * d ∧ d + e < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4052 (a b c d e f g : Nat)
    (q0 : 6 * a ≤ e + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + f < b + g)
    (q4 : c + g = a + 2 * d)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4053 (a b c d f g : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4054 (a b c d e f g : Nat)
    (q0 : 5 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : b + g = d + e)
    (q4 : c + f < b + g)
    (q5 : c + g = a + 2 * d)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    5 * a < b + 2 * c ∧ 3 * a + c < b + 2 * c ∧ 2 * a + 2 * b < b + 2 * c ∧ 2 * a + e < b + 2 * c ∧ a + b + d < b + 2 * c ∧ a + 2 * c < b + 2 * c ∧ 2 * b + c < b + 2 * c ∧ a + g < b + 2 * c ∧ b + f < b + 2 * c ∧ c + e < b + 2 * c ∧ 2 * d < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4055 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ e + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + f < b + g)
    (q4 : c + g = a + 2 * d)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4056 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4057 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ e + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + f < b + g)
    (q4 : c + g = a + 2 * d)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4058 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4059 (a b c d e g : Nat)
    (q0 : 3 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c ∧ a + c < b + 2 * c ∧ 2 * b < b + 2 * c ∧ e < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4060 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + f < b + g)
    (q4 : c + g = a + 2 * d)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4061 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4062 (a b c d f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4063 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4064 (a b c d e f g : Nat)
    (q0 : 4 * a + b < a + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + f < b + g)
    (q4 : c + g = a + 2 * d)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4065 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4066 (a b c d e f g : Nat)
    (q0 : 3 * a + b < a + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + f < b + g)
    (q4 : c + g = a + 2 * d)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4067 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4068 (a b c d f g : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4069 (a b c d f g : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4070 (a b c d e f g : Nat)
    (q0 : 4 * a + d < a + b + c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : b + g = d + e)
    (q4 : c + f < b + g)
    (q5 : c + g = a + 2 * d)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    4 * a + d < a + b + c + d ∧ 3 * a + b + c < a + b + c + d ∧ 2 * a + 3 * b < a + b + c + d ∧ 3 * a + f < a + b + c + d ∧ 2 * a + b + e < a + b + c + d ∧ 2 * a + c + d < a + b + c + d ∧ a + 2 * b + d < a + b + c + d ∧ a + b + 2 * c < a + b + c + d ∧ 3 * b + c < a + b + c + d ∧ a + c + f < a + b + c + d ∧ a + d + e < a + b + c + d ∧ 2 * b + f < a + b + c + d ∧ b + c + e < a + b + c + d ∧ b + 2 * d < a + b + c + d ∧ 2 * c + d < a + b + c + d ∧ d + g < a + b + c + d ∧ e + f < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4071 (a b c d f g : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4072 (a b c d e f g : Nat)
    (q0 : 3 * a + d < a + b + c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : b + g = d + e)
    (q4 : c + f < b + g)
    (q5 : c + g = a + 2 * d)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    3 * a + d < a + b + c + d ∧ 2 * a + b + c < a + b + c + d ∧ a + 3 * b < a + b + c + d ∧ 2 * a + f < a + b + c + d ∧ a + b + e < a + b + c + d ∧ a + c + d < a + b + c + d ∧ 2 * b + d < a + b + c + d ∧ b + 2 * c < a + b + c + d ∧ c + f < a + b + c + d ∧ d + e < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4073 (a b c d f g : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4074 (a b c d f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4075 (a b c d e f g : Nat)
    (q0 : 2 * a + d < a + b + c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + f < b + g)
    (q4 : c + g = a + 2 * d)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    2 * a + d < a + b + c + d ∧ a + b + c < a + b + c + d ∧ 3 * b < a + b + c + d ∧ a + f < a + b + c + d ∧ b + e < a + b + c + d ∧ c + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4076 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4077 (a b c d e f g : Nat)
    (q0 : 4 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : b + g = d + e)
    (q4 : c + f < b + g)
    (q5 : c + g = a + 2 * d)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d ∧ 3 * a + b + e < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * b + f < a + c + 2 * d ∧ a + b + c + e < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 3 * b + e < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ b + c + g < a + c + 2 * d ∧ b + d + f < a + c + 2 * d ∧ b + 2 * e < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d ∧ f + g < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4078 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4079 (a b c d e f g : Nat)
    (q0 : 3 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : b + g = d + e)
    (q4 : c + f < b + g)
    (q5 : c + g = a + 2 * d)
    (q6 : d < a + b)
    (q7 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d ∧ 2 * a + 3 * b < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d ∧ 2 * a + b + e < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + 2 * b + d < a + c + 2 * d ∧ a + b + 2 * c < a + c + 2 * d ∧ 3 * b + c < a + c + 2 * d ∧ a + c + f < a + c + 2 * d ∧ a + d + e < a + c + 2 * d ∧ 2 * b + f < a + c + 2 * d ∧ b + c + e < a + c + 2 * d ∧ b + 2 * d < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d ∧ e + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4080 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + f < b + g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4081 (a b c d e f g : Nat)
    (q0 : 2 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + f < b + g)
    (q4 : c + g = a + 2 * d)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d ∧ a + 3 * b < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d ∧ a + b + e < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ 2 * b + d < a + c + 2 * d ∧ b + 2 * c < a + c + 2 * d ∧ c + f < a + c + 2 * d ∧ d + e < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4082 (a c d f g : Nat)
    (q0 : 6 * a ≤ d + g)
    (q1 : d + g < a + c + f) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4083 (a c d e f g : Nat)
    (q0 : 6 * a ≤ e + f)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4084 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4085 (a b c d f g : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4086 (a b c d e f g : Nat)
    (q0 : 6 * a ≤ b + c + e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4087 (a b c d f g : Nat)
    (q0 : 6 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4088 (a c d f g : Nat)
    (q0 : 6 * a ≤ 2 * c + d)
    (q1 : d + g < a + c + f)
    (q2 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4089 (a b c d f g : Nat)
    (q0 : 6 * a ≤ 3 * b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4090 (a b c d e f g : Nat)
    (q0 : 5 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    5 * a < c + f ∧ 3 * a + c < c + f ∧ 2 * a + 2 * b < c + f ∧ 2 * a + e < c + f ∧ a + b + d < c + f ∧ a + 2 * c < c + f ∧ 2 * b + c < c + f ∧ a + g < c + f ∧ b + f < c + f ∧ c + e < c + f ∧ 2 * d < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4091 (a c d f g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : d + g < a + c + f) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4092 (a c d e f g : Nat)
    (q0 : 5 * a ≤ e + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + f = d + e)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4093 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4094 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4095 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ b + c + e)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4096 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4097 (a c d f g : Nat)
    (q0 : 5 * a ≤ 2 * c + d)
    (q1 : d + g < a + c + f)
    (q2 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4098 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 3 * b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4099 (a b c d e f g : Nat)
    (q0 : 4 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    4 * a < c + f ∧ 2 * a + c < c + f ∧ a + 2 * b < c + f ∧ a + e < c + f ∧ b + d < c + f ∧ 2 * c < c + f ∧ g < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4100 (a c d f g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : d + g < a + c + f) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4101 (a c d e f g : Nat)
    (q0 : 4 * a ≤ e + f)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4102 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4103 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4104 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ b + c + e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4105 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4106 (a c d f g : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : d + g < a + c + f)
    (q2 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4107 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 3 * b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4108 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ b + e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4109 (a c d f g : Nat)
    (q0 : 4 * a ≤ c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4110 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4111 (a b c d e f g : Nat)
    (q0 : 3 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    3 * a < c + f ∧ a + c < c + f ∧ 2 * b < c + f ∧ e < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4112 (a b c d f g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : b + g < c + f)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4113 (a c d e f g : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4114 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4115 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4116 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ b + c + e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4117 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4118 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : b + g < c + f)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4119 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 3 * b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4120 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ b + e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4121 (a c d f g : Nat)
    (q0 : 3 * a ≤ c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4122 (a b c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a ≤ b)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4123 (a c d f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4124 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4125 (a b c d f g : Nat)
    (q0 : 2 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a < c + f ∧ c < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4126 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4127 (a b c d f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4128 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4129 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4130 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4131 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4132 (a b c d e f g : Nat)
    (q0 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : d + g < a + c + f)
    (q7 : g = 2 * c) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4133 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4134 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4135 (a b c d f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4136 (a b c d e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4137 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4138 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4139 (a b c d e f g : Nat)
    (q0 : 3 * a + b < a + 2 * d)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4140 (a b c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a ≤ 4 * b)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4141 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4142 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4143 (a b c d e f g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4144 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4145 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4146 (a b c d f g : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4147 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4148 (a c d f g : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4149 (a c d e f g : Nat)
    (q0 : 5 * a ≤ d + e)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + f = d + e)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4150 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4151 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4152 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + 2 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4153 (a b c d e f g : Nat)
    (q0 : 4 * a + d < a + d + f)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : d + g < a + c + f)
    (q7 : g = 2 * c) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + c + e < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4154 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4155 (a c d f g : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4156 (a c d e f g : Nat)
    (q0 : 4 * a ≤ d + e)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + f = d + e)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4157 (a b c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a ≤ b)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4158 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4159 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + 2 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4160 (a b c d e f g : Nat)
    (q0 : 3 * a + d < a + d + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    3 * a + d < a + d + f ∧ 2 * a + b + c < a + d + f ∧ a + 3 * b < a + d + f ∧ 2 * a + f < a + d + f ∧ a + b + e < a + d + f ∧ a + c + d < a + d + f ∧ 2 * b + d < a + d + f ∧ b + 2 * c < a + d + f ∧ c + f < a + d + f ∧ d + e < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4161 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4162 (a c d f g : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4163 (a c d e f g : Nat)
    (q0 : 3 * a ≤ d + e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4164 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4165 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4166 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + 2 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4167 (a c d f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f)
    (q4 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4168 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f)
    (q5 : g = 2 * c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4169 (a b c d e f g : Nat)
    (q0 : 2 * a + d < a + d + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    2 * a + d < a + d + f ∧ a + b + c < a + d + f ∧ 3 * b < a + d + f ∧ a + f < a + d + f ∧ b + e < a + d + f ∧ c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4170 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d) :
    4 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4171 (a c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f) :
    4 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4172 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f) :
    4 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4173 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f) :
    4 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4174 (a c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f) :
    4 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4175 (a b c d e f g : Nat)
    (q0 : 4 * a + f < a + c + 2 * d)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : d + g < a + c + f)
    (q7 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d ∧ 3 * a + b + e < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + 2 * b + f < a + c + 2 * d ∧ a + b + c + e < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 3 * b + e < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ a + e + f < a + c + 2 * d ∧ b + c + g < a + c + 2 * d ∧ b + d + f < a + c + 2 * d ∧ b + 2 * e < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d ∧ f + g < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4176 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d) :
    3 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4177 (a c d f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f) :
    3 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4178 (a c d e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f) :
    3 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4179 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f) :
    3 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4180 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f) :
    3 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4181 (a b c d e f g : Nat)
    (q0 : 3 * a + f < a + c + 2 * d)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : d + g < a + c + f)
    (q7 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d ∧ 2 * a + 3 * b < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d ∧ 2 * a + b + e < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + 2 * b + d < a + c + 2 * d ∧ a + b + 2 * c < a + c + 2 * d ∧ 3 * b + c < a + c + 2 * d ∧ a + c + f < a + c + 2 * d ∧ a + d + e < a + c + 2 * d ∧ 2 * b + f < a + c + 2 * d ∧ b + c + e < a + c + 2 * d ∧ b + 2 * d < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d ∧ e + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4182 (a b c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a ≤ 4 * b)
    (q2 : b + g < c + f)
    (q3 : c + g = a + 2 * d) :
    2 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4183 (a c d f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f) :
    2 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4184 (a c d e f g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d + g < a + c + f) :
    2 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4185 (a c d f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f) :
    2 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4186 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = a + 2 * d)
    (q3 : d + g < a + c + f) :
    2 * a + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4187 (a b c d e f g : Nat)
    (q0 : 2 * a + f < a + c + 2 * d)
    (q1 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + g < a + c + f)
    (q6 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d ∧ a + 3 * b < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d ∧ a + b + e < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ 2 * b + d < a + c + 2 * d ∧ b + 2 * c < a + c + 2 * d ∧ c + f < a + c + 2 * d ∧ d + e < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4188 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + c + f < d + g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4189 (a c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ c + f)
    (q2 : a + c + f < d + g)
    (q3 : c + g = a + 2 * d) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4190 (a c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + c + f < d + g)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4191 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + c + f < d + g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4192 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + c + f < d + g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4193 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + c + f < d + g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4194 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a + d < c + 2 * d)
    (q2 : a + c + f < d + g)
    (q3 : b + g < c + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a + d < c + 2 * d ∧ 3 * a + b + c < c + 2 * d ∧ 2 * a + 3 * b < c + 2 * d ∧ 3 * a + f < c + 2 * d ∧ 2 * a + b + e < c + 2 * d ∧ 2 * a + c + d < c + 2 * d ∧ a + 2 * b + d < c + 2 * d ∧ a + b + 2 * c < c + 2 * d ∧ 3 * b + c < c + 2 * d ∧ a + c + f < c + 2 * d ∧ a + d + e < c + 2 * d ∧ 2 * b + f < c + 2 * d ∧ b + c + e < c + 2 * d ∧ b + 2 * d < c + 2 * d ∧ 2 * c + d < c + 2 * d ∧ d + g < c + 2 * d ∧ e + f < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4195 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + c + f < d + g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4196 (a c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + c + f < d + g)
    (q3 : c + g = a + 2 * d) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4197 (a c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ d + e)
    (q2 : a + c + f < d + g)
    (q3 : c + f = d + e)
    (q4 : c + g = a + 2 * d) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4198 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : a + c + f < d + g)
    (q2 : a ≤ b)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4199 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + c + f < d + g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega

end Max11DegreeRoutes
