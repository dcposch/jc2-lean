import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1000 (a b c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a ≤ 4 * b)
    (q3 : 4 * e < a + 2 * b + 2 * g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1001 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : c + f < b + g)
    (q4 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1002 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : e + f < a + b + g)
    (q4 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1003 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : a + 2 * f < 2 * g)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1004 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : 2 * g < 5 * a + 2 * b)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1005 (a b c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 3 * a + b + c < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b)
    (q4 : 4 * e < a + 2 * b + 2 * g)
    (q5 : a + 2 * f < 2 * g)
    (q6 : c + f < b + g)
    (q7 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1006 (a b c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : 7 * a ≤ 4 * e)
    (q4 : a + 2 * f < 2 * g)
    (q5 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1007 (a b c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b + c < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b)
    (q2 : 2 * c < a + 2 * b)
    (q3 : 4 * e < a + 2 * b + 2 * g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : c + f < b + g)
    (q6 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1008 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1009 (a b c e f g : Nat)
    (q0 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1010 (a b c e f g : Nat)
    (q0 : 3 * a + b < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ b + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1011 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1012 (a b c e f g : Nat)
    (q0 : 4 * a + b + c < 4 * c ∧ 4 * a + f < 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a + b + c < 4 * c ∧ 3 * a + 3 * b < 4 * c ∧ 4 * a + f < 4 * c ∧ 3 * a + b + e < 4 * c ∧ 2 * a + b + 2 * c < 4 * c ∧ a + 3 * b + c < 4 * c ∧ 5 * b < 4 * c ∧ 2 * a + c + f < 4 * c ∧ a + 2 * b + f < 4 * c ∧ a + b + c + e < 4 * c ∧ 3 * b + e < 4 * c ∧ b + 3 * c < 4 * c ∧ a + e + f < 4 * c ∧ b + c + g < 4 * c ∧ b + 2 * e < 4 * c ∧ 2 * c + f < 4 * c ∧ f + g < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1013 (a b c e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a + b + c < 4 * c ∧ 3 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1014 (a b c e f g : Nat)
    (q0 : 3 * a + b + c < 4 * c ∧ 3 * a + f < 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a + b + c < 4 * c ∧ 2 * a + 3 * b < 4 * c ∧ 3 * a + f < 4 * c ∧ 2 * a + b + e < 4 * c ∧ a + b + 2 * c < 4 * c ∧ 3 * b + c < 4 * c ∧ a + c + f < 4 * c ∧ 2 * b + f < 4 * c ∧ b + c + e < 4 * c ∧ e + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1015 (a b c e f g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * f < 2 * g)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a + b + c < 4 * c ∧ 2 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1016 (a b c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b + c < 4 * c ∧ 2 * a + f < 4 * c)
    (q2 : 2 * e < c + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + b + f < c + g)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a + b + c < 4 * c ∧ a + 3 * b < 4 * c ∧ 2 * a + f < 4 * c ∧ a + b + e < 4 * c ∧ b + 2 * c < 4 * c ∧ c + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1017 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1018 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * f < 2 * g)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1019 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b)
    (q3 : d + e < b + g)
    (q4 : d < a + b)
    (q5 : e + f < a + b + g)
    (q6 : f < 2 * a + b)
    (q7 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1020 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * f < 2 * g)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1021 (a b d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1022 (a b d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * a + 4 * b)
    (q2 : d + e < b + g)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1023 (a c d f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1024 (a c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1025 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1026 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1027 (a c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1028 (a c d e f g : Nat)
    (q0 : 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q1 : e < a + c)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ c + f < 3 * c ∧ d + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1029 (a c d g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * d < c + g)
    (q2 : g < 2 * a + c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1030 (a c d g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : g < 2 * a + c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1031 (a c d e g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * d < c + g)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1032 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1033 (a c d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * d < c + g)
    (q2 : g < 2 * a + c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1034 (a c d f g : Nat)
    (q0 : 2 * a + d < 3 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    2 * a + d < 3 * c ∧ a + f < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1035 (a c d f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1036 (a c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1037 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1038 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1039 (a c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1040 (a c d e f g : Nat)
    (q0 : 4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c)
    (q1 : a + 2 * d < c + g)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a + f < 4 * c ∧ 3 * a + c + d < 4 * c ∧ 2 * a + c + f < 4 * c ∧ 2 * a + d + e < 4 * c ∧ a + 2 * c + d < 4 * c ∧ a + e + f < 4 * c ∧ 2 * c + f < 4 * c ∧ c + d + e < 4 * c ∧ 3 * d < 4 * c ∧ f + g < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1041 (a c d f g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a + f < 4 * c ∧ 2 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1042 (a c d f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a + f < 4 * c ∧ 2 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1043 (a c d e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a + f < 4 * c ∧ 2 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1044 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a + f < 4 * c ∧ 2 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1045 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a + f < 4 * c ∧ 2 * a + c + d < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1046 (a c d e f g : Nat)
    (q0 : 3 * a + f < 4 * c ∧ 2 * a + c + d < 4 * c)
    (q1 : e < a + c)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    3 * a + f < 4 * c ∧ 2 * a + c + d < 4 * c ∧ a + c + f < 4 * c ∧ a + d + e < 4 * c ∧ 2 * c + d < 4 * c ∧ e + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1047 (a b : Nat)
    (q0 : 0 < a)
    (q1 : b = 0) :
    ¬ (a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1048 (a c f g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : g = 2 * c) :
    2 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1049 (a c d f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    2 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1050 (a c e f g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * f < 2 * g)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    2 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1051 (a c f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    2 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1052 (a c f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    2 * a + f < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1053 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 4 * c)
    (q2 : 2 * e < c + g)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : g = 2 * c) :
    2 * a + f < 4 * c ∧ a + c + d < 4 * c ∧ c + f < 4 * c ∧ d + e < 4 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1054 (a d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d)
    (q3 : e + g < 2 * a + 2 * d) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1055 (a c d e f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + d = f)
    (q4 : c + g < a + 2 * d)
    (q5 : e + g < 2 * a + 2 * d) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1056 (a d e g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : e + g < 2 * a + 2 * d) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1057 (a d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + d = f)
    (q4 : e + g < 2 * a + 2 * d) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1058 (a c d e f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 4 * a + d < a + d + f)
    (q2 : 5 * a > 2 * d)
    (q3 : a + d = f)
    (q4 : c + g < a + 2 * d)
    (q5 : e + g < 2 * a + 2 * d) :
    4 * a + d < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1059 (a d e f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + d = f)
    (q4 : e + g < 2 * a + 2 * d) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1060 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < a + d + f)
    (q3 : a + d = f)
    (q4 : c + g < a + 2 * d)
    (q5 : e + g < 2 * a + 2 * d) :
    3 * a + d < a + d + f ∧ 2 * a + f < a + d + f ∧ a + c + d < a + d + f ∧ c + f < a + d + f ∧ d + e < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1061 (a b c d e f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : c + f < a + 3 * b)
    (q5 : d < a + b)
    (q6 : g < a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1062 (a b c d e f g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : c + f < a + 3 * b)
    (q5 : d < a + b)
    (q6 : g < a + 2 * b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1063 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b)
    (q6 : f < 2 * a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1064 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b)
    (q6 : f < 2 * a + b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1065 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b < a + 2 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b)
    (q6 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1066 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b + c < 2 * a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b)
    (q6 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1067 (a g : Nat)
    (q0 : 0 < a)
    (q1 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1068 (a g : Nat)
    (q0 : 0 < a)
    (q1 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1069 (a d : Nat)
    (q0 : 0 < a)
    (q1 : 5 * a ≤ 4 * d) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1070 (a g : Nat)
    (q0 : 0 < a)
    (q1 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1071 (a f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 7 * a > 2 * f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1072 (a f : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1073 (a f : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * f) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1074 (a c : Nat)
    (q0 : 0 < a)
    (q1 : c = 0) :
    ¬ (a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1075 (a d : Nat)
    (q0 : 0 < a)
    (q1 : d = 0) :
    ¬ (3 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1076 (a e : Nat)
    (q0 : 0 < a)
    (q1 : e = 0) :
    ¬ (5 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1077 (a f : Nat)
    (q0 : 0 < a)
    (q1 : 7 * a ≤ 4 * f) :
    f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1078 (a g : Nat)
    (q0 : 0 < a)
    (q1 : g = 0) :
    ¬ (9 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1079 (a b c : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ b + 2 * c < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1080 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1081 (a b d : Nat)
    (q0 : 4 * b < a + 2 * d)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 6 * b < 4 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1082 (a b d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 9 * a ≤ 4 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1083 (a b d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (q2 : 5 * a > 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * b + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1084 (a b d : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 6 * b < 4 * d) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1085 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 6 * b < 4 * d) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1086 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : a + 6 * b < 4 * d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ 3 * b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1087 (a b d : Nat)
    (q0 : a + 6 * b < 4 * d)
    (q1 : a ≤ 4 * b) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1088 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + 6 * b < 4 * d) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1089 (a b d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < a + 2 * d) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1090 (a b e : Nat)
    (q0 : 3 * a + 6 * b < 4 * e)
    (q1 : 5 * a ≤ 4 * b) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1091 (a b e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * b < e)
    (q2 : 3 * a > e) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1092 (a b e : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 4 * a + b < 2 * e) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1093 (a b e : Nat)
    (q0 : 3 * a + 6 * b < 4 * e)
    (q1 : 3 * a ≤ 4 * b) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1094 (a b e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 9 * a ≤ 4 * e) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1095 (a b e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 3 * a + b < 2 * e) :
    3 * a + b < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1096 (a b e : Nat)
    (q0 : 3 * a + 6 * b < 4 * e)
    (q1 : a ≤ 4 * b) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1097 (a b e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 7 * a ≤ 4 * e) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1098 (a b f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1099 (a b c f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : c = 0)
    (q2 : f < 2 * a + b) :
    ¬ (7 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1100 (a b d f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : d = 0)
    (q2 : f < 2 * a + b) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1101 (a b e f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : e = 0)
    (q2 : f < 2 * a + b) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1102 (a b f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1103 (a b f g : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : f < 2 * a + b)
    (q2 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1104 (a b f : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1105 (a b f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1106 (a b c f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : c = 0)
    (q2 : f < 2 * a + b) :
    ¬ (5 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1107 (a b d f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : d = 0)
    (q2 : f < 2 * a + b) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1108 (a b e f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : e = 0)
    (q2 : f < 2 * a + b) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1109 (a b f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1110 (a b f g : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : f < 2 * a + b)
    (q2 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1111 (a b f : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1112 (a b f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : a ≤ 4 * b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1113 (a b c f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : c = 0)
    (q2 : f < 2 * a + b) :
    ¬ (3 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1114 (a b d f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : d = 0)
    (q2 : f < 2 * a + b) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1115 (a b e f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : e = 0)
    (q2 : f < 2 * a + b) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1116 (a b f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1117 (a b f g : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : f < 2 * a + b)
    (q2 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1118 (a b f : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1119 (a b f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a + b = f)
    (q2 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1120 (a b f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1121 (a b f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 3 * a ≤ 4 * b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1122 (a b f : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1123 (a b f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1124 (a b f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : 7 * a > 2 * f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1125 (a b f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f) :
    2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * b + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1126 (a c d : Nat)
    (q0 : 2 * a > c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * d < 3 * c) :
    3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1127 (a c d : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * d < 3 * c) :
    3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1128 (a c d : Nat)
    (q0 : 2 * a > c)
    (q1 : 3 * a + d < 3 * c) :
    3 * a + d < 3 * c ∧ a + c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1129 (a c d : Nat)
    (q0 : 0 < a)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * d < 3 * c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1130 (a c d : Nat)
    (q0 : 2 * a > c)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * d < 3 * c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1131 (a c d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < 3 * c)
    (q2 : a + 2 * d < 3 * c) :
    2 * a + d < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1132 (a c d : Nat)
    (q0 : 3 * c < a + 2 * d)
    (q1 : 5 * a > 2 * d)
    (q2 : 7 * a ≤ 4 * c) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1133 (a c d : Nat)
    (q0 : 3 * a + d < a + 2 * d)
    (q1 : 3 * c < a + 2 * d)
    (q2 : 5 * a > 2 * d) :
    3 * a + d < a + 2 * d ∧ a + c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1134 (a c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * c < a + 2 * d)
    (q2 : 5 * a ≤ 4 * c) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1135 (a c d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < a + 2 * d)
    (q2 : 3 * c < a + 2 * d) :
    2 * a + d < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1136 (a c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : 3 * c < a + 2 * d) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1137 (a c f : Nat)
    (q0 : 2 * a > c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f < 4 * c) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1138 (a c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1139 (a c f : Nat)
    (q0 : 2 * a + f < 3 * c)
    (q1 : 2 * a > c) :
    2 * a + f < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1140 (a c f : Nat)
    (q0 : 0 < a)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * f < 4 * c) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1141 (a c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1142 (a c f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 7 * a ≤ 4 * c) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1143 (a c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1144 (a c f : Nat)
    (q0 : 2 * a + f < 3 * c)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c) :
    2 * a + f < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1145 (a c f : Nat)
    (q0 : 0 < a)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * f = 4 * c) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1146 (a c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1147 (a c f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1148 (a c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 4 * c < a + 2 * f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1149 (a c f : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 4 * c < a + 2 * f) :
    3 * a + f < 2 * f ∧ a + c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1150 (a c f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 5 * a ≤ 4 * c) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1151 (a c f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : 3 * a + 2 * c = 2 * f) :
    2 * a + f < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1152 (a c f : Nat)
    (q0 : 3 * a + 2 * c < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : 7 * a ≤ 4 * c) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1153 (a c f : Nat)
    (q0 : 3 * a + 2 * c < 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f) :
    3 * a + f < 2 * f ∧ a + c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1154 (a c f : Nat)
    (q0 : 3 * a + 2 * c < 2 * f)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : 7 * a > 2 * f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1155 (a c f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : 3 * a + 2 * c < 2 * f) :
    2 * a + f < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1156 (a d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < a + 2 * d)
    (q2 : 5 * a > 2 * d) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1157 (a d e : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 5 * a > 2 * d) :
    3 * a + d < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1158 (a d e : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 5 * a > 2 * d)
    (q2 : 9 * a ≤ 4 * e) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1159 (a d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * e < a + 2 * d)
    (q2 : 7 * a ≤ 4 * e) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1160 (a d e : Nat)
    (q0 : 3 * a > e)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1161 (a d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1162 (a d e : Nat)
    (q0 : 3 * a + d < 2 * e)
    (q1 : 3 * a > e) :
    3 * a + d < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1163 (a d e : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1164 (a d e : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1165 (a d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 5 * a > 2 * d)
    (q2 : f < a + d) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1166 (a d f : Nat)
    (q0 : 3 * a + d < a + 2 * d)
    (q1 : f < a + d) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1167 (a d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 5 * a > 2 * d)
    (q2 : f < a + d) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1168 (a d f : Nat)
    (q0 : 2 * a + d < a + 2 * d)
    (q1 : f < a + d) :
    2 * a + d < a + 2 * d ∧ a + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1169 (a d f : Nat)
    (q0 : 5 * a > 2 * d)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : f < a + d) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1170 (a d f : Nat)
    (q0 : a + d < a + 2 * d)
    (q1 : f < a + d) :
    a + d < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1171 (a d f : Nat)
    (q0 : 7 * a > 2 * f)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + d < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1172 (a d f : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1173 (a d f : Nat)
    (q0 : 7 * a > 2 * f)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + d < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1174 (a d f : Nat)
    (q0 : 2 * a + f < 2 * f)
    (q1 : a + d < f) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1175 (a e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * e < 2 * f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1176 (a e f : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * e < 2 * f) :
    3 * a + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1177 (a e f : Nat)
    (q0 : 7 * a > 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * e < 2 * f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1178 (a e f : Nat)
    (q0 : 0 < a)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * e < 2 * f) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1179 (a f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * a > g)
    (q2 : a + 2 * f < 2 * g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1180 (a f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 4 * a > g)
    (q2 : a + 2 * f < 2 * g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1181 (a f g : Nat)
    (q0 : 4 * a + f < 2 * g)
    (q1 : 4 * a > g) :
    4 * a + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1182 (a f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 4 * a > g)
    (q2 : a + 2 * f < 2 * g) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1183 (a f g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : a + 2 * f < 2 * g) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1184 (a f g : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * f < 2 * g) :
    2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1185 (a f g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : a + 2 * f < 2 * g) :
    2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1186 (a b c d : Nat)
    (q0 : 2 * a > c)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1187 (a b c d : Nat)
    (q0 : 2 * a > c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1188 (a b c d : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1189 (a b c d : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1190 (a b c d : Nat)
    (q0 : 2 * a > c)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1191 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c) :
    3 * a + b < 3 * c ∧ 2 * a + d < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1192 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1193 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c) :
    2 * a + b < 3 * c ∧ a + d < 3 * c ∧ b + c < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1194 (a b c d : Nat)
    (q0 : 2 * b + c < 2 * d)
    (q1 : 3 * c < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : 7 * a ≤ 4 * c) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1195 (a b c d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 3 * c < a + 2 * d)
    (q2 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d)
    (q4 : b + c < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1196 (a b c d : Nat)
    (q0 : 2 * b + c < 2 * d)
    (q1 : 3 * c < a + 2 * d)
    (q2 : 5 * a ≤ 4 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1197 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : 3 * c < a + 2 * d)
    (q3 : a + 6 * b < 4 * d)
    (q4 : b + c < a + d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1198 (a b c d : Nat)
    (q0 : 2 * b + c < 2 * d)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : 3 * c < a + 2 * d) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1199 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < a + 2 * d)
    (q2 : 2 * b + c < 2 * d)
    (q3 : 3 * c < a + 2 * d) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d := by
  omega

end Max11DegreeRoutes
