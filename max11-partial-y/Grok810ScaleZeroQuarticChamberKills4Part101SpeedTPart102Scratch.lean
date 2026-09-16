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
/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1200 (a b c e : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1201 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ b + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1202 (a b c e : Nat)
    (q0 : 3 * c < 2 * e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b + c < 2 * e) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1203 (a b c e : Nat)
    (q0 : 2 * b < e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e)
    (q3 : 4 * a + b < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1204 (a b c e : Nat)
    (q0 : 3 * c < 2 * e)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b + c < 2 * e) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1205 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 2 * c < a + e)
    (q3 : 3 * a + b < 2 * e) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1206 (a b c e : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : 3 * c < 2 * e)
    (q2 : a + 2 * b + c < 2 * e) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1207 (a b c e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 2 * e)
    (q2 : 3 * c < 2 * e)
    (q3 : a + 2 * b + c < 2 * e) :
    2 * a + b < 2 * e ∧ b + c < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1208 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1209 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1210 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1211 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1212 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1213 (a b c f : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1214 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1215 (a b c f : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1216 (a b c d f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0)
    (q3 : f < 2 * a + b) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1217 (a b c e f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0)
    (q3 : f < 2 * a + b) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1218 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1219 (a b c f g : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : f < 2 * a + b)
    (q3 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1220 (a b c f : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1221 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1222 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1223 (a b c d f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0)
    (q3 : f < 2 * a + b) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1224 (a b c e f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0)
    (q3 : f < 2 * a + b) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1225 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1226 (a b c f g : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : f < 2 * a + b)
    (q3 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1227 (a b c f : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1228 (a b c f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : a ≤ 4 * b)
    (q2 : b + c < f) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1229 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1230 (a b c d f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0)
    (q3 : f < 2 * a + b) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1231 (a b c e f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0)
    (q3 : f < 2 * a + b) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1232 (a b c f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1233 (a b c f g : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : f < 2 * a + b)
    (q3 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1234 (a b c f : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : b + c < f)
    (q2 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1235 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1236 (a b c f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1237 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1238 (a b c f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1239 (a b c f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1240 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 2 * c < a + 2 * b)
    (q3 : 3 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1241 (a b c f : Nat)
    (q0 : 2 * a > c)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < 3 * c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1242 (a b c f : Nat)
    (q0 : 2 * a > c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 4 * c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1243 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c)
    (q3 : a + b + f < 3 * c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1244 (a b c f : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1245 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c)
    (q3 : a + b + f < 3 * c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1246 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 4 * c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1247 (a b c f : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * f < 4 * c)
    (q3 : a + b + f < 3 * c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1248 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < 3 * c) :
    2 * a + b < 3 * c ∧ b + c < 3 * c ∧ f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1249 (a b c f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1250 (a b c f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1251 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1252 (a b c e f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1253 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1254 (a b c f g : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1255 (a b c f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1256 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1257 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1258 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1259 (a b c e f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1260 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1261 (a b c f g : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1262 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1263 (a b c f : Nat)
    (q0 : a + 2 * f = 4 * c)
    (q1 : a ≤ 4 * b)
    (q2 : b + c < f) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1264 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1265 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : d = 0) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1266 (a b c e f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1267 (a b c f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1268 (a b c f g : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : b + c < f)
    (q2 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1269 (a b c f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f) :
    2 * a + b < 3 * c ∧ b + c < 3 * c ∧ f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1270 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1271 (a b c f : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : b + c < f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1272 (a b c f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + 2 * c < 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 7 * a > 2 * f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1273 (a b c g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1274 (a b c g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1275 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1276 (a b e g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1277 (a b f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1278 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1279 (a b c g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1280 (a b c g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1281 (a b c g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1282 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1283 (a b e g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1284 (a b f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : f = 0) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1285 (a b c g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1286 (a b c g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1287 (a b c g : Nat)
    (q0 : a + 2 * b < g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a ≤ 4 * b) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1288 (a b c g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1289 (a b d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : d = 0) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1290 (a b e g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1291 (a b f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a + 2 * b < g)
    (q2 : f = 0) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1292 (a b c g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1293 (a b c g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    2 * a + b < c + g ∧ b + c < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1294 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1295 (a b c g : Nat)
    (q0 : 4 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1296 (a b c g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1297 (a b c g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1298 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * c) :
    4 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1299 (a b c g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1300 (a b c g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1301 (a b c g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1302 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1303 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1304 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : g < 2 * a + c) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1305 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e = 0)
    (q3 : g < 2 * a + c) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1306 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : f = 0)
    (q3 : g < 2 * a + c) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1307 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1308 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1309 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1310 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1311 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : g < 2 * a + c) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1312 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e = 0)
    (q3 : g < 2 * a + c) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1313 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : f = 0)
    (q3 : g < 2 * a + c) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1314 (a b c g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1315 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1316 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a ≤ 4 * b) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1317 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1318 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : g < 2 * a + c) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1319 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e = 0)
    (q3 : g < 2 * a + c) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1320 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : f = 0)
    (q3 : g < 2 * a + c) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1321 (a b c g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1322 (a b c g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    2 * a + b < c + g ∧ b + c < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1323 (a b c d g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1324 (a b c e g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1325 (a b c f g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1326 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + c = g)
    (q2 : 2 * c < g)
    (q3 : a + 2 * b < 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1327 (a b c g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 4 * a + b < c + g)
    (q3 : a + 2 * b < 2 * c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1328 (a b d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < a + 2 * d)
    (q2 : 3 * a > 2 * b)
    (q3 : 5 * a > 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1329 (a b d e : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + b + e < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1330 (a b d e : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 9 * a ≤ 4 * e) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1331 (a b d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * e < a + 2 * d)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 6 * b < 4 * d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ 3 * b < a + 2 * d ∧ b + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1332 (a b d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * e < a + 2 * d)
    (q2 : 7 * a ≤ 4 * e)
    (q3 : a + 6 * b < 4 * d) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1333 (a b d e : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a + 6 * b < 4 * e)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1334 (a b d e : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1335 (a b d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * b < e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1336 (a b d e : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 4 * a + b < 2 * e ∧ 3 * a + d < 2 * e)
    (q3 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ 2 * b + d < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1337 (a b d e : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1338 (a b d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + b < 2 * e ∧ 2 * a + d < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1339 (a b d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : a + 2 * d < 2 * e) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1340 (a b d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 2 * e)
    (q2 : a + 2 * d < 2 * e) :
    2 * a + b < 2 * e ∧ a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1341 (a b d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1342 (a b d f : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ 2 * b + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1343 (a b d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1344 (a b d f : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1345 (a b d f : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1346 (a b d f : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : d < a + b)
    (q2 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ a + d < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1347 (a b f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 4 * b < 2 * f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1348 (a b d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : a + b = d) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1349 (a b d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : a + b = d)
    (q3 : b + f = 2 * d) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1350 (a b d f : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : a + b = d)
    (q3 : b + f = 2 * d) :
    3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 5 * b < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ b + d + f < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1351 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + b = d)
    (q3 : b + f = 2 * d) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1352 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + b = d)
    (q3 : b + f = 2 * d) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1353 (a f : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1354 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + f < a + 2 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b = d)
    (q4 : b + f = 2 * d) :
    2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + 2 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1355 (a b d f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ 2 * b + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1356 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : d < a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1357 (a b d : Nat)
    (q0 : 4 * b < a + 2 * d)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 6 * b < 4 * d) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1358 (a b d : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 9 * a ≤ 4 * d) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1359 (a b d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a > 2 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : f < a + d) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1360 (a b d f : Nat)
    (q0 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * b < a + 2 * d)
    (q3 : f < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ 2 * b + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1361 (a b d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 3 * a > 2 * b)
    (q2 : f < a + d) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1362 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : a + 6 * b < 4 * d)
    (q3 : f < a + d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1363 (a b d f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : f < a + d) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1364 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < a + 2 * d)
    (q2 : b + f < 2 * d) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1365 (a b d f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + d < f) :
    4 * a + d < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ a + 2 * b + d < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1366 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < g) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1367 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : c = 0)
    (q3 : d < a + b) :
    ¬ (7 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1368 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1369 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1370 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1371 (a b d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1372 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1373 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b < g) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1374 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : c = 0)
    (q3 : d < a + b) :
    ¬ (5 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1375 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1376 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1377 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : f = 0) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1378 (a b d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1379 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ 3 * b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1380 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : a ≤ 4 * b) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1381 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : c = 0)
    (q3 : d < a + b) :
    ¬ (3 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1382 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1383 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1384 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : d < a + b)
    (q3 : f = 0) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1385 (a b d g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : d < a + b) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1386 (a b d : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : d < a + b) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1387 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1388 (a b d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1389 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1390 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1391 (a b d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1392 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ 3 * b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1393 (a b d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < 3 * a + 2 * d)
    (q2 : 3 * a > 2 * b)
    (q3 : 5 * a > 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1394 (a b d g : Nat)
    (q0 : 2 * g < 3 * a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1395 (a b d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < 3 * a + 2 * d)
    (q2 : 3 * a > 2 * b) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1396 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : 2 * b + 2 * g < a + 4 * d) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1397 (a b d g : Nat)
    (q0 : 2 * b + 2 * g < a + 4 * d)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ 4 * b) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1398 (a b d g : Nat)
    (q0 : 2 * b + 2 * g < a + 4 * d)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1399 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega

end Max11DegreeRoutes
/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1400 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1401 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1402 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1403 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1404 (a b e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : b + e < a + f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1405 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : b + e < a + f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1406 (a b e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + b + f = 2 * e)
    (q3 : b + e < a + f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1407 (a b e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + b + f = 2 * e)
    (q3 : b + e < a + f) :
    2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ 2 * b + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1408 (a b e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : b + e < a + f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1409 (a b e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : b + e < a + f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1410 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + b + f = 2 * e)
    (q3 : b + e < a + f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1411 (a b e f : Nat)
    (q0 : 2 * a + f < 2 * f)
    (q1 : a + b + f = 2 * e)
    (q2 : b + e < a + f) :
    a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ a + b + e < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1412 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a + b = f)
    (q2 : 2 * e < a + b + f)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1413 (a b e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1414 (a b e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1415 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 2 * e < a + b + f)
    (q3 : 3 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1416 (a b e f : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a + 6 * b < 4 * e)
    (q2 : 3 * a > e)
    (q3 : 5 * a ≤ 4 * b)
    (q4 : a + b + f < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1417 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * b < e)
    (q2 : 2 * f < a + 2 * e)
    (q3 : 3 * a > e) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1418 (a b e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + b + f < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1419 (a b e f : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 4 * a + b < 2 * e ∧ 2 * a + f < 2 * e) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1420 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + b + f < 2 * e) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1421 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + b + f < 2 * e) :
    3 * a + b < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1422 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + b + f < 2 * e) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1423 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 2 * e)
    (q2 : a + b + f < 2 * e) :
    2 * a + b < 2 * e ∧ f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1424 (a b e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + b + f < 2 * e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1425 (a e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1426 (a e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1427 (a b e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + b + f < 2 * e) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1428 (a b e f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * e < 2 * f) :
    2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ 2 * b + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1429 (a b e g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1430 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : c = 0) :
    ¬ (7 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1431 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1432 (a b e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1433 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1434 (a b e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1435 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 4 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1436 (a b e g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1437 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : c = 0) :
    ¬ (5 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1438 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1439 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1440 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : f = 0) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1441 (a b e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1442 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 3 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1443 (a b e g : Nat)
    (q0 : a + 2 * b + 2 * g = 4 * e)
    (q1 : a + 2 * b < g)
    (q2 : a ≤ 4 * b) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1444 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : c = 0) :
    ¬ (3 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1445 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : d = 0) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1446 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1447 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : f = 0) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1448 (a b e g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1449 (a b e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1450 (a b e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1451 (a b e g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 4 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1452 (a b e g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1453 (a b e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1454 (a b e g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1455 (a b e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * b < e)
    (q2 : 3 * a > e)
    (q3 : g < a + e) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1456 (a b e g : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 4 * a + b < 2 * e)
    (q3 : g < a + e) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1457 (a b e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * b < e)
    (q2 : 3 * a > e)
    (q3 : g < a + e) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1458 (a b e g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * b < e)
    (q2 : 3 * a > e)
    (q3 : g < a + e) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1459 (a b e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1460 (a b e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1461 (a b e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a > e)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1462 (a b e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 4 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1463 (a b f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1464 (a b f g : Nat)
    (q0 : 2 * g < a + 2 * f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + g < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1465 (a b f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1466 (a b f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1467 (a b f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1468 (a b f g : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + g < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1469 (a b f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1470 (a b f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1471 (a b f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1472 (a b f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + g < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1473 (a b f g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : a + 2 * f = 2 * g) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1474 (a b f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1475 (a b f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + g < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1476 (a b f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1477 (a b f g : Nat)
    (q0 : 5 * a + 2 * b = 2 * g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < g)
    (q3 : f < 2 * a + b) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1478 (a b f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : f < 2 * a + b) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1479 (a b f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : f < 2 * a + b) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1480 (a b f g : Nat)
    (q0 : 0 < a)
    (q1 : 4 * a + f < 2 * g)
    (q2 : 5 * a + 2 * b = 2 * g)
    (q3 : a + 2 * b < g) :
    3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 5 * b < 2 * g ∧ a + 2 * b + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1481 (a f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 7 * a > 2 * f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1482 (a f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1483 (a b f g : Nat)
    (q0 : 3 * a + b + f < 2 * g)
    (q1 : 4 * a > g)
    (q2 : 5 * a + 2 * b < 2 * g)
    (q3 : 5 * a ≤ 4 * b) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1484 (a b f g : Nat)
    (q0 : 0 < a)
    (q1 : 4 * a + f < 2 * g)
    (q2 : 4 * a > g)
    (q3 : 5 * a + 2 * b < 2 * g) :
    3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 5 * b < 2 * g ∧ a + 2 * b + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1485 (a c d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : e < a + c) :
    3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1486 (a c d e : Nat)
    (q0 : 2 * a > c)
    (q1 : 3 * a + d < 3 * c)
    (q2 : e < a + c) :
    3 * a + d < 3 * c ∧ a + c + d < 3 * c ∧ d + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1487 (a c d e : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * d < 3 * c)
    (q3 : e < a + c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1488 (a c d e : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 3 * c < a + 2 * d)
    (q3 : 5 * a > 2 * d) :
    3 * a + d < a + 2 * d ∧ a + c + d < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1489 (a c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1490 (a c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 3 * a + d < 2 * e)
    (q2 : 3 * a > e) :
    3 * a + d < 2 * e ∧ a + c + d < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1491 (a c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1492 (a c d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < 2 * e)
    (q2 : 3 * c < 2 * e)
    (q3 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1493 (a c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1494 (a c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1495 (a c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1496 (a c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1497 (a c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1498 (a c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < 3 * c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c) :
    2 * a + d < 3 * c ∧ a + f < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1499 (a c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1500 (a c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1501 (a c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1502 (a c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1503 (a c d f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * f = 4 * c)
    (q2 : c + d < a + f) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1504 (a c d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * f = 4 * c)
    (q2 : c + d < a + f) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1505 (a c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1506 (a c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    2 * a + d < 3 * c ∧ a + f < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1507 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 7 * a ≤ 4 * c) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1508 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 9 * a ≤ 4 * d) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1509 (a c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 4 * c < a + 2 * f) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1510 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + d < a + 2 * d)
    (q3 : 4 * c < a + 2 * f) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1511 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 5 * a ≤ 4 * c) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1512 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 7 * a ≤ 4 * d) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1513 (a c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 4 * c < a + 2 * f) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1514 (a c d f : Nat)
    (q0 : 2 * a + d < a + 2 * d)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 4 * c < a + 2 * f) :
    2 * a + d < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1515 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a ≤ 4 * c)
    (q3 : 4 * c < a + 2 * f) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1516 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 5 * a ≤ 4 * d) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1517 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 9 * a ≤ 4 * f) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1518 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : a + d < a + 2 * d) :
    a + d < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1519 (a c d f : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 9 * a ≤ 4 * d) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1520 (a c d f : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 4 * c < a + 2 * f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ 2 * c + d < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1521 (a c d f : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 7 * a ≤ 4 * d) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1522 (a c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 3 * a + 2 * c = 2 * f) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f ∧ a + c + d < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1523 (a c d f : Nat)
    (q0 : 3 * a + d < a + 2 * d)
    (q1 : 3 * c < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : f < a + d) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1524 (a c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < a + 2 * d)
    (q2 : 3 * c < a + 2 * d)
    (q3 : f < a + d) :
    2 * a + d < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1525 (a c d f : Nat)
    (q0 : 3 * a + 2 * c < 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ 2 * c + d < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1526 (a c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : 3 * a + 2 * c < 2 * f)
    (q3 : a + d < f) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f ∧ a + c + d < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1527 (a c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : g < 2 * c) :
    3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1528 (a c d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : g < 2 * c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1529 (a d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < 3 * a + 2 * d)
    (q2 : 5 * a > 2 * d) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1530 (a d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < 3 * a + 2 * d)
    (q2 : 5 * a > 2 * d) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1531 (a d g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : 2 * g < 3 * a + 2 * d) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1532 (a c d g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : c + g < a + 2 * d) :
    3 * a + d < a + 2 * d ∧ a + c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1533 (a c d g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < a + 2 * d)
    (q2 : 3 * a + 2 * d = 2 * g)
    (q3 : c + g < a + 2 * d) :
    2 * a + d < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1534 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c)
    (q3 : e < a + c) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1535 (a c e f : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * f < 4 * c)
    (q3 : e < a + c) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1536 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : e < a + c) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1537 (a c e f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : e < a + c) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1538 (a b c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b = 0)
    (q3 : e < a + c) :
    ¬ (5 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1539 (a c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1540 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : d = 0)
    (q3 : e < a + c) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1541 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1542 (a c e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1543 (a c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : e < a + c)
    (q3 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1544 (a c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    2 * a + f < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1545 (a b c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b = 0)
    (q3 : e < a + c) :
    ¬ (3 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1546 (a c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1547 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : d = 0)
    (q3 : e < a + c) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1548 (a c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1549 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1550 (a c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : e < a + c)
    (q3 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1551 (a c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1552 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1553 (a c e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1554 (a c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    2 * a + f < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1555 (a c e f : Nat)
    (q0 : 0 < a)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1556 (a c e f : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1557 (a c e f : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1558 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : e < a + c) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1559 (a c e f : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : e < a + c) :
    3 * a + f < 2 * f ∧ a + c + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1560 (a c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : e < a + c) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1561 (a c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 7 * a ≤ 4 * c) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1562 (a e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1563 (a e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1564 (a c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e) :
    2 * a + f < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1565 (a c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 5 * a ≤ 4 * c) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1566 (a e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 9 * a ≤ 4 * e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1567 (a e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1568 (a c e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f < 4 * e)
    (q3 : a + 2 * e = 2 * f) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1569 (a c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * c + 2 * f < 4 * e)
    (q3 : a + 2 * e = 2 * f) :
    2 * a + f < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1570 (a c e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f < 4 * e)
    (q3 : a + 2 * e = 2 * f) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1571 (a e f : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * e = 2 * f) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1572 (a e f : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * f)
    (q2 : a + 2 * e = 2 * f) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1573 (a c e f : Nat)
    (q0 : 3 * a + 2 * c < 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * e < 2 * f) :
    3 * a + f < 2 * f ∧ a + c + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1574 (a c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c)
    (q3 : g < 2 * c) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1575 (a c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c)
    (q3 : g < 2 * c) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1576 (a c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1577 (a c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1578 (a c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : g < 2 * a + c) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1579 (a c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : g < 2 * a + c) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1580 (a f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 7 * a > 2 * f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1581 (a c f g : Nat)
    (q0 : 7 * a > 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1582 (a c f g : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f) :
    3 * a + f < 2 * f ∧ a + c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1583 (a c f g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1584 (a f g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : a + 2 * f = 2 * g) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1585 (a c f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f) :
    2 * a + f < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1586 (a c f g : Nat)
    (q0 : 2 * a + c < g)
    (q1 : 4 * a > g)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * f < 2 * g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1587 (a c f g : Nat)
    (q0 : 2 * a + c < g)
    (q1 : 4 * a + f < 2 * g)
    (q2 : 4 * a > g) :
    4 * a + f < 2 * g ∧ 2 * a + c + f < 2 * g ∧ 2 * c + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1588 (a c f g : Nat)
    (q0 : 2 * a + c < g)
    (q1 : 4 * a > g)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * f < 2 * g) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1589 (a c f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + c < g)
    (q2 : 3 * a + f < 2 * g)
    (q3 : a + 2 * f < 2 * g) :
    3 * a + f < 2 * g ∧ a + c + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1590 (a d e f : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : f < a + d) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1591 (a d f : Nat)
    (q0 : 5 * a > 2 * d)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + d = f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1592 (a d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1593 (a d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 5 * a > 2 * d)
    (q2 : a + d = f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1594 (a d e f : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    4 * a + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + e + f < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1595 (a d f : Nat)
    (q0 : 0 < a)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + d = f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1596 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1597 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + f < a + 2 * f)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    3 * a + f < a + 2 * f ∧ a + d + e < a + 2 * f ∧ e + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1598 (a d f : Nat)
    (q0 : 0 < a)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + d = f) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1599 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    2 * a + f < a + 2 * f := by
  omega

end Max11DegreeRoutes
/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1600 (a f : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * f) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1601 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < a + 2 * f)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    2 * a + f < a + 2 * f ∧ d + e < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1602 (a d e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * d < 2 * e)
    (q3 : d + f < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1603 (a d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1604 (a d e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1605 (a d e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * d < 2 * e)
    (q3 : d + f < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1606 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1607 (a d e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : d + f < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1608 (a d e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * e = 2 * f)
    (q3 : d + f < 2 * e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1609 (a d e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f)
    (q3 : d + f < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1610 (a d e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * e = 2 * f)
    (q3 : d + f < 2 * e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1611 (a d e f : Nat)
    (q0 : a + 2 * e = 2 * f)
    (q1 : a + f < 2 * e)
    (q2 : d + f < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1612 (a d e f : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * e < 2 * f)
    (q3 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ a + d + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1613 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * e < 2 * f)
    (q3 : a + d < f) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f ∧ d + e < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1614 (a d e g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * d = 2 * e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1615 (a d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1616 (a d e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1617 (a d e g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 4 * a + d < e + g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e) :
    4 * a + d < e + g ∧ a + d + e < e + g ∧ d + g < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1618 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : a + 2 * d = 2 * e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1619 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 9 * a ≤ 4 * e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1620 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : a + 2 * d = 2 * e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1621 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < e + g) :
    3 * a + d < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1622 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : a + 2 * d = 2 * e) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1623 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 7 * a ≤ 4 * e) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1624 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : a + 2 * d = 2 * e) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1625 (a d f g : Nat)
    (q0 : 2 * g < a + 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ d + g < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1626 (a d f g : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ d + g < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1627 (a d f g : Nat)
    (q0 : 2 * a + d + f < 2 * g)
    (q1 : 3 * a + 2 * d < 2 * g)
    (q2 : 4 * a > g)
    (q3 : 9 * a ≤ 4 * d) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1628 (a d f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d < 2 * g)
    (q2 : 4 * a + f < 2 * g)
    (q3 : 4 * a > g) :
    4 * a + f < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1629 (a d f g : Nat)
    (q0 : 2 * a + d + f < 2 * g)
    (q1 : 3 * a + 2 * d < 2 * g)
    (q2 : 4 * a > g)
    (q3 : 7 * a ≤ 4 * d) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1630 (a f g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : 2 * g < a + 2 * f) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1631 (a e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1632 (a e f g : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * f) :
    3 * a + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1633 (a e f g : Nat)
    (q0 : 7 * a > 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1634 (a e f g : Nat)
    (q0 : 7 * a > 2 * f)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * f) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1635 (a f g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : a + 2 * f = 2 * g) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1636 (a e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * a > g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + e < g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1637 (a e f g : Nat)
    (q0 : 4 * a + f < 2 * g)
    (q1 : 4 * a > g)
    (q2 : a + e < g) :
    4 * a + f < 2 * g ∧ a + e + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1638 (a e f g : Nat)
    (q0 : 4 * a > g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + e < g) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1639 (a e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + f < 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + e < g) :
    3 * a + f < 2 * g ∧ e + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1640 (a e f g : Nat)
    (q0 : 4 * a > g)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + e < g) :
    2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1641 (a b c d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : e < a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1642 (a b c d e : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : e < a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + b + e < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ d + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1643 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : e < a + c) :
    3 * a + b < 3 * c ∧ 2 * a + d < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ b + e < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1644 (a b c d e : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * c < a + 2 * d)
    (q3 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (q4 : 5 * a > 2 * d)
    (q5 : b + c < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1645 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * e < a + 2 * d)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : 3 * c < a + 2 * d)
    (q4 : a + 6 * b < 4 * d)
    (q5 : b + c < a + d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1646 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 3 * c < 2 * e)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1647 (a b c d e : Nat)
    (q0 : 2 * b < e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e)
    (q3 : 4 * a + b < 2 * e ∧ 3 * a + d < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1648 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 2 * c < a + e)
    (q3 : 3 * a + b < 2 * e)
    (q4 : 3 * c < 2 * e)
    (q5 : a + 2 * d < 2 * e) :
    3 * a + b < 2 * e ∧ 2 * a + d < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1649 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 2 * e)
    (q2 : 3 * c < 2 * e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    2 * a + b < 2 * e ∧ a + d < 2 * e ∧ b + c < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1650 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1651 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1652 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1653 (a b c d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1654 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1655 (a b c e g : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1656 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e ∧ 2 * a + 3 * b < 2 * c + e ∧ 2 * a + b + e < 2 * c + e ∧ 2 * a + c + d < 2 * c + e ∧ a + 2 * b + d < 2 * c + e ∧ a + b + 2 * c < 2 * c + e ∧ 3 * b + c < 2 * c + e ∧ a + d + e < 2 * c + e ∧ b + c + e < 2 * c + e ∧ b + 2 * d < 2 * c + e ∧ 2 * c + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1657 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 3 * a ≤ 4 * b)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1658 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1659 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1660 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1661 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : f = 0) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1662 (a b c e g : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1663 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e)
    (q3 : a + 2 * b + c < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e ∧ a + 3 * b < 2 * c + e ∧ a + b + e < 2 * c + e ∧ a + c + d < 2 * c + e ∧ 2 * b + d < 2 * c + e ∧ b + 2 * c < 2 * c + e ∧ d + e < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1664 (a b c d e : Nat)
    (q0 : 2 * e = 3 * c)
    (q1 : a + 2 * b + c < 2 * e)
    (q2 : a + 2 * d < 2 * e)
    (q3 : a ≤ 4 * b) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1665 (a c d e : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1666 (a c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1667 (a c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 7 * a ≤ 4 * e)
    (q3 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1668 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : f = 0) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1669 (a b c e g : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1670 (a b c d e : Nat)
    (q0 : 2 * a + d < 2 * c + e)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e) :
    2 * a + d < 2 * c + e ∧ a + b + c < 2 * c + e ∧ 3 * b < 2 * c + e ∧ b + e < 2 * c + e ∧ c + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1671 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1672 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1673 (a b c d f : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ a + d < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1674 (a b c d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1675 (a b c d f : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1676 (a b c d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1677 (a b c d f : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1678 (a b c d f : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1679 (a b c d f : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : b + c < f)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ a + d < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1680 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1681 (a b c f : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1682 (a b c d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1683 (a b c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1684 (a b c d f : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ b + d + f < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1685 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1686 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1687 (a b c d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1688 (a b c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1689 (a b c d f : Nat)
    (q0 : 3 * a + f < a + 2 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d) :
    3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ 2 * c + d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1690 (a b c d f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1691 (a b c d f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : d < a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1692 (a b d f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 4 * b < 2 * f) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1693 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1694 (a b d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1695 (a b d e f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1696 (a b d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1697 (a b d f g : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1698 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 4 * a + d < a + d + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ 2 * b + f < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1699 (a b d f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 4 * b < 2 * f) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1700 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1701 (a b d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1702 (a b d e f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1703 (a b d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1704 (a b d f g : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1705 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + d < a + d + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + d + f ∧ 2 * a + b + c < a + d + f ∧ a + 3 * b < a + d + f ∧ 2 * a + f < a + d + f ∧ a + c + d < a + d + f ∧ 2 * b + d < a + d + f ∧ b + 2 * c < a + d + f ∧ c + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1706 (a b d f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : a ≤ 4 * b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1707 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1708 (a b d f : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1709 (a b d e f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1710 (a b d f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1711 (a b d f g : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1712 (a b c d f : Nat)
    (q0 : 2 * a + d < a + d + f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + d + f ∧ a + b + c < a + d + f ∧ 3 * b < a + d + f ∧ a + f < a + d + f ∧ c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1713 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1714 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b = d)
    (q4 : b + f = 2 * d) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ b + d + f < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1715 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1716 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b = d)
    (q5 : b + f = 2 * d) :
    3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ 2 * c + d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1717 (a b c d f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1718 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 2 * c < a + 2 * b)
    (q3 : 3 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : d < a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1719 (a b c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + b + f < 3 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1720 (a b c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + 2 * f < 4 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1721 (a b c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + 2 * f < 4 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1722 (a b c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c)
    (q4 : a + b + f < 3 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1723 (a b c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1724 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + 2 * f < 4 * c) :
    3 * a + b < 3 * c ∧ 2 * a + d < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1725 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + b + f < 3 * c) :
    2 * a + b < 3 * c ∧ a + d < 3 * c ∧ b + c < 3 * c ∧ f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1726 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1727 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1728 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1729 (a b c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1730 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1731 (a b c d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f)
    (q3 : c + d < a + f) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1732 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : a + 4 * d < 2 * c + 2 * f)
    (q4 : b + c < f)
    (q5 : c + d < a + f) :
    3 * a + b < 3 * c ∧ 2 * a + d < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1733 (a b c d f : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f)
    (q3 : c + d < a + f) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1734 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : a + 4 * d < 2 * c + 2 * f)
    (q4 : b + c < f)
    (q5 : c + d < a + f) :
    2 * a + b < 3 * c ∧ a + d < 3 * c ∧ b + c < 3 * c ∧ f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1735 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b < 2 * c)
    (q4 : b + c < f) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1736 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 7 * a ≤ 4 * c)
    (q4 : b + c < f) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1737 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 9 * a ≤ 4 * d)
    (q4 : b + c < f) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1738 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1739 (a b c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 4 * c < a + 2 * f)
    (q4 : b + c < f) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1740 (a b c d f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1741 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q3 : 4 * c < a + 2 * f)
    (q4 : a + 2 * b < 2 * c)
    (q5 : b + c < f) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1742 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : b + c < f) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1743 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : b + c < f) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1744 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : b + c < f) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1745 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1746 (a b c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : b + c < f) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1747 (a b c d f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1748 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : 4 * c < a + 2 * f)
    (q4 : b + c < f) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1749 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a ≤ 4 * b)
    (q3 : b + c < f) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1750 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : b + c < f) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1751 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : b + c < f) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1752 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1753 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 9 * a ≤ 4 * f)
    (q3 : b + c < f) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1754 (a b c d f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1755 (a b c d f : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 4 * c < a + 2 * f)
    (q4 : a + 2 * b < 2 * c)
    (q5 : b + c < f) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1756 (a b c d f : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : a + 2 * b < 2 * c)
    (q5 : b + c < f) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1757 (a b c d : Nat)
    (q0 : 2 * b + c < 2 * d)
    (q1 : 3 * c < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : 7 * a ≤ 4 * c) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1758 (a b c d f : Nat)
    (q0 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * c < a + 2 * d)
    (q3 : 4 * b < a + 2 * d)
    (q4 : 5 * a > 2 * d)
    (q5 : b + c < a + d)
    (q6 : f < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1759 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : 3 * c < a + 2 * d)
    (q3 : a + 6 * b < 4 * d)
    (q4 : b + c < a + d)
    (q5 : f < a + d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1760 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < a + 2 * d)
    (q2 : 2 * b + c < 2 * d)
    (q3 : 3 * c < a + 2 * d)
    (q4 : b + f < 2 * d) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1761 (a b c d f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + 2 * c < 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 7 * a > 2 * f)
    (q4 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1762 (a b c d g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1763 (a b c d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1764 (a b c d g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1765 (a b c d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1766 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1767 (a b c d g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    2 * a + b < c + g ∧ a + d < c + g ∧ b + c < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1768 (a b c d g : Nat)
    (q0 : 4 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1769 (a b c d g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1770 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b < g) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1771 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : d < a + b) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1772 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * b < g) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1773 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1774 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a ≤ 4 * c)
    (q3 : a + 2 * b < g) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1775 (a b c d g : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : 2 * c < a + 2 * b)
    (q3 : a + 2 * b < g)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1776 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1777 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1778 (a b c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1779 (a b c d g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1780 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1781 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1782 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1783 (a b c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1784 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g ∧ 3 * a + d < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1785 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1786 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1787 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1788 (a b c d g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g ∧ a + d < c + g ∧ b + c < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1789 (a b c d g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1790 (a b c d g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1791 (a b c d g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1792 (a b c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + c = g)
    (q2 : 2 * c < g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1793 (a b c d g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 4 * a + b < c + g ∧ 3 * a + d < c + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1794 (a b c d g : Nat)
    (q0 : 2 * g < 3 * a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * c < a + 2 * d)
    (q3 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (q4 : 5 * a > 2 * d)
    (q5 : b + c < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1795 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g < a + 4 * d)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d)
    (q4 : c + g < a + 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1796 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1797 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1798 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1799 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega

end Max11DegreeRoutes
/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1800 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1801 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1802 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1803 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1804 (a b c f : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1805 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1806 (a b c e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1807 (a b c e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1808 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1809 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1810 (a b c e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1811 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1812 (a b c e f : Nat)
    (q0 : 2 * a + f < 2 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f) :
    2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ a + b + e < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1813 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a + b = f)
    (q2 : 2 * e < a + b + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1814 (a b c e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1815 (a b c e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1816 (a b c e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1817 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1818 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1819 (a b e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1820 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1821 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 4 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b + f = 2 * e) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1822 (a b f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 4 * b < 2 * f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1823 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1824 (a b e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 4 * b < 2 * f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1825 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1826 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1827 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 3 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b + f = 2 * e) :
    3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + b + e < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + c + e < a + 2 * f ∧ e + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1828 (a b f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : a ≤ 4 * b) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1829 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1830 (a b c d e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : d = 0) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1831 (a b e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 4 * b < 2 * f) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1832 (a b e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1833 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1834 (a b c e f : Nat)
    (q0 : 2 * a + f < a + 2 * f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b + f = 2 * e) :
    2 * a + b + c < a + 2 * f ∧ a + 3 * b < a + 2 * f ∧ 2 * a + f < a + 2 * f ∧ a + b + e < a + 2 * f ∧ b + 2 * c < a + 2 * f ∧ c + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1835 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : b + e < a + f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1836 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 3 * a + f < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : b + e < a + f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1837 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : b + e < a + f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1838 (a b c e f : Nat)
    (q0 : 2 * a + f < 2 * f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + 2 * b = 2 * e)
    (q3 : a + b + f = 2 * e)
    (q4 : b + e < a + f) :
    2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ a + b + e < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1839 (a b c e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < a + b + f)
    (q3 : 4 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1840 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 2 * c < a + 2 * b)
    (q3 : 2 * e < a + b + f)
    (q4 : 3 * a + b < a + b + f)
    (q5 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1841 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 4 * c)
    (q4 : e < a + c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1842 (a b c e f : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1843 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 4 * c)
    (q4 : e < a + c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ b + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1844 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1845 (a b c e f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1846 (a b c e f : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1847 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ b + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1848 (a b c e f : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1849 (a b c e f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1850 (a b c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1851 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1852 (a b c e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1853 (a b c e f : Nat)
    (q0 : 4 * a + b < 2 * e ∧ 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1854 (a b c e f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1855 (a b c e f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1856 (a b c e f : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1857 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1858 (a b c e f : Nat)
    (q0 : 3 * a + b < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1859 (a b c e f : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : a ≤ 4 * b)
    (q3 : b + c < f) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1860 (a b c e f : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1861 (a b c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : d = 0)
    (q4 : e < a + c) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1862 (a b c e f : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1863 (a b c e f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b + c < f)
    (q3 : e < a + c) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1864 (a b c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c)
    (q4 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1865 (a b c e f : Nat)
    (q0 : 2 * a + b < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : b + c < f)
    (q5 : e < a + c) :
    2 * a + b < 2 * e ∧ b + c < 2 * e ∧ f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1866 (a b c e f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e)
    (q4 : b + c < f) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1867 (a b c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : a + c = e)
    (q5 : b + c < f) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1868 (a b c e f : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : b + c < f)
    (q5 : e < a + c) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1869 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * c < 2 * e)
    (q3 : 7 * a ≤ 4 * c)
    (q4 : a + 2 * b + c < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1870 (a b c e f : Nat)
    (q0 : 2 * b < e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e)
    (q3 : 4 * a + b < 2 * e ∧ 2 * a + f < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1871 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 2 * c < a + e)
    (q3 : 3 * a + b < 2 * e)
    (q4 : a + b + f < 2 * e) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1872 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 2 * e)
    (q2 : 3 * c < 2 * e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + b + f < 2 * e) :
    2 * a + b < 2 * e ∧ b + c < 2 * e ∧ f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1873 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + b + f < 2 * e) :
    3 * a + b + c < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1874 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * c + 2 * f < 4 * e) :
    3 * a + b + c < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1875 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1876 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * c + 2 * f < 4 * e) :
    3 * a + b + c < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1877 (a b c e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + b + f < 2 * e) :
    3 * a + b + c < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1878 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 3 * a + b + c < 2 * c + e ∧ 3 * a + f < 2 * c + e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + b + f < 2 * e) :
    3 * a + b + c < 2 * c + e ∧ 2 * a + 3 * b < 2 * c + e ∧ 3 * a + f < 2 * c + e ∧ 2 * a + b + e < 2 * c + e ∧ a + b + 2 * c < 2 * c + e ∧ 3 * b + c < 2 * c + e ∧ a + c + f < 2 * c + e ∧ 2 * b + f < 2 * c + e ∧ b + c + e < 2 * c + e ∧ e + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1879 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 3 * a ≤ 4 * b)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + b + f < 2 * e) :
    2 * a + b + c < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1880 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * c + 2 * f < 4 * e) :
    2 * a + b + c < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1881 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1882 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * c + 2 * f < 4 * e) :
    2 * a + b + c < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1883 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * c + 2 * f < 4 * e)
    (q4 : a + b + f < 2 * e) :
    2 * a + b + c < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1884 (a b c e f : Nat)
    (q0 : 2 * a + b + c < 2 * c + e ∧ 2 * a + f < 2 * c + e)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e) :
    2 * a + b + c < 2 * c + e ∧ a + 3 * b < 2 * c + e ∧ 2 * a + f < 2 * c + e ∧ a + b + e < 2 * c + e ∧ b + 2 * c < 2 * c + e ∧ c + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1885 (a b c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * c + 2 * f < 4 * e)
    (q3 : a + 2 * e = 2 * f)
    (q4 : a + b + f < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1886 (a b c e f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + 2 * c < 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 7 * a > 2 * f)
    (q4 : a + 2 * e < 2 * f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1887 (a b c e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1888 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a + b < c + g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1889 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1890 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a + b < c + g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ b + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1891 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1892 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 4 * a + b < c + g)
    (q2 : 5 * a + 2 * b = 2 * g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1893 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 3 * a + b < c + g)
    (q2 : 5 * a + 2 * b = 2 * g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ b + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1894 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1895 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 4 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1896 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1897 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1898 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1899 (a b c e g : Nat)
    (q0 : 2 * a + b < 2 * e)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g) :
    2 * a + b < 2 * e ∧ b + c < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1900 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 4 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1901 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1902 (a b c e g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c)
    (q4 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1903 (a b c e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1904 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1905 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1906 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ b + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1907 (a b c e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1908 (a b c e g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 4 * a + b < c + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : e < a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1909 (a b c e g : Nat)
    (q0 : 2 * b < e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e)
    (q3 : 4 * a + b < 2 * e)
    (q4 : g < a + e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1910 (a b c e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1911 (a b c e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 4 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1912 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1913 (a b c f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1914 (a b c f g : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1915 (a b c f g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1916 (a b c f g : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1917 (a b c f g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1918 (a b c f g : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1919 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1920 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1921 (a b c f : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1922 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1923 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1924 (a b c f : Nat)
    (q0 : 2 * a + f < 2 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1925 (a b c f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : a ≤ 4 * b)
    (q2 : b + c < f) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1926 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1927 (a b c f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1928 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1929 (a b c f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : a + f < 2 * f)
    (q2 : b + c < f)
    (q3 : f < 2 * a + b) :
    a + b + c < 2 * f ∧ 3 * b < 2 * f ∧ a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1930 (a b c f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1931 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + c < f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1932 (a b c f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1933 (a b c f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1934 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + c < f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1935 (a b c f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f) :
    2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1936 (a b c f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * b < 2 * f)
    (q4 : c + g < a + b + f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1937 (a b c f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + 4 * b < 2 * f)
    (q5 : c + g < a + b + f) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1938 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1939 (a b c f g : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1940 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1941 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : c + g < a + b + f)
    (q4 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1942 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : c + g < a + b + f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1943 (a b c f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : c + g < a + b + f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1944 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : c + g < a + b + f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1945 (a b c f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1946 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1947 (a b c f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1948 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1949 (a b c f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1950 (a b c f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1951 (a b c f g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    2 * a + b < c + g ∧ b + c < c + g ∧ f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1952 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1953 (a b c f g : Nat)
    (q0 : 4 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1954 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1955 (a b c f g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1956 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b < g)
    (q4 : f < 2 * a + b) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1957 (a b c f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + f < 2 * g)
    (q3 : 5 * a + 2 * b = 2 * g)
    (q4 : a + 2 * b < g) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + 2 * b + f < 2 * g ∧ b + 3 * c < 2 * g ∧ b + c + g < 2 * g ∧ 2 * c + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1958 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 4 * c)
    (q4 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1959 (a b c f g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1960 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1961 (a b c f g : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1962 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1963 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1964 (a b c f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1965 (a b c f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1966 (a b c d f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : d = 0)
    (q4 : g < 2 * a + c) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1967 (a b c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : e = 0)
    (q4 : g < 2 * a + c) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1968 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1969 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1970 (a b c f g : Nat)
    (q0 : 4 * a + b < c + g ∧ 2 * a + f < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1971 (a b c f g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1972 (a b c f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1973 (a b c d f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : d = 0)
    (q4 : g < 2 * a + c) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1974 (a b c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : e = 0)
    (q4 : g < 2 * a + c) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1975 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1976 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1977 (a b c f g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1978 (a b c f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a ≤ 4 * b)
    (q3 : b + g < c + f) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1979 (a b c f g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1980 (a b c d f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : d = 0)
    (q4 : g < 2 * a + c) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1981 (a b c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : b + g < c + f)
    (q3 : e = 0)
    (q4 : g < 2 * a + c) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1982 (a b c f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1983 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1984 (a b c f g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g ∧ b + c < c + g ∧ f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1985 (a b c f g : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + g < c + f) :
    2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1986 (a c f g : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * f = 2 * g) :
    2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1987 (a b c d f g : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1988 (a b c e f g : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1989 (a c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * f = 2 * g) :
    2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1990 (a c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * f = 2 * g) :
    2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1991 (a b c f g : Nat)
    (q0 : 2 * a + f < c + g)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + g < c + f) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1992 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1993 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1994 (a b c f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1995 (a b c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1996 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g ∧ 2 * a + f < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1997 (a b c f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1998 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1999 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + b + f < c + g)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g := by
  omega

end Max11DegreeRoutes
