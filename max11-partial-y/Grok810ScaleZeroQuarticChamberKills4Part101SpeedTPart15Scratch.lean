import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3000 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : e < a + c)
    (q6 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3001 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : e < a + c)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g ∧ d + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3002 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : e < a + c)
    (q6 : g < 2 * a + c) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ b + e < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3003 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d)
    (q6 : d + f < c + g) :
    3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g ∧ 4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3004 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g ∧ 4 * a + f < 2 * g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + b + e < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ 2 * a + d + e < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + c + e < 2 * g ∧ a + b + 2 * d < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 3 * b + e < 2 * g ∧ 2 * b + c + d < 2 * g ∧ b + 3 * c < 2 * g ∧ a + e + f < 2 * g ∧ b + c + g < 2 * g ∧ b + d + f < 2 * g ∧ b + 2 * e < 2 * g ∧ 2 * c + f < 2 * g ∧ c + d + e < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3005 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d)
    (q6 : d + f < c + g) :
    3 * a + b + c < 2 * g ∧ 3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3006 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + b + c < 2 * g ∧ 3 * a + f < 2 * g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d) :
    3 * a + b + c < 2 * g ∧ 2 * a + 3 * b < 2 * g ∧ 3 * a + f < 2 * g ∧ 2 * a + b + e < 2 * g ∧ 2 * a + c + d < 2 * g ∧ a + 2 * b + d < 2 * g ∧ a + b + 2 * c < 2 * g ∧ 3 * b + c < 2 * g ∧ a + c + f < 2 * g ∧ a + d + e < 2 * g ∧ 2 * b + f < 2 * g ∧ b + c + e < 2 * g ∧ b + 2 * d < 2 * g ∧ 2 * c + d < 2 * g ∧ e + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3007 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * e)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d)
    (q6 : d + f < c + g) :
    2 * a + b + c < 2 * g ∧ 2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3008 (a b c d e f g : Nat)
    (q0 : 2 * a + b + c < 2 * g ∧ 2 * a + f < 2 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d)
    (q6 : d + f < c + g) :
    2 * a + b + c < 2 * g ∧ a + 3 * b < 2 * g ∧ 2 * a + f < 2 * g ∧ a + b + e < 2 * g ∧ a + c + d < 2 * g ∧ 2 * b + d < 2 * g ∧ b + 2 * c < 2 * g ∧ c + f < 2 * g ∧ d + e < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3009 (a b c d e f g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 4 * a + d < e + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * c = 2 * d)
    (q5 : c + g = a + 2 * d)
    (q6 : d + f < c + g) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3010 (a b c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < g)
    (q2 : 4 * a + f < 2 * g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * c = 2 * d)
    (q5 : c + g = a + 2 * d)
    (q6 : e < a + c) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + b + e < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ 2 * a + d + e < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + c + e < 2 * g ∧ a + b + 2 * d < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 3 * b + e < 2 * g ∧ 2 * b + c + d < 2 * g ∧ b + 3 * c < 2 * g ∧ a + e + f < 2 * g ∧ b + c + g < 2 * g ∧ b + d + f < 2 * g ∧ b + 2 * e < 2 * g ∧ 2 * c + f < 2 * g ∧ c + d + e < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3011 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + b + f < c + g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3012 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3013 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3014 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3015 (a b c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + b + f < c + g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3016 (a b c d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3017 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 3 * a + f < e + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3018 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + b + f < c + g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3019 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3020 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3021 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3022 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + b + f < c + g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3023 (a b c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3024 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ 2 * a + f < e + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ a + 3 * b < e + g ∧ 2 * a + f < e + g ∧ a + b + e < e + g ∧ a + c + d < e + g ∧ 2 * b + d < e + g ∧ b + 2 * c < e + g ∧ c + f < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3025 (a b c d e f g : Nat)
    (q0 : 2 * a + d < e + g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + b + f < c + g)
    (q5 : c + g = 2 * e)
    (q6 : e < a + c) :
    2 * a + d < e + g ∧ a + b + c < e + g ∧ 3 * b < e + g ∧ a + f < e + g ∧ b + e < e + g ∧ c + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3026 (a b c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + b + f < c + g)
    (q5 : a + c = e)
    (q6 : c + g = 2 * e) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3027 (a b c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < g)
    (q2 : 4 * a + d < e + g ∧ 3 * a + f < e + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g)
    (q5 : a + c = e)
    (q6 : c + g = 2 * e) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3028 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a + c = g)
    (q2 : 2 * c < g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g)
    (q5 : a + 2 * f < 2 * g)
    (q6 : e < a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3029 (a b c d e f g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g)
    (q5 : e < a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g ∧ d + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3030 (a b c d e f g : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 2 * g < 3 * a + 2 * d)
    (q2 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q3 : 3 * a > 2 * b)
    (q4 : 3 * c < a + 2 * d)
    (q5 : 4 * b < a + 2 * d)
    (q6 : 5 * a > 2 * d)
    (q7 : b + c < a + d)
    (q8 : f < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3031 (a b c d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * e < a + 2 * d)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : 3 * c < a + 2 * d)
    (q4 : a + 6 * b < 4 * d)
    (q5 : b + c < a + d)
    (q6 : f < a + d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3032 (a b c d e f g : Nat)
    (q0 : 2 * c + 2 * f < a + 4 * d)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e)
    (q4 : a + d = f)
    (q5 : b + f < 2 * d)
    (q6 : e + g < 2 * a + 2 * d) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3033 (a c d e g : Nat)
    (q0 : 6 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : e < a + c) :
    5 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3034 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 6 * a ≤ e + f)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    5 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3035 (a b c d e g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    5 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3036 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 6 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : b + g < d + e)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c)
    (q6 : f = 0)
    (q7 : g = 2 * c) :
    5 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3037 (a b c d e g : Nat)
    (q0 : 6 * a ≤ b + c + e)
    (q1 : b + g < d + e)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    5 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3038 (a b c d e g : Nat)
    (q0 : 6 * a ≤ b + 2 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    5 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3039 (a c d e g : Nat)
    (q0 : 6 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    5 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3040 (a b c d e g : Nat)
    (q0 : 6 * a ≤ 3 * b + c)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    5 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3041 (a b c d e g : Nat)
    (q0 : 5 * a < d + e)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    5 * a < d + e ∧ 3 * a + c < d + e ∧ 2 * a + 2 * b < d + e ∧ 2 * a + e < d + e ∧ a + b + d < d + e ∧ a + 2 * c < d + e ∧ 2 * b + c < d + e ∧ a + g < d + e ∧ c + e < d + e ∧ 2 * d < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3042 (a c d e g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : e < a + c) :
    4 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3043 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ e + f)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    4 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3044 (a b c d e g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    4 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3045 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : b + g < d + e)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c)
    (q6 : f = 0)
    (q7 : g = 2 * c) :
    4 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3046 (a b c d e g : Nat)
    (q0 : 5 * a ≤ b + c + e)
    (q1 : b + g < d + e)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    4 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3047 (a b c d e g : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    4 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3048 (a c d e g : Nat)
    (q0 : 5 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    4 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3049 (a b c d e g : Nat)
    (q0 : 5 * a ≤ 3 * b + c)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    4 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3050 (a b c d e g : Nat)
    (q0 : 4 * a < d + e)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    4 * a < d + e ∧ 2 * a + c < d + e ∧ a + 2 * b < d + e ∧ a + e < d + e ∧ b + d < d + e ∧ 2 * c < d + e ∧ g < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3051 (a c d e g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : e < a + c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3052 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ e + f)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3053 (a b c d e g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3054 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : b + g < d + e)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c)
    (q6 : f = 0)
    (q7 : g = 2 * c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3055 (a b c d e g : Nat)
    (q0 : 4 * a ≤ b + c + e)
    (q1 : b + g < d + e)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3056 (a b c d e g : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3057 (a c d e g : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3058 (a b c d e g : Nat)
    (q0 : 4 * a ≤ 3 * b + c)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3059 (a b c d e g : Nat)
    (q0 : 4 * a ≤ b + e)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3060 (a c d e g : Nat)
    (q0 : 4 * a ≤ c + d)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3061 (a b c d e g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3062 (a b c d e g : Nat)
    (q0 : 3 * a < d + e)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < d + e ∧ a + c < d + e ∧ 2 * b < d + e ∧ e < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3063 (a b c d e g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3064 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3065 (a b c d e g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3066 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ 2 * b + f)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3067 (a b c d e g : Nat)
    (q0 : 3 * a ≤ b + c + e)
    (q1 : b + g < d + e)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3068 (a b c d e g : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3069 (a b c d e g : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3070 (a b c d e g : Nat)
    (q0 : 3 * a ≤ 3 * b + c)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3071 (a b c d e g : Nat)
    (q0 : 3 * a ≤ b + e)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3072 (a c d e g : Nat)
    (q0 : 3 * a ≤ c + d)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3073 (a b c d e g : Nat)
    (q0 : a + 2 * d < c + g)
    (q1 : a ≤ b)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3074 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ f)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3075 (a b c d e g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3076 (a b c d e g : Nat)
    (q0 : 2 * a < d + e)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < d + e ∧ c < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3077 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 6 * a ≤ d + g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3078 (a c e f : Nat)
    (q0 : 6 * a ≤ e + f)
    (q1 : e < a + c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3079 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : b + g < c + f)
    (q4 : c + g = 2 * e)
    (q5 : d = 0)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3080 (a b c e f g : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3081 (a b c e f g : Nat)
    (q0 : 6 * a ≤ b + c + e)
    (q1 : b + g < c + f)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3082 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 6 * a ≤ b + 2 * d)
    (q3 : b + g < c + f)
    (q4 : c + g = 2 * e)
    (q5 : d = 0)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3083 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 6 * a ≤ 2 * c + d)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3084 (a b c e f g : Nat)
    (q0 : 6 * a ≤ 3 * b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3085 (a b c e f g : Nat)
    (q0 : 5 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    5 * a < c + f ∧ 3 * a + c < c + f ∧ 2 * a + 2 * b < c + f ∧ 2 * a + e < c + f ∧ a + 2 * c < c + f ∧ 2 * b + c < c + f ∧ a + g < c + f ∧ b + f < c + f ∧ c + e < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3086 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 5 * a ≤ d + g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3087 (a c e f : Nat)
    (q0 : 5 * a ≤ e + f)
    (q1 : e < a + c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3088 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : b + g < c + f)
    (q4 : c + g = 2 * e)
    (q5 : d = 0)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3089 (a b c e f g : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3090 (a b c e f g : Nat)
    (q0 : 5 * a ≤ b + c + e)
    (q1 : b + g < c + f)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3091 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 5 * a ≤ b + 2 * d)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3092 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 5 * a ≤ 2 * c + d)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3093 (a b c e f g : Nat)
    (q0 : 5 * a ≤ 3 * b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3094 (a b c e f g : Nat)
    (q0 : 4 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    4 * a < c + f ∧ 2 * a + c < c + f ∧ a + 2 * b < c + f ∧ a + e < c + f ∧ 2 * c < c + f ∧ g < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3095 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3096 (a c e f : Nat)
    (q0 : 4 * a ≤ e + f)
    (q1 : e < a + c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3097 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : b + g < c + f)
    (q4 : c + g = 2 * e)
    (q5 : d = 0)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3098 (a b c e f g : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3099 (a b c e f g : Nat)
    (q0 : 4 * a ≤ b + c + e)
    (q1 : b + g < c + f)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3100 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 4 * a ≤ b + 2 * d)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3101 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3102 (a b c e f g : Nat)
    (q0 : 4 * a ≤ 3 * b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3103 (a b c e f g : Nat)
    (q0 : 4 * a ≤ b + e)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3104 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 4 * a ≤ c + d)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3105 (a b c e f g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3106 (a b c e f g : Nat)
    (q0 : 3 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < c + f ∧ a + c < c + f ∧ 2 * b < c + f ∧ e < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3107 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : b + g < c + f)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3108 (a b c e f g : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3109 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3110 (a b c e f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3111 (a b c e f g : Nat)
    (q0 : 3 * a ≤ b + c + e)
    (q1 : b + g < c + f)
    (q2 : e < a + c)
    (q3 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3112 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 3 * a ≤ b + 2 * d)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3113 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : b + g < c + f)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3114 (a b c e f g : Nat)
    (q0 : 3 * a ≤ 3 * b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3115 (a b c e f g : Nat)
    (q0 : 3 * a ≤ b + e)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3116 (a b c d e f g : Nat)
    (q0 : 2 * e + 2 * f < a + 2 * c + 2 * g)
    (q1 : 3 * a ≤ c + d)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3117 (a b c e f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a ≤ b)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3118 (a c e f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3119 (a b c e f g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3120 (a b c e f g : Nat)
    (q0 : 2 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < c + f ∧ c < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3121 (a c d e f g : Nat)
    (q0 : 6 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : d + e < c + f)
    (q3 : e < a + c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3122 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3123 (a b c d e f g : Nat)
    (q0 : 6 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3124 (a c d e f g : Nat)
    (q0 : 6 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : d + e < c + f)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    5 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3125 (a b c d e f g : Nat)
    (q0 : 5 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    5 * a < c + f ∧ 3 * a + c < c + f ∧ 2 * a + 2 * b < c + f ∧ 2 * a + e < c + f ∧ a + b + d < c + f ∧ a + 2 * c < c + f ∧ 2 * b + c < c + f ∧ a + g < c + f ∧ b + f < c + f ∧ c + e < c + f ∧ 2 * d < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3126 (a c d e f g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : d + e < c + f)
    (q3 : e < a + c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3127 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3128 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3129 (a c d e f g : Nat)
    (q0 : 5 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : d + e < c + f)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    4 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3130 (a b c d e f g : Nat)
    (q0 : 4 * a < c + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    4 * a < c + f ∧ 2 * a + c < c + f ∧ a + 2 * b < c + f ∧ a + e < c + f ∧ b + d < c + f ∧ 2 * c < c + f ∧ g < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3131 (a c d e f g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : d + e < c + f)
    (q3 : e < a + c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3132 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3133 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3134 (a c d e f g : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : d + e < c + f)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3135 (a c d e f g : Nat)
    (q0 : 4 * a ≤ c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = 2 * e)
    (q3 : d + e < c + f)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3136 (a c d e f g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : d + e < c + f)
    (q3 : e < a + c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3137 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3138 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g < c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3139 (a c d e f g : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : d + e < c + f)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3140 (a c d e f g : Nat)
    (q0 : 3 * a ≤ c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + g = 2 * e)
    (q3 : d + e < c + f)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < c + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3141 (a c d e f : Nat)
    (q0 : 6 * a ≤ e + f)
    (q1 : c + f < d + e)
    (q2 : e < a + c) :
    5 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3142 (a b c d e f g : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + f < d + e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    5 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3143 (a b c d e f g : Nat)
    (q0 : 5 * a < d + e)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + f < d + e)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    5 * a < d + e ∧ 3 * a + c < d + e ∧ 2 * a + 2 * b < d + e ∧ 2 * a + e < d + e ∧ a + b + d < d + e ∧ a + 2 * c < d + e ∧ 2 * b + c < d + e ∧ a + g < d + e ∧ b + f < d + e ∧ c + e < d + e ∧ 2 * d < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3144 (a c d e f : Nat)
    (q0 : 5 * a ≤ e + f)
    (q1 : c + f < d + e)
    (q2 : e < a + c) :
    4 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3145 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + f < d + e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    4 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3146 (a c d e f : Nat)
    (q0 : 4 * a ≤ e + f)
    (q1 : c + f < d + e)
    (q2 : e < a + c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3147 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + f < d + e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3148 (a c d e f : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : c + f < d + e)
    (q2 : e < a + c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3149 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g < d + e)
    (q3 : c + f < d + e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3150 (a c d e f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + 2 * d < c + g)
    (q2 : c + f < d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < d + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3151 (a b c d g : Nat)
    (q0 : 6 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3152 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 6 * a ≤ e + f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q4 : b + g = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : f = 0)
    (q7 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3153 (a b c d : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d < a + b) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3154 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 6 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3155 (a b c d e g : Nat)
    (q0 : 6 * a ≤ b + c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3156 (a b c d : Nat)
    (q0 : 6 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d < a + b) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3157 (a b c d : Nat)
    (q0 : 6 * a ≤ 2 * c + d)
    (q1 : d < a + b) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3158 (a b c d g : Nat)
    (q0 : 6 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3159 (a b c d e g : Nat)
    (q0 : 5 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : b + g = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    5 * a < b + 2 * c ∧ 3 * a + c < b + 2 * c ∧ 2 * a + 2 * b < b + 2 * c ∧ 2 * a + e < b + 2 * c ∧ a + b + d < b + 2 * c ∧ a + 2 * c < b + 2 * c ∧ 2 * b + c < b + 2 * c ∧ a + g < b + 2 * c ∧ c + e < b + 2 * c ∧ 2 * d < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3160 (a b c d g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3161 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ e + f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q4 : b + g = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : f = 0)
    (q7 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3162 (a b c d : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d < a + b) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3163 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3164 (a b c d e g : Nat)
    (q0 : 5 * a ≤ b + c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3165 (a b c d : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d < a + b) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3166 (a b c d : Nat)
    (q0 : 5 * a ≤ 2 * c + d)
    (q1 : d < a + b) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3167 (a b c d g : Nat)
    (q0 : 5 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3168 (a b c d e g : Nat)
    (q0 : 4 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c ∧ 2 * a + c < b + 2 * c ∧ a + 2 * b < b + 2 * c ∧ a + e < b + 2 * c ∧ b + d < b + 2 * c ∧ 2 * c < b + 2 * c ∧ g < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3169 (a b c d g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3170 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ e + f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q4 : c + g = a + 2 * d)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3171 (a b c d : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d < a + b) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3172 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3173 (a b c d e g : Nat)
    (q0 : 4 * a ≤ b + c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3174 (a b c d : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d < a + b) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3175 (a b c d : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : d < a + b) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3176 (a b c d g : Nat)
    (q0 : 4 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3177 (a b c d e g : Nat)
    (q0 : 4 * a ≤ b + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3178 (a b c d g : Nat)
    (q0 : 4 * a ≤ c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3179 (a b c d g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3180 (a b c d e g : Nat)
    (q0 : 3 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c ∧ a + c < b + 2 * c ∧ 2 * b < b + 2 * c ∧ e < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3181 (a b c d g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3182 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ e + f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q4 : c + g = a + 2 * d)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3183 (a b c d : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d < a + b) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3184 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ 2 * b + f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : f = 0)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3185 (a b c d e g : Nat)
    (q0 : 3 * a ≤ b + c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3186 (a b c d : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d < a + b) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3187 (a b c d : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : d < a + b) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3188 (a b c d g : Nat)
    (q0 : 3 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3189 (a b c d e g : Nat)
    (q0 : 3 * a ≤ b + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3190 (a b c d g : Nat)
    (q0 : 3 * a ≤ c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3191 (a b c d g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a ≤ b)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3192 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : f = 0)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3193 (a b c d g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3194 (a b c d g : Nat)
    (q0 : 2 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c ∧ c < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3195 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3196 (a b c d g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3197 (a b c d g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3198 (a b c d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3199 (a b c d f g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : c + g = a + 2 * d)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = 2 * c) :
    ¬ (13 * a ≤ 4 * f) := by
  omega

end Max11DegreeRoutes
