import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3200 (a b c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3201 (a b c d e g : Nat)
    (q0 : 4 * a + b < a + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3202 (a b c d g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3203 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3204 (a b c d g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3205 (a b c d e g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3206 (a b c d f g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : c + g = a + 2 * d)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = 2 * c) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3207 (a b c d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3208 (a b c d e g : Nat)
    (q0 : 3 * a + b < a + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3209 (a b c d g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a ≤ 4 * b)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3210 (a b c d g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3211 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3212 (a b c d e g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3213 (a b c d f g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : c + g = a + 2 * d)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = 2 * c) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3214 (a b c d g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3215 (a b c d g : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3216 (a b c d g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3217 (a b c d f g : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3218 (a b c d e g : Nat)
    (q0 : 5 * a ≤ d + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3219 (a b c d g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3220 (a b c d g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3221 (a b c d g : Nat)
    (q0 : 5 * a ≤ b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3222 (a b c d e g : Nat)
    (q0 : 4 * a + d < a + b + c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + d < a + b + c + d ∧ 3 * a + b + c < a + b + c + d ∧ 2 * a + 3 * b < a + b + c + d ∧ 2 * a + b + e < a + b + c + d ∧ 2 * a + c + d < a + b + c + d ∧ a + 2 * b + d < a + b + c + d ∧ a + b + 2 * c < a + b + c + d ∧ 3 * b + c < a + b + c + d ∧ a + d + e < a + b + c + d ∧ b + c + e < a + b + c + d ∧ b + 2 * d < a + b + c + d ∧ 2 * c + d < a + b + c + d ∧ d + g < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3223 (a b c d g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3224 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : f = 0)
    (q5 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3225 (a b c d e g : Nat)
    (q0 : 4 * a ≤ d + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3226 (a b c d g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a ≤ b)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3227 (a b c d g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3228 (a b c d g : Nat)
    (q0 : 4 * a ≤ b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3229 (a b c d e g : Nat)
    (q0 : 3 * a + d < a + b + c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + d < a + b + c + d ∧ 2 * a + b + c < a + b + c + d ∧ a + 3 * b < a + b + c + d ∧ a + b + e < a + b + c + d ∧ a + c + d < a + b + c + d ∧ 2 * b + d < a + b + c + d ∧ b + 2 * c < a + b + c + d ∧ d + e < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3230 (a b c d g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3231 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ c + f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : f = 0)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3232 (a b c d e g : Nat)
    (q0 : 3 * a ≤ d + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3233 (a b c d g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3234 (a b c d g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3235 (a b c d g : Nat)
    (q0 : 3 * a ≤ b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3236 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : f = 0)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3237 (a b c d g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3238 (a b c d e g : Nat)
    (q0 : 2 * a + d < a + b + c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d ∧ a + b + c < a + b + c + d ∧ 3 * b < a + b + c + d ∧ b + e < a + b + c + d ∧ c + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3239 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3240 (a b c d g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3241 (a b c d g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3242 (a b c d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3243 (a b c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3244 (a b c d e g : Nat)
    (q0 : 4 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : b + g = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 3 * a + b + e < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + d + e < a + c + 2 * d ∧ a + b + c + e < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 3 * b + e < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ b + c + g < a + c + 2 * d ∧ b + 2 * e < a + c + 2 * d ∧ c + d + e < a + c + 2 * d ∧ 3 * d < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3245 (a b c d g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3246 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3247 (a b c d g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3248 (a b c d e g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3249 (a b c d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3250 (a b c d e g : Nat)
    (q0 : 3 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : b + g = d + e)
    (q4 : c + g = a + 2 * d)
    (q5 : d < a + b)
    (q6 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d ∧ 2 * a + 3 * b < a + c + 2 * d ∧ 2 * a + b + e < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + 2 * b + d < a + c + 2 * d ∧ a + b + 2 * c < a + c + 2 * d ∧ 3 * b + c < a + c + 2 * d ∧ a + d + e < a + c + 2 * d ∧ b + c + e < a + c + 2 * d ∧ b + 2 * d < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3251 (a b c d g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a ≤ 4 * b)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3252 (a b c d g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3253 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3254 (a b c d e g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3255 (a b c d g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = a + 2 * d)
    (q3 : d < a + b)
    (q4 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3256 (a b c d e g : Nat)
    (q0 : 2 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q3 : c + g = a + 2 * d)
    (q4 : d < a + b)
    (q5 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d ∧ a + 3 * b < a + c + 2 * d ∧ a + b + e < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ 2 * b + d < a + c + 2 * d ∧ b + 2 * c < a + c + 2 * d ∧ d + e < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3257 (a b c d e g : Nat)
    (q0 : 6 * a ≤ d + g)
    (q1 : b + g = d + e)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3258 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 6 * a ≤ e + f)
    (q2 : b + g = d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3259 (a b c d e g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3260 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 6 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : b + g = d + e)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c)
    (q6 : f = 0)
    (q7 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3261 (a b c d e g : Nat)
    (q0 : 6 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3262 (a b c d e g : Nat)
    (q0 : 6 * a ≤ 2 * c + d)
    (q1 : b + g = d + e)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3263 (a b c d e g : Nat)
    (q0 : 5 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c ∧ 3 * a + c < b + 2 * c ∧ 2 * a + 2 * b < b + 2 * c ∧ 2 * a + e < b + 2 * c ∧ a + b + d < b + 2 * c ∧ a + 2 * c < b + 2 * c ∧ 2 * b + c < b + 2 * c ∧ a + g < b + 2 * c ∧ c + e < b + 2 * c ∧ 2 * d < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3264 (a b c d e g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : b + g = d + e)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3265 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ e + f)
    (q2 : b + g = d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3266 (a b c d e g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3267 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : b + g = d + e)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c)
    (q6 : f = 0)
    (q7 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3268 (a b c d e g : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3269 (a b c d e g : Nat)
    (q0 : 5 * a ≤ 2 * c + d)
    (q1 : b + g = d + e)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3270 (a b c d e g : Nat)
    (q0 : 4 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c ∧ 2 * a + c < b + 2 * c ∧ a + 2 * b < b + 2 * c ∧ a + e < b + 2 * c ∧ b + d < b + 2 * c ∧ 2 * c < b + 2 * c ∧ g < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3271 (a b c d e g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : b + g = d + e)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3272 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ e + f)
    (q2 : b + g = d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3273 (a b c d e g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3274 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : b + g = d + e)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c)
    (q6 : f = 0)
    (q7 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3275 (a b c d e g : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3276 (a b c d e g : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : b + g = d + e)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3277 (a b c d e g : Nat)
    (q0 : 4 * a ≤ c + d)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g = d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3278 (a b c d e g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : b + g = d + e)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3279 (a b c d e g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3280 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ 2 * b + f)
    (q2 : b + g = d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3281 (a b c d e g : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3282 (a b c d e g : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : b + g = d + e)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3283 (a b c d e g : Nat)
    (q0 : 3 * a ≤ c + d)
    (q1 : a + 2 * d < c + g)
    (q2 : b + g = d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3284 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ f)
    (q2 : b + g = d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3285 (a b c d e g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e) :
    4 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3286 (a c d e g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e) :
    4 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3287 (a c d e g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    4 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3288 (a c d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    4 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3289 (a c d e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    4 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3290 (a b c d e g : Nat)
    (q0 : 4 * a + d < 2 * c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : b + g = d + e)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e ∧ 2 * a + 3 * b < 2 * c + e ∧ 2 * a + b + e < 2 * c + e ∧ 2 * a + c + d < 2 * c + e ∧ a + 2 * b + d < 2 * c + e ∧ a + b + 2 * c < 2 * c + e ∧ 3 * b + c < 2 * c + e ∧ a + d + e < 2 * c + e ∧ b + c + e < 2 * c + e ∧ b + 2 * d < 2 * c + e ∧ 2 * c + d < 2 * c + e ∧ d + g < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3291 (a b c d e g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e) :
    3 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3292 (a c d e g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e) :
    3 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3293 (a c d e g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    3 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3294 (a c d e g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    3 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3295 (a c d e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    3 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3296 (a b c d e g : Nat)
    (q0 : 3 * a + d < 2 * c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e ∧ a + 3 * b < 2 * c + e ∧ a + b + e < 2 * c + e ∧ a + c + d < 2 * c + e ∧ 2 * b + d < 2 * c + e ∧ b + 2 * c < 2 * c + e ∧ d + e < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3297 (a b c d e g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a + 2 * d < c + g)
    (q2 : a ≤ 4 * b)
    (q3 : c + g = 2 * e) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3298 (a c d e g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3299 (a c d e g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3300 (a c d e g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3301 (a c d e g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * d < c + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3302 (a b c d e g : Nat)
    (q0 : 2 * a + d < 2 * c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = d + e)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a + d < 2 * c + e ∧ a + b + c < 2 * c + e ∧ 3 * b < 2 * c + e ∧ b + e < 2 * c + e ∧ c + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3303 (a b d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 6 * a ≤ d + g)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3304 (a b d e f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a > e)
    (q3 : 6 * a ≤ e + f)
    (q4 : e = 0)
    (q5 : f < a + d) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3305 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : f < a + d) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3306 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 6 * a ≤ 2 * b + f)
    (q2 : f < a + d) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3307 (a b c d e f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a > e)
    (q3 : 6 * a ≤ b + c + e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : e = 0)
    (q6 : f < a + d) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3308 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 6 * a ≤ b + 2 * d)
    (q2 : f < a + d) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3309 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 6 * a ≤ 2 * c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < a + d) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3310 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 6 * a ≤ 3 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3311 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : f < a + d) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3312 (a b d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ d + g)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3313 (a b d e f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a > e)
    (q3 : 5 * a ≤ e + f)
    (q4 : e = 0)
    (q5 : f < a + d) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3314 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : f < a + d) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3315 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ 2 * b + f)
    (q2 : f < a + d) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3316 (a b c d e f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a > e)
    (q3 : 5 * a ≤ b + c + e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : e = 0)
    (q6 : f < a + d) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3317 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ b + 2 * d)
    (q2 : f < a + d) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3318 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ 2 * c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < a + d) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3319 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ 3 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3320 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : f < a + d) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3321 (a b d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ d + g)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3322 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3323 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ 2 * b + f)
    (q2 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3324 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ b + 2 * d)
    (q2 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3325 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ 2 * c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3326 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 3 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3327 (a b d e f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a > e)
    (q3 : 4 * a ≤ b + e)
    (q4 : e = 0)
    (q5 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3328 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3329 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 3 * b)
    (q3 : f < a + d) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3330 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3331 (a b d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ d + g)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3332 (a b d e f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ e + f)
    (q3 : e = 0)
    (q4 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3333 (a b d f : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : 2 * d < b + f)
    (q2 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3334 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ 2 * b + f)
    (q2 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3335 (a b c d e f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + c + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : e = 0)
    (q5 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3336 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ b + 2 * d)
    (q2 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3337 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ 2 * c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3338 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ 3 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3339 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3340 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a ≤ b)
    (q3 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3341 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ f)
    (q3 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3342 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3343 (a b c d f : Nat)
    (q0 : 2 * a < a + 3 * b)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3344 (a b d f g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3345 (a b d e f : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : 2 * d < b + f)
    (q2 : e = 0)
    (q3 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3346 (a b d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : a ≤ 2 * b + d)
    (q2 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3347 (a b d f : Nat)
    (q0 : 2 * a ≤ 2 * b + f)
    (q1 : 2 * d < b + f)
    (q2 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3348 (a b c d e f : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : e = 0)
    (q5 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3349 (a b d f : Nat)
    (q0 : 2 * a ≤ b + 2 * d)
    (q1 : 2 * d < b + f)
    (q2 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3350 (a b c d f : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : 2 * d < b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3351 (a b c d f : Nat)
    (q0 : 2 * a ≤ 3 * b + c)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3352 (a b d e f : Nat)
    (q0 : 2 * a ≤ b + e)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : e = 0)
    (q4 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3353 (a b c d f : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3354 (a b d f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3355 (a b d f : Nat)
    (q0 : 2 * a ≤ f)
    (q1 : 2 * d < b + f)
    (q2 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3356 (a b c d f : Nat)
    (q0 : 2 * a ≤ b + c)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3357 (a b d f : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : f < a + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3358 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3359 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ c + f)
    (q2 : f < a + d) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3360 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3361 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3362 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ b + 2 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3363 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b < a + 2 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : f < a + d) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3364 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3365 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ c + f)
    (q2 : f < a + d) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3366 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a ≤ b)
    (q4 : f < a + d) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3367 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3368 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ b + 2 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3369 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a + b < a + 2 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3370 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3371 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ c + f)
    (q2 : f < a + d) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3372 (a b c d f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3373 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3374 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + 2 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3375 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3376 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3377 (a b c d f : Nat)
    (q0 : 2 * a + b < a + 2 * b + c)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3378 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3379 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ c + f)
    (q2 : f < a + d) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3380 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : e = 0)
    (q6 : f < 2 * a + b) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3381 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3382 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3383 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ b + 2 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3384 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + d < a + b + c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : f < a + d) :
    4 * a + d < a + b + c + d ∧ 3 * a + b + c < a + b + c + d ∧ 2 * a + 3 * b < a + b + c + d ∧ 3 * a + f < a + b + c + d ∧ 2 * a + c + d < a + b + c + d ∧ a + 2 * b + d < a + b + c + d ∧ a + b + 2 * c < a + b + c + d ∧ 3 * b + c < a + b + c + d ∧ a + c + f < a + b + c + d ∧ 2 * b + f < a + b + c + d ∧ b + 2 * d < a + b + c + d ∧ 2 * c + d < a + b + c + d ∧ d + g < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3385 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3386 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ c + f)
    (q2 : f < a + d) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3387 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : e = 0)
    (q6 : f < 2 * a + b) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3388 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a ≤ b)
    (q4 : f < a + d) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3389 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3390 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ b + 2 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3391 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a + d < a + b + c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a + d < a + b + c + d ∧ 2 * a + b + c < a + b + c + d ∧ a + 3 * b < a + b + c + d ∧ 2 * a + f < a + b + c + d ∧ a + c + d < a + b + c + d ∧ 2 * b + d < a + b + c + d ∧ b + 2 * c < a + b + c + d ∧ c + f < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3392 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3393 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ c + f)
    (q2 : f < a + d) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3394 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : f < 2 * a + b) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3395 (a b c d f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3396 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3397 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + 2 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3398 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3399 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + d < a + b + c + d := by
  omega

end Max11DegreeRoutes
/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3400 (a b c d f : Nat)
    (q0 : 2 * a + d < a + b + c + d)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + d < a + b + c + d ∧ a + b + c < a + b + c + d ∧ 3 * b < a + b + c + d ∧ a + f < a + b + c + d ∧ c + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3401 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3402 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 5 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < a + d) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3403 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3404 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3405 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ b + 2 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3406 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b + c < 2 * a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : f < a + d) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3407 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3408 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < a + d) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3409 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a ≤ b)
    (q4 : f < a + d) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3410 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3411 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ b + 2 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3412 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a + b + c < 2 * a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3413 (a b c d f g : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : f < a + d) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3414 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 3 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < a + d) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3415 (a b c d f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3416 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3417 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + 2 * c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3418 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3419 (a b c d f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3420 (a b c d f : Nat)
    (q0 : 2 * a + b + c < 2 * a + 4 * b)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < a + d) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3421 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + f < c + d)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3422 (a c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ c + f)
    (q2 : a + f < c + d)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3423 (a c d e g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ d + e)
    (q3 : c + g = a + 2 * d)
    (q4 : e = 0)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3424 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + f < c + d)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3425 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + f < c + d)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3426 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + f < c + d)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3427 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a + d < c + 2 * d)
    (q2 : a + f < c + d)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < c + 2 * d ∧ 3 * a + b + c < c + 2 * d ∧ 2 * a + 3 * b < c + 2 * d ∧ 3 * a + f < c + 2 * d ∧ 2 * a + c + d < c + 2 * d ∧ a + 2 * b + d < c + 2 * d ∧ a + b + 2 * c < c + 2 * d ∧ 3 * b + c < c + 2 * d ∧ a + c + f < c + 2 * d ∧ 2 * b + f < c + 2 * d ∧ b + 2 * d < c + 2 * d ∧ 2 * c + d < c + 2 * d ∧ d + g < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3428 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + f < c + d)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3429 (a c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + f < c + d)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3430 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ d + e)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : e = 0)
    (q6 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3431 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : a + f < c + d)
    (q2 : a ≤ b)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3432 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + f < c + d)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3433 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + f < c + d)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3434 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + d < c + 2 * d)
    (q2 : a + f < c + d)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d ∧ 2 * a + b + c < c + 2 * d ∧ a + 3 * b < c + 2 * d ∧ 2 * a + f < c + 2 * d ∧ a + c + d < c + 2 * d ∧ 2 * b + d < c + 2 * d ∧ b + 2 * c < c + 2 * d ∧ c + f < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3435 (a b c d f g : Nat)
    (q0 : 6 * a ≤ d + g)
    (q1 : b + g = c + f)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3436 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > e)
    (q2 : 6 * a ≤ e + f)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g)
    (q6 : e = 0)
    (q7 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3437 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3438 (a b c d f g : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3439 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > e)
    (q2 : 6 * a ≤ b + c + e)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g)
    (q6 : e = 0)
    (q7 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3440 (a b c d f g : Nat)
    (q0 : 6 * a ≤ b + 2 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3441 (a b c d f g : Nat)
    (q0 : 6 * a ≤ 2 * c + d)
    (q1 : b + g = c + f)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3442 (a b c d f g : Nat)
    (q0 : 6 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3443 (a b c d f g : Nat)
    (q0 : 5 * a < b + 2 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    5 * a < b + 2 * c ∧ 3 * a + c < b + 2 * c ∧ 2 * a + 2 * b < b + 2 * c ∧ a + b + d < b + 2 * c ∧ a + 2 * c < b + 2 * c ∧ 2 * b + c < b + 2 * c ∧ a + g < b + 2 * c ∧ b + f < b + 2 * c ∧ 2 * d < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3444 (a b c d f g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : b + g = c + f)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3445 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ e + f)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g)
    (q6 : e = 0)
    (q7 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3446 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3447 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3448 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ b + c + e)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g)
    (q6 : e = 0)
    (q7 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3449 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3450 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 2 * c + d)
    (q1 : b + g = c + f)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3451 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3452 (a b c d f g : Nat)
    (q0 : 4 * a < b + 2 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a < b + 2 * c ∧ 2 * a + c < b + 2 * c ∧ a + 2 * b < b + 2 * c ∧ b + d < b + 2 * c ∧ 2 * c < b + 2 * c ∧ g < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3453 (a b c d f g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : b + g = c + f)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3454 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ e + f)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g)
    (q6 : e = 0)
    (q7 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3455 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3456 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3457 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ b + c + e)
    (q3 : b + g = c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g)
    (q6 : e = 0)
    (q7 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3458 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3459 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : b + g = c + f)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3460 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3461 (a b c d e f g : Nat)
    (q0 : 3 * a > e)
    (q1 : 4 * a ≤ b + e)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + b + f < c + g)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : e = 0)
    (q7 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3462 (a b c d f g : Nat)
    (q0 : 4 * a ≤ c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3463 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3464 (a b c d f g : Nat)
    (q0 : 3 * a < b + 2 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c ∧ a + c < b + 2 * c ∧ 2 * b < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3465 (a b c d f g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : b + g = c + f)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3466 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : e = 0)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3467 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3468 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3469 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ b + c + e)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : e = 0)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3470 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3471 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : b + g = c + f)
    (q2 : c + d < a + f)
    (q3 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3472 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 3 * b + c)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3473 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ b + e)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : e = 0)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3474 (a b c d f g : Nat)
    (q0 : 3 * a ≤ c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3475 (a b c d f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a + b + f < c + g)
    (q2 : a ≤ b)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3476 (a b c d f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3477 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3478 (a b c d f g : Nat)
    (q0 : 2 * a < b + 2 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c ∧ c < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3479 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3480 (a b c d e f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : e = 0)
    (q5 : g = 2 * c) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3481 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3482 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3483 (a b c d f g : Nat)
    (q0 : 4 * a + b < a + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3484 (a b c d f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3485 (a b c d e f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : e = 0)
    (q5 : g = 2 * c) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3486 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3487 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3488 (a b c d f g : Nat)
    (q0 : 3 * a + b < a + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3489 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3490 (a b c d e f g : Nat)
    (q0 : a + 2 * f < 2 * g)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : e = 0)
    (q5 : g = 2 * c) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3491 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3492 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3493 (a b c d f g : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3494 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3495 (a b c d f g : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3496 (a b c d e f g : Nat)
    (q0 : 3 * a > e)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : e = 0)
    (q7 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3497 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3498 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3499 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + 2 * c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3500 (a b c d f g : Nat)
    (q0 : 4 * a + d < a + b + c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a + d < a + b + c + d ∧ 3 * a + b + c < a + b + c + d ∧ 2 * a + 3 * b < a + b + c + d ∧ 3 * a + f < a + b + c + d ∧ 2 * a + c + d < a + b + c + d ∧ a + 2 * b + d < a + b + c + d ∧ a + b + 2 * c < a + b + c + d ∧ 3 * b + c < a + b + c + d ∧ a + c + f < a + b + c + d ∧ 2 * b + f < a + b + c + d ∧ b + 2 * d < a + b + c + d ∧ 2 * c + d < a + b + c + d ∧ d + g < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3501 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3502 (a b c d f g : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3503 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ d + e)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : e = 0)
    (q6 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3504 (a b c d f g : Nat)
    (q0 : a + b + f < c + g)
    (q1 : a ≤ b)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3505 (a b c d f g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3506 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + 2 * c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3507 (a b c d f g : Nat)
    (q0 : 3 * a + d < a + b + c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    3 * a + d < a + b + c + d ∧ 2 * a + b + c < a + b + c + d ∧ a + 3 * b < a + b + c + d ∧ 2 * a + f < a + b + c + d ∧ a + c + d < a + b + c + d ∧ 2 * b + d < a + b + c + d ∧ b + 2 * c < a + b + c + d ∧ c + f < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3508 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3509 (a b c d f g : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3510 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a ≤ d + e)
    (q2 : b + g = c + f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g)
    (q5 : e = 0)
    (q6 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3511 (a b c d f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : a + b + f < c + g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3512 (a b c d f g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3513 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + 2 * c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : c + d < a + f)
    (q3 : c + g = a + 2 * d)
    (q4 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3514 (a b c d f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3515 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3516 (a b c d f g : Nat)
    (q0 : 2 * a + d < a + b + c + d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + d < a + b + c + d ∧ a + b + c < a + b + c + d ∧ 3 * b < a + b + c + d ∧ a + f < a + b + c + d ∧ c + d < a + b + c + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3517 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3518 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3519 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3520 (a b c d f g : Nat)
    (q0 : 4 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    4 * a + b + c < a + c + 2 * d ∧ 3 * a + 3 * b < a + c + 2 * d ∧ 4 * a + f < a + c + 2 * d ∧ 3 * a + c + d < a + c + 2 * d ∧ 2 * a + 2 * b + d < a + c + 2 * d ∧ 2 * a + b + 2 * c < a + c + 2 * d ∧ a + 3 * b + c < a + c + 2 * d ∧ 5 * b < a + c + 2 * d ∧ 2 * a + c + f < a + c + 2 * d ∧ a + 2 * b + f < a + c + 2 * d ∧ a + b + 2 * d < a + c + 2 * d ∧ a + 2 * c + d < a + c + 2 * d ∧ 2 * b + c + d < a + c + 2 * d ∧ b + 3 * c < a + c + 2 * d ∧ b + c + g < a + c + 2 * d ∧ b + d + f < a + c + 2 * d ∧ 2 * c + f < a + c + 2 * d ∧ 3 * d < a + c + 2 * d ∧ f + g < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3521 (a b c d f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3522 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3523 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3524 (a b c d f g : Nat)
    (q0 : 3 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    3 * a + b + c < a + c + 2 * d ∧ 2 * a + 3 * b < a + c + 2 * d ∧ 3 * a + f < a + c + 2 * d ∧ 2 * a + c + d < a + c + 2 * d ∧ a + 2 * b + d < a + c + 2 * d ∧ a + b + 2 * c < a + c + 2 * d ∧ 3 * b + c < a + c + 2 * d ∧ a + c + f < a + c + 2 * d ∧ 2 * b + f < a + c + 2 * d ∧ b + 2 * d < a + c + 2 * d ∧ 2 * c + d < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3525 (a b c d f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3526 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3527 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + d < a + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3528 (a b c d f g : Nat)
    (q0 : 2 * a + b + c < a + c + 2 * d)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + d < a + f)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    2 * a + b + c < a + c + 2 * d ∧ a + 3 * b < a + c + 2 * d ∧ 2 * a + f < a + c + 2 * d ∧ a + c + d < a + c + 2 * d ∧ 2 * b + d < a + c + 2 * d ∧ b + 2 * c < a + c + 2 * d ∧ c + f < a + c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3529 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a > 2 * d)
    (q4 : 6 * a ≤ d + g)
    (q5 : a + 2 * f = 2 * g)
    (q6 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3530 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 6 * a ≤ e + f)
    (q4 : a + 2 * f = 2 * g) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3531 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a > 2 * d)
    (q4 : 5 * a ≤ 2 * b + d)
    (q5 : a + 2 * f = 2 * g)
    (q6 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3532 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 6 * a ≤ 2 * b + f)
    (q3 : a + 2 * f = 2 * g) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3533 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 6 * a ≤ b + c + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3534 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a > 2 * d)
    (q4 : 6 * a ≤ b + 2 * d)
    (q5 : a + 2 * f = 2 * g)
    (q6 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3535 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a > 2 * d)
    (q4 : 6 * a ≤ 2 * c + d)
    (q5 : a + 2 * b = 2 * c)
    (q6 : a + 2 * f = 2 * g)
    (q7 : d = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3536 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 6 * a ≤ 3 * b + c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3537 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a < a + 3 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3538 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a > 2 * d)
    (q4 : 5 * a ≤ d + g)
    (q5 : a + 2 * f = 2 * g)
    (q6 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3539 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a ≤ e + f)
    (q4 : a + 2 * f = 2 * g) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3540 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ 2 * b + d)
    (q4 : 5 * a > 2 * d)
    (q5 : a + 2 * f = 2 * g)
    (q6 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3541 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ 2 * b + f)
    (q3 : a + 2 * f = 2 * g) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3542 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ b + c + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3543 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a ≤ b + 2 * d)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3544 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a > 2 * d)
    (q4 : 5 * a ≤ 2 * c + d)
    (q5 : a + 2 * b = 2 * c)
    (q6 : a + 2 * f = 2 * g)
    (q7 : d = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3545 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a ≤ 3 * b + c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3546 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a < a + 3 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3547 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ d + g)
    (q4 : 5 * a > 2 * d)
    (q5 : a + 2 * f = 2 * g)
    (q6 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3548 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ e + f)
    (q4 : a + 2 * f = 2 * g) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3549 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ 2 * b + d)
    (q4 : 5 * a > 2 * d)
    (q5 : a + 2 * f = 2 * g)
    (q6 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3550 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 4 * a ≤ 2 * b + f)
    (q3 : a + 2 * f = 2 * g) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3551 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 4 * a ≤ b + c + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3552 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ b + 2 * d)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3553 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ 2 * c + d)
    (q4 : 5 * a > 2 * d)
    (q5 : a + 2 * b = 2 * c)
    (q6 : a + 2 * f = 2 * g)
    (q7 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3554 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ 3 * b + c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3555 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ b + e)
    (q4 : a + 2 * f = 2 * g) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3556 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ c + d)
    (q4 : 5 * a > 2 * d)
    (q5 : a + 2 * b = 2 * c)
    (q6 : a + 2 * f = 2 * g)
    (q7 : d = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3557 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ 3 * b)
    (q4 : a + 2 * f = 2 * g) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3558 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a < a + 3 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3559 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ d + g)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3560 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ e + f)
    (q4 : a + 2 * f = 2 * g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3561 (a b d e f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3562 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 3 * a ≤ 2 * b + f)
    (q3 : a + 2 * f = 2 * g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3563 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 3 * a ≤ b + c + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3564 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ b + 2 * d)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3565 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ 2 * c + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : d = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3566 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ 3 * b + c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3567 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ b + e)
    (q4 : a + 2 * f = 2 * g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3568 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ c + d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : d = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3569 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a ≤ b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3570 (a b e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ f)
    (q4 : a + 2 * f = 2 * g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3571 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 3 * a ≤ b + c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3572 (a b c e f g : Nat)
    (q0 : 2 * a < a + 3 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3573 (a b d e f g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3574 (a b e f g : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * f = 2 * g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3575 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a ≤ 2 * b + d)
    (q5 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3576 (a b e f g : Nat)
    (q0 : 2 * a ≤ 2 * b + f)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : a + 2 * f = 2 * g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3577 (a b c e f g : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3578 (a b d e f g : Nat)
    (q0 : 2 * a ≤ b + 2 * d)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3579 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3580 (a b c e f g : Nat)
    (q0 : 2 * a ≤ 3 * b + c)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3581 (a b e f g : Nat)
    (q0 : 2 * a ≤ b + e)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * f = 2 * g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3582 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g)
    (q6 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3583 (a b e f g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * f = 2 * g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3584 (a b e f g : Nat)
    (q0 : 2 * a ≤ f)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : a + 2 * f = 2 * g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3585 (a b c e f g : Nat)
    (q0 : 2 * a ≤ b + c)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3586 (a b d e f g : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f < e + g)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3587 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3588 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 5 * a ≤ c + f)
    (q3 : a + 2 * f = 2 * g) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3589 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f)
    (q7 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3590 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ 3 * b)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3591 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a > 2 * d)
    (q4 : 5 * a ≤ 2 * b + d)
    (q5 : a + 2 * b = 2 * c)
    (q6 : a + 2 * f = 2 * g)
    (q7 : d = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3592 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 5 * a ≤ b + 2 * c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3593 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a + b < a + 2 * b + c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3594 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 4 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3595 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 4 * a ≤ c + f)
    (q3 : a + 2 * f = 2 * g) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3596 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ d + e)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : d = 0)
    (q6 : e + g < 2 * a + b + f)
    (q7 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3597 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + 2 * f = 2 * g)
    (q5 : a ≤ b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3598 (a b c d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ 2 * b + d)
    (q4 : 5 * a > 2 * d)
    (q5 : a + 2 * b = 2 * c)
    (q6 : a + 2 * f = 2 * g)
    (q7 : d = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_3599 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f < e + g)
    (q2 : 2 * f = a + 4 * b)
    (q3 : 4 * a ≤ b + 2 * c)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + 2 * f = 2 * g) :
    3 * a + b < a + 2 * b + c := by
  omega

end Max11DegreeRoutes
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
