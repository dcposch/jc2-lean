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
