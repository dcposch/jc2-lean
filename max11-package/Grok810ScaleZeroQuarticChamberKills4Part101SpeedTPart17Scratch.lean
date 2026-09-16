import Lean.Elab.Tactic.Omega

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
