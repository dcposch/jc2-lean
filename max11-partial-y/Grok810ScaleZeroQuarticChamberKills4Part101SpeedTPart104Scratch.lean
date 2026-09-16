import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2400 (a b c d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : e < a + c)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2401 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g ∧ 3 * a + d < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : e < a + c)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + b + e < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ d + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2402 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : e < a + c)
    (q5 : g < 2 * a + c) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ b + e < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2403 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b < 2 * c) :
    3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2404 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b < 2 * c) :
    3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2405 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * b < 2 * c) :
    3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2406 (a b c d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d) :
    3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2407 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2408 (a b c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d) :
    3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2409 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 3 * a + b + e < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + d + e < 2 * g ∧ a + b + c + e < 2 * g ∧ a + b + 2 * d < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 3 * b + e < 2 * g ∧ 2 * b + c + d < 2 * g ∧ b + 3 * c < 2 * g ∧ b + c + g < 2 * g ∧ b + 2 * e < 2 * g ∧ c + d + e < 2 * g ∧ 3 * d < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2410 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c) :
    3 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2411 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c) :
    3 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2412 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : a + 2 * b < 2 * c) :
    3 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2413 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d) :
    3 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2414 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : f = 0) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2415 (a b c d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d) :
    3 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2416 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + b + c < 2 * g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d) :
    3 * a + b + c < 2 * g ∧ 2 * a + 3 * b < 2 * g ∧ 2 * a + b + e < 2 * g ∧ 2 * a + c + d < 2 * g ∧ a + 2 * b + d < 2 * g ∧ a + b + 2 * c < 2 * g ∧ 3 * b + c < 2 * g ∧ a + d + e < 2 * g ∧ b + c + e < 2 * g ∧ b + 2 * d < 2 * g ∧ 2 * c + d < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2417 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a ≤ 4 * b) :
    2 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2418 (a b c g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c) :
    2 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2419 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : a + 2 * b < 2 * c) :
    2 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2420 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * e)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d) :
    2 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2421 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : f = 0) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2422 (a b c d g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d) :
    2 * a + b + c < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2423 (a b c d e g : Nat)
    (q0 : 2 * a + b + c < 2 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q5 : c + g = a + 2 * d) :
    2 * a + b + c < 2 * g ∧ a + 3 * b < 2 * g ∧ a + b + e < 2 * g ∧ a + c + d < 2 * g ∧ 2 * b + d < 2 * g ∧ b + 2 * c < 2 * g ∧ d + e < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2424 (a b c d e g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2425 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + g = a + 2 * d)
    (q4 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2426 (a b c d e g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 4 * a + d < e + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * c = 2 * d)
    (q5 : c + g = a + 2 * d) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + d + e < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2427 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2428 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2429 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2430 (a b c d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2431 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2432 (a b c d e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2433 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + d < e + g ∧ 3 * a + b + c < e + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + d + e < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2434 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2435 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2436 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2437 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2438 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : f = 0) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2439 (a b c d e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2440 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + d < e + g ∧ 2 * a + b + c < e + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + b + c < e + g ∧ a + 3 * b < e + g ∧ a + b + e < e + g ∧ a + c + d < e + g ∧ 2 * b + d < e + g ∧ b + 2 * c < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2441 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a ≤ 4 * b)
    (q4 : c + g = 2 * e) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2442 (a c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2443 (a c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2444 (a c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2445 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : f = 0) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2446 (a c d e g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2447 (a b c d e g : Nat)
    (q0 : 2 * a + d < e + g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    2 * a + d < e + g ∧ a + b + c < e + g ∧ 3 * b < e + g ∧ b + e < e + g ∧ c + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2448 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : c + g = 2 * e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2449 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + c = e)
    (q3 : c + g = 2 * e)
    (q4 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2450 (a b c d e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < g)
    (q2 : 4 * a + d < e + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g)
    (q5 : a + c = e)
    (q6 : c + g = 2 * e) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + d + e < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2451 (a b c d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a + c = g)
    (q2 : 2 * c < g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g)
    (q5 : e < a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2452 (a b c d e g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 4 * a + b < c + g ∧ 3 * a + d < c + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g)
    (q5 : e < a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + b + e < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ d + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2453 (a b c d e g : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 2 * g < 3 * a + 2 * d)
    (q2 : 3 * a > 2 * b)
    (q3 : 3 * c < a + 2 * d)
    (q4 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (q5 : 5 * a > 2 * d)
    (q6 : b + c < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2454 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g < a + 4 * d)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 4 * a + d < e + g)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * d = 2 * e)
    (q5 : c + g < a + 2 * d) :
    4 * a + d < e + g ∧ 3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 2 * a + b + e < e + g ∧ 2 * a + c + d < e + g ∧ a + 2 * b + d < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + d + e < e + g ∧ b + c + e < e + g ∧ b + 2 * d < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2455 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g < a + 4 * d)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d)
    (q4 : c + g < a + 2 * d)
    (q5 : e + g < 2 * a + 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2456 (a b c d e g : Nat)
    (q0 : 2 * b < e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e)
    (q3 : 4 * a + b < 2 * e ∧ 3 * a + d < 2 * e)
    (q4 : a + 2 * d < 2 * e)
    (q5 : g < a + e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2457 (a b c d e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e)
    (q5 : c + g < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2458 (a b c d e g : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e)
    (q5 : c + g < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e ∧ 2 * a + 3 * b < 2 * c + e ∧ 2 * a + b + e < 2 * c + e ∧ 2 * a + c + d < 2 * c + e ∧ a + 2 * b + d < 2 * c + e ∧ a + b + 2 * c < 2 * c + e ∧ 3 * b + c < 2 * c + e ∧ a + d + e < 2 * c + e ∧ b + c + e < 2 * c + e ∧ b + 2 * d < 2 * c + e ∧ 2 * c + d < 2 * c + e ∧ d + g < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2459 (a b c d e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e)
    (q5 : c + g < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2460 (a c d e g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * d < 2 * e)
    (q4 : c + g < 2 * e) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2461 (a b c d e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + 2 * d < 2 * e)
    (q4 : a + e = g)
    (q5 : c + g < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2462 (a b c d e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 4 * a + b < 2 * e ∧ 3 * a + d < 2 * e)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + 2 * d < 2 * e)
    (q4 : a + e = g)
    (q5 : c + g < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2463 (a b c d f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2464 (a b c d f g : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2465 (a b c d f g : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2466 (a b c d f g : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ a + d < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2467 (a b c d f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2468 (a b c d f : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2469 (a b c d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2470 (a b c d e f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2471 (a b c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2472 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2473 (a b c d f g : Nat)
    (q0 : 4 * a + d < a + d + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ 2 * b + f < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2474 (a b c d f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2475 (a b c d f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2476 (a b c d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2477 (a b c d e f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2478 (a b c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2479 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2480 (a b c d f : Nat)
    (q0 : 3 * a + d < a + d + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + d + f ∧ 2 * a + b + c < a + d + f ∧ a + 3 * b < a + d + f ∧ 2 * a + f < a + d + f ∧ a + c + d < a + d + f ∧ 2 * b + d < a + d + f ∧ b + 2 * c < a + d + f ∧ c + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2481 (a b c d f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : a ≤ 4 * b)
    (q2 : b + c < f) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2482 (a b c d f : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2483 (a b c d f : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2484 (a b c d e f : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : b + c < f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b)
    (q4 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2485 (a b c d f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2486 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2487 (a b c d f : Nat)
    (q0 : 2 * a + d < a + d + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + d + f ∧ a + b + c < a + d + f ∧ 3 * b < a + d + f ∧ a + f < a + d + f ∧ c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2488 (a b c d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2489 (a b c d f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + c < f)
    (q5 : d < a + b) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2490 (a b c d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2491 (a b c d f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : d < a + b) :
    3 * a + d < 2 * f ∧ 2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ a + c + d < 2 * f ∧ 2 * b + d < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2492 (a b c d f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * b < 2 * f)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2493 (a b c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + 4 * b < 2 * f)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2494 (a b c d f g : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2495 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2496 (a b c d f g : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + d + f < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2497 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2498 (a b c d f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2499 (a b c d f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + d < a + d + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ 2 * b + f < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2500 (a b c d f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b = d)
    (q5 : b + f = 2 * d) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + d + f < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2501 (a b c d f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2502 (a b c d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g)
    (q5 : d < a + b) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2503 (a b c d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g)
    (q5 : d < a + b) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2504 (a b c d f g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g)
    (q5 : d < a + b) :
    2 * a + b < c + g ∧ a + d < c + g ∧ b + c < c + g ∧ f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2505 (a b c f g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < b + g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2506 (a b c f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < b + g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2507 (a b c d f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b = d)
    (q4 : c + f < b + g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2508 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b = d)
    (q5 : c + f < b + g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2509 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : a + b = d)
    (q5 : c + f < b + g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2510 (a b c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : 4 * a + f < 2 * g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : a + b = d) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + 2 * d < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 2 * b + c + d < 2 * g ∧ b + 3 * c < 2 * g ∧ b + c + g < 2 * g ∧ b + d + f < 2 * g ∧ 2 * c + f < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2511 (a b c d f g : Nat)
    (q0 : 4 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g)
    (q5 : d < a + b) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2512 (a b c d f g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : c + f < b + g)
    (q5 : d < a + b) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2513 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : c + f < b + g)
    (q6 : d < a + b) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2514 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : d < a + b) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2515 (a b c d f g : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : 2 * c < a + 2 * b)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : d < a + b) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2516 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2517 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d)
    (q5 : f < 2 * a + b) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2518 (a b c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + f < 2 * g)
    (q3 : 5 * a + 2 * b = 2 * g)
    (q4 : a + 2 * b < g)
    (q5 : d < a + b) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + 2 * d < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 2 * b + c + d < 2 * g ∧ b + 3 * c < 2 * g ∧ b + c + g < 2 * g ∧ b + d + f < 2 * g ∧ 2 * c + f < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2519 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + 2 * f < 4 * c)
    (q5 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2520 (a b c d f g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2521 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f)
    (q5 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2522 (a b c d f g : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f)
    (q5 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2523 (a b c d f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d + g < a + c + f)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2524 (a b c d f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d + g < a + c + f)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2525 (a b c d f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d + g < a + c + f)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2526 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d + g < a + c + f)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2527 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d + g < a + c + f)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2528 (a b c d f g : Nat)
    (q0 : 4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d + g < a + c + f)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2529 (a b c d f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d + g < a + c + f) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2530 (a b c d f g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * d < 2 * c + 2 * f)
    (q4 : b + g < c + f)
    (q5 : d + g < a + c + f)
    (q6 : g < 2 * a + c) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2531 (a b c d f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : d + g < a + c + f) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2532 (a b c d f g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * d < 2 * c + 2 * f)
    (q4 : b + g < c + f)
    (q5 : d + g < a + c + f)
    (q6 : g < 2 * a + c) :
    2 * a + b < c + g ∧ a + d < c + g ∧ b + c < c + g ∧ f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2533 (a c d f g : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * f = 2 * g)
    (q4 : d + g < a + c + f) :
    2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2534 (a b c d f g : Nat)
    (q0 : 2 * a + f < c + g)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + g < c + f)
    (q5 : d + g < a + c + f) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2535 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 2 * g < a + 2 * f)
    (q4 : 4 * c < a + 2 * f)
    (q5 : b + c < f) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2536 (a b c d f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q4 : 4 * c < a + 2 * f)
    (q5 : a + 2 * b < 2 * c)
    (q6 : b + c < f) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2537 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 2 * g < a + 2 * f)
    (q4 : b + c < f) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2538 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 2 * g < a + 2 * f)
    (q4 : b + c < f) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2539 (a b c d f : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : b + c < f) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2540 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : a + 2 * b < 2 * c)
    (q5 : b + c < f)
    (q6 : g < 2 * a + c) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2541 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + b + f < c + g)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2542 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2543 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2544 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + b + f < c + g)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2545 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2546 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2547 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : g < 2 * a + c) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2548 (a b c d f g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : a + b + f < c + g)
    (q5 : g < 2 * a + c) :
    2 * a + b < c + g ∧ a + d < c + g ∧ b + c < c + g ∧ f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2549 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + b + f < c + g) :
    3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g ∧ 4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2550 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * f < 2 * g) :
    3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g ∧ 4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2551 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * b < 2 * c)
    (q4 : d + f < c + g) :
    3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g ∧ 4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2552 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2553 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g ∧ 4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2554 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g ∧ 4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2555 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + c + d < 2 * g ∧ 4 * a + b + c < 2 * g ∧ 4 * a + f < 2 * g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + 2 * d < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 2 * b + c + d < 2 * g ∧ b + 3 * c < 2 * g ∧ b + c + g < 2 * g ∧ b + d + f < 2 * g ∧ 2 * c + f < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2556 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < c + g) :
    3 * a + b + c < 2 * g ∧ 3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2557 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g) :
    3 * a + b + c < 2 * g ∧ 3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2558 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : a + 2 * b < 2 * c)
    (q4 : d + f < c + g) :
    3 * a + b + c < 2 * g ∧ 3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2559 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2560 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    3 * a + b + c < 2 * g ∧ 3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2561 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    3 * a + b + c < 2 * g ∧ 3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2562 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + b + c < 2 * g ∧ 3 * a + f < 2 * g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d) :
    3 * a + b + c < 2 * g ∧ 2 * a + 3 * b < 2 * g ∧ 3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g ∧ a + 2 * b + d < 2 * g ∧ a + b + 2 * c < 2 * g ∧ 3 * b + c < 2 * g ∧ a + c + f < 2 * g ∧ 2 * b + f < 2 * g ∧ b + 2 * d < 2 * g ∧ 2 * c + d < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2563 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : a ≤ 4 * b) :
    2 * a + b + c < 2 * g ∧ 2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2564 (a b c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g) :
    2 * a + b + c < 2 * g ∧ 2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2565 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : a + 2 * b < 2 * c)
    (q4 : d + f < c + g) :
    2 * a + b + c < 2 * g ∧ 2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2566 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2567 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 9 * a ≤ 4 * f)
    (q3 : a + b + f < c + g)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    2 * a + b + c < 2 * g ∧ 2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2568 (a b c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    2 * a + b + c < 2 * g ∧ 2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2569 (a b c d f g : Nat)
    (q0 : 2 * a + b + c < 2 * g ∧ 2 * a + f < 2 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    2 * a + b + c < 2 * g ∧ a + 3 * b < 2 * g ∧ 2 * a + f < 2 * g ∧ a + c + d < 2 * g ∧ 2 * b + d < 2 * g ∧ b + 2 * c < 2 * g ∧ c + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2570 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * c = 2 * d)
    (q4 : d + f < c + g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2571 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + g = a + 2 * d)
    (q4 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2572 (a b c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < g)
    (q2 : 4 * a + f < 2 * g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * c = 2 * d)
    (q5 : c + g = a + 2 * d) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + 2 * d < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 2 * b + c + d < 2 * g ∧ b + 3 * c < 2 * g ∧ b + c + g < 2 * g ∧ b + d + f < 2 * g ∧ 2 * c + f < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2573 (a b c d f g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g)
    (q5 : a + b + f < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2574 (a b c d f g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g)
    (q5 : a + 2 * f < 2 * g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2575 (a b c d f g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g)
    (q5 : a + 2 * f < 2 * g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2576 (a b c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a + c = g)
    (q2 : 2 * c < g)
    (q3 : a + 2 * d < c + g)
    (q4 : a + 2 * f < 2 * g)
    (q5 : a + b + f < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2577 (a b c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + c = g)
    (q2 : 2 * c < g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g)
    (q5 : a + 2 * f < 2 * g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2578 (a b c d f g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + f < c + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2579 (a b c d f g : Nat)
    (q0 : 2 * g < 3 * a + 2 * d)
    (q1 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q2 : 3 * a > 2 * b)
    (q3 : 3 * c < a + 2 * d)
    (q4 : 4 * b < a + 2 * d)
    (q5 : 5 * a > 2 * d)
    (q6 : b + c < a + d)
    (q7 : f < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2580 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g < a + 4 * d)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d)
    (q4 : c + g < a + 2 * d)
    (q5 : f < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2581 (a b c d f g : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 3 * a + 2 * c < 2 * f)
    (q3 : 3 * a + f < 2 * f)
    (q4 : 7 * a > 2 * f)
    (q5 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2582 (a b c d f g : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + c + g < 2 * f)
    (q5 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2583 (a b c d f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + c < g)
    (q2 : 3 * a + 2 * d < 2 * g)
    (q3 : 4 * a + f < 2 * g)
    (q4 : 4 * a > g)
    (q5 : 5 * a + 2 * b < 2 * g) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + 2 * d < 2 * g ∧ a + 2 * c + d < 2 * g ∧ 2 * b + c + d < 2 * g ∧ b + 3 * c < 2 * g ∧ b + c + g < 2 * g ∧ b + d + f < 2 * g ∧ 2 * c + f < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2584 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2585 (a b c e f g : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : e + g < 2 * a + b + f)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2586 (a b c e f g : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : c + g < a + b + f)
    (q4 : e + g < 2 * a + b + f)
    (q5 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2587 (a b c e f g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2588 (a b c e f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2589 (a b c d e f g : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : b + c < f)
    (q4 : d = 0)
    (q5 : e + g < 2 * a + b + f) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2590 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2591 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2592 (a b c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2593 (a b c e f g : Nat)
    (q0 : 3 * a + f < e + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2594 (a b c e f g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2595 (a b c e f g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2596 (a b c d e f g : Nat)
    (q0 : a + 2 * b = 2 * c)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + b + f = 2 * e)
    (q3 : b + c < f)
    (q4 : d = 0)
    (q5 : e + g < 2 * a + b + f) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2597 (a b c e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2598 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2599 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + f < e + g := by
  omega

end Max11DegreeRoutes
/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2600 (a b c e f g : Nat)
    (q0 : 2 * a + f < e + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < e + g ∧ a + 3 * b < e + g ∧ 2 * a + f < e + g ∧ a + b + e < e + g ∧ b + 2 * c < e + g ∧ c + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2601 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : e + g < 2 * a + b + f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2602 (a b c e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2603 (a b c e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + c < f)
    (q4 : e + g < 2 * a + b + f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2604 (a b c e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + c < f)
    (q5 : e + g < 2 * a + b + f) :
    2 * a + b + c < 2 * f ∧ a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ a + b + e < 2 * f ∧ b + 2 * c < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2605 (a b c e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * b < 2 * f)
    (q4 : c + g < a + b + f)
    (q5 : e + g < 2 * a + b + f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2606 (a b c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + 4 * b < 2 * f)
    (q5 : c + g < a + b + f)
    (q6 : e + g < 2 * a + b + f) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2607 (a b c e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : c + g < a + b + f)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2608 (a b c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : c + g < a + b + f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2609 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : a + b + f = 2 * e)
    (q4 : b + c < f)
    (q5 : c + g < a + b + f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2610 (a b c e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + c < f)
    (q5 : c + g < a + b + f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2611 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * a + f < a + 2 * f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : a + b + f = 2 * e) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + c + e < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + c + g < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2612 (a b c e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < a + b + f)
    (q3 : 2 * g < a + 2 * f)
    (q4 : 4 * a + b < a + b + f)
    (q5 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ b + g < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2613 (a b c e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a + b < c + g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2614 (a b c e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a + b < c + g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ b + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2615 (a b c e f g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2616 (a b c e f g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2617 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2618 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2619 (a b c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2620 (a b c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 3 * a + f < e + g)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : a + 2 * b = 2 * c) :
    3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2621 (a b c e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 4 * a + b < c + g)
    (q2 : 5 * a + 2 * b = 2 * g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2622 (a b c e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 3 * a + b < c + g)
    (q2 : 5 * a + 2 * b = 2 * g)
    (q3 : a + 2 * b < g)
    (q4 : a + 2 * b = 2 * c)
    (q5 : c + f < b + g) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ b + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2623 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 4 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : e + f < a + b + g) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2624 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : e + f < a + b + g) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2625 (a b c e f g : Nat)
    (q0 : 2 * a + b < 2 * e)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : e + f < a + b + g) :
    2 * a + b < 2 * e ∧ b + c < 2 * e ∧ f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2626 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 4 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : e + f < a + b + g) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2627 (a b c e f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + 2 * b + 2 * g = 4 * e)
    (q4 : a + 2 * b < g)
    (q5 : e + f < a + b + g) :
    3 * a + b < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2628 (a b c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : 4 * a + f < 2 * g)
    (q4 : 5 * a + 2 * b = 2 * g)
    (q5 : a + 2 * b < g) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + b + e < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + c + e < 2 * g ∧ 3 * b + e < 2 * g ∧ b + 3 * c < 2 * g ∧ a + e + f < 2 * g ∧ b + c + g < 2 * g ∧ b + 2 * e < 2 * g ∧ 2 * c + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2629 (a b c e f g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c)
    (q4 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2630 (a b c e f g : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + b < 3 * c ∧ 2 * a + f < 3 * c)
    (q3 : a + 2 * f = 4 * c)
    (q4 : b + c < f)
    (q5 : e < a + c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2631 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : e < a + c)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2632 (a b c e f g : Nat)
    (q0 : 4 * a + b < c + g ∧ 2 * a + f < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : e < a + c)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2633 (a b c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : e < a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2634 (a b c e f g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : e < a + c)
    (q5 : g < 2 * a + c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ b + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2635 (a b c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * f = 2 * g)
    (q3 : b + g < c + f)
    (q4 : e < a + c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2636 (a c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : e < a + c) :
    2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2637 (a b c e f g : Nat)
    (q0 : 2 * a + f < c + g)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : b + g < c + f)
    (q5 : e < a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2638 (a b c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : b + c < f)
    (q5 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2639 (a b c e f g : Nat)
    (q0 : 2 * g < a + 2 * f)
    (q1 : 4 * a + b < 2 * e ∧ 2 * a + f < 2 * e)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : b + c < f)
    (q5 : e < a + c) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2640 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2641 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2642 (a b c e f : Nat)
    (q0 : 2 * a + b < 2 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : b + c < f)
    (q4 : e < a + c) :
    2 * a + b < 2 * e ∧ b + c < 2 * e ∧ f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2643 (a b c e f g : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : a + c = e)
    (q5 : b + c < f)
    (q6 : g < 2 * a + c) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2644 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : e < a + c)
    (q5 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2645 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g ∧ 2 * a + f < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2646 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : e < a + c)
    (q5 : g < 2 * a + c) :
    3 * a + b < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ a + f < c + g ∧ b + e < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2647 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + b + c < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2648 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + b + c < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2649 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2650 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + b + c < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2651 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + b + f < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + b + c < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2652 (a b c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + b + c < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2653 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b + c < e + g ∧ 3 * a + f < e + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2654 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    2 * a + b + c < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2655 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    2 * a + b + c < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2656 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2657 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    2 * a + b + c < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2658 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + b + f < c + g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    2 * a + b + c < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2659 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    2 * a + b + c < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2660 (a b c e f g : Nat)
    (q0 : 2 * a + b + c < e + g ∧ 2 * a + f < e + g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    2 * a + b + c < e + g ∧ a + 3 * b < e + g ∧ 2 * a + f < e + g ∧ a + b + e < e + g ∧ b + 2 * c < e + g ∧ c + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2661 (a b c e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + b + f < c + g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2662 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + c = e)
    (q3 : c + g = 2 * e)
    (q4 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2663 (a b c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < g)
    (q2 : 3 * a + f < e + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    3 * a + b + c < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ a + b + 2 * c < e + g ∧ 3 * b + c < e + g ∧ a + c + f < e + g ∧ 2 * b + f < e + g ∧ b + c + e < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2664 (a b c e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a + c = g)
    (q2 : 2 * c < g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * f < 2 * g)
    (q5 : e < a + c) :
    4 * a + b < c + g ∧ 2 * a + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2665 (a b c e f g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 4 * a + b < c + g ∧ 2 * a + f < c + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : e < a + c) :
    4 * a + b < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ 2 * a + f < c + g ∧ a + b + e < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g ∧ c + f < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2666 (a b c e f g : Nat)
    (q0 : 2 * b < e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e)
    (q3 : 4 * a + b < 2 * e ∧ 2 * a + f < 2 * e)
    (q4 : g < a + e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2667 (a b c e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * c + 2 * f < 4 * e)
    (q5 : c + g < 2 * e) :
    3 * a + b + c < 2 * c + e ∧ 3 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2668 (a b c e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * c + 2 * f < 4 * e)
    (q5 : c + g < 2 * e) :
    2 * a + b + c < 2 * c + e ∧ 2 * a + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2669 (a b c e f g : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + b + f < 2 * e)
    (q4 : a + e = g)
    (q5 : c + g < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2670 (a b c e f g : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * c + 2 * f < 4 * e)
    (q3 : a + 2 * e = 2 * f)
    (q4 : a + b + f < 2 * e)
    (q5 : g < a + e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2671 (a b c e f g : Nat)
    (q0 : 2 * f < a + 2 * e)
    (q1 : 3 * a > e)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b + 2 * g < 4 * e)
    (q4 : a + e = g)
    (q5 : c + g < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2672 (a b c e f g : Nat)
    (q0 : 3 * a > e)
    (q1 : 4 * a + b < 2 * e ∧ 2 * a + f < 2 * e)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g)
    (q4 : c + g < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ b + 2 * c < 2 * e ∧ b + g < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2673 (a b c e f g : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + c + g < 2 * f)
    (q5 : e + g < 2 * f) :
    3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + c + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2674 (a b c e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + c < g)
    (q2 : 4 * a + f < 2 * g)
    (q3 : 4 * a > g)
    (q4 : 5 * a + 2 * b < 2 * g)
    (q5 : a + e < g) :
    4 * a + b + c < 2 * g ∧ 3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + b + e < 2 * g ∧ 2 * a + b + 2 * c < 2 * g ∧ a + 3 * b + c < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + c + f < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + c + e < 2 * g ∧ 3 * b + e < 2 * g ∧ b + 3 * c < 2 * g ∧ a + e + f < 2 * g ∧ b + c + g < 2 * g ∧ b + 2 * e < 2 * g ∧ 2 * c + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2675 (a b d e f g : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : d < a + b)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ 2 * b + d < a + b + f ∧ b + g < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2676 (a b d e f g : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : d < a + b)
    (q4 : e + g < 2 * a + b + f)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ 2 * b + d < a + b + f ∧ b + g < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2677 (a b d e f g : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : d < a + b)
    (q4 : e + g < 2 * a + b + f)
    (q5 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2678 (a b d e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * b < 2 * f)
    (q4 : d < a + b)
    (q5 : e + g < 2 * a + b + f) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ 2 * b + d < a + b + f ∧ b + g < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2679 (a b d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + 4 * b < 2 * f)
    (q5 : d < a + b)
    (q6 : e + g < 2 * a + b + f) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2680 (a b d e f g : Nat)
    (q0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + d < a + d + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    4 * a + d < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + b + e < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + d + e < a + d + f ∧ 2 * b + f < a + d + f ∧ b + 2 * d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2681 (a b d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + b = d)
    (q3 : b + e < a + f)
    (q4 : b + f = 2 * d)
    (q5 : e + g < 2 * a + b + f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2682 (a b d e f g : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + b = d)
    (q3 : b + e < a + f)
    (q4 : b + f = 2 * d)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2683 (a b d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + b = d)
    (q3 : b + e < a + f)
    (q4 : b + f = 2 * d)
    (q5 : e + g < 2 * a + b + f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2684 (a b d e f g : Nat)
    (q0 : 2 * d + 2 * e < a + 2 * b + 2 * f)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b = d)
    (q5 : b + f = 2 * d) :
    3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2685 (a b c d e f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : c = 0) :
    ¬ (7 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2686 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b + f = 2 * e)
    (q5 : d < a + b) :
    3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2687 (a b c d e f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : c = 0) :
    ¬ (5 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2688 (a b c d e f : Nat)
    (q0 : 2 * d < b + f)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b + f = 2 * e)
    (q4 : c = 0) :
    ¬ (3 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2689 (a b d e f g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + b + f = 2 * e)
    (q3 : b + e < a + f)
    (q4 : d < a + b)
    (q5 : e + g < 2 * a + b + f) :
    4 * a + d < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + d + e < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2690 (a b d e f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ 2 * b + d < a + b + f ∧ b + g < a + b + f ∧ d + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2691 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : d + e < b + g)
    (q5 : d < a + b) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2692 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : d + e < b + g)
    (q5 : d < a + b) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ b + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2693 (a b d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d)
    (q4 : b + g = d + e)
    (q5 : e + f < a + b + g) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2694 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + d < e + g)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d)
    (q4 : b + g = d + e)
    (q5 : e + f < a + b + g) :
    4 * a + d < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ a + 2 * b + d < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + 2 * d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2695 (a b d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d)
    (q4 : b + g = d + e)
    (q5 : e + f < a + b + g) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2696 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + d < e + g)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d)
    (q4 : b + g = d + e)
    (q5 : e + f < a + b + g) :
    3 * a + d < e + g ∧ a + 3 * b < e + g ∧ 2 * a + f < e + g ∧ a + b + e < e + g ∧ 2 * b + d < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2697 (a b d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : b + g = d + e)
    (q5 : d < a + b) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2698 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + d < e + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : b + g = d + e)
    (q5 : d < a + b) :
    4 * a + d < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ a + 2 * b + d < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + 2 * d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2699 (a b d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : b + g = d + e)
    (q5 : d < a + b) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2700 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + d < e + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : b + g = d + e)
    (q5 : d < a + b) :
    3 * a + d < e + g ∧ a + 3 * b < e + g ∧ 2 * a + f < e + g ∧ a + b + e < e + g ∧ 2 * b + d < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2701 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : b + g = d + e)
    (q5 : d < a + b) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2702 (a b d e f g : Nat)
    (q0 : 2 * a + d < e + g)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : b + g = d + e)
    (q5 : d < a + b) :
    2 * a + d < e + g ∧ 3 * b < e + g ∧ a + f < e + g ∧ b + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2703 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d)
    (q4 : d + e < b + g)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2704 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : a + 2 * b < g)
    (q3 : a + b = d)
    (q4 : d + e < b + g)
    (q5 : f < 2 * a + b) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ b + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2705 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 4 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : d + e < b + g)
    (q5 : e + f < a + b + g) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ 2 * b + d < 2 * e ∧ b + g < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2706 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 3 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : d + e < b + g)
    (q5 : e + f < a + b + g) :
    3 * a + b < 2 * e ∧ 2 * a + d < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2707 (a b d e f g : Nat)
    (q0 : 2 * a + b < 2 * e)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : d + e < b + g)
    (q4 : e + f < a + b + g) :
    2 * a + b < 2 * e ∧ a + d < 2 * e ∧ f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2708 (a b d e f g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 4 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : d + e < b + g)
    (q5 : e + f < a + b + g) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ 2 * b + d < 2 * e ∧ b + g < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2709 (a b d e f g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g)
    (q4 : d + e < b + g)
    (q5 : e + f < a + b + g) :
    3 * a + b < 2 * e ∧ 2 * a + d < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2710 (a b d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 4 * a + f < 2 * g)
    (q3 : 5 * a + 2 * b = 2 * g)
    (q4 : a + 2 * b < g)
    (q5 : d < a + b) :
    3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + b + e < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + d + e < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + 2 * d < 2 * g ∧ 3 * b + e < 2 * g ∧ a + e + f < 2 * g ∧ b + d + f < 2 * g ∧ b + 2 * e < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2711 (a b d e f g : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 2 * g < 3 * a + 2 * d)
    (q2 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q3 : 3 * a > 2 * b)
    (q4 : 4 * b < a + 2 * d)
    (q5 : 5 * a > 2 * d)
    (q6 : f < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2712 (a b d e f g : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f)
    (q4 : b + f < 2 * d)
    (q5 : e + g < 2 * a + 2 * d) :
    3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + b + e < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ 3 * b + e < a + 2 * f ∧ a + e + f < a + 2 * f ∧ b + d + f < a + 2 * f ∧ b + 2 * e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2713 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g < a + 4 * d)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 4 * a + d < e + g)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * d = 2 * e)
    (q5 : f < a + d) :
    4 * a + d < e + g ∧ 2 * a + 3 * b < e + g ∧ 3 * a + f < e + g ∧ 2 * a + b + e < e + g ∧ a + 2 * b + d < e + g ∧ a + d + e < e + g ∧ 2 * b + f < e + g ∧ b + 2 * d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2714 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g < a + 4 * d)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d)
    (q4 : e + g < 2 * a + 2 * d)
    (q5 : f < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + b + e < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + g < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2715 (a b d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * b < e)
    (q2 : 2 * f < a + 2 * e)
    (q3 : 3 * a > e)
    (q4 : a + 2 * d < 2 * e)
    (q5 : g < a + e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2716 (a b d e f g : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e)
    (q3 : a + 2 * d < 2 * e)
    (q4 : g < a + e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ 2 * b + d < 2 * e ∧ b + g < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2717 (a b d e f g : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + b + f < 2 * e)
    (q4 : a + e = g)
    (q5 : d + f < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ 2 * b + d < 2 * e ∧ b + g < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2718 (a b d e f g : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + b + f < 2 * e)
    (q4 : d + f < 2 * e)
    (q5 : g < a + e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ 2 * b + d < 2 * e ∧ b + g < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2719 (a b d e f g : Nat)
    (q0 : 3 * a > e)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + 2 * d < 2 * e)
    (q4 : a + b + f < 2 * e)
    (q5 : a + e = g) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2720 (a b d e f g : Nat)
    (q0 : 3 * a > e)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + 2 * d < 2 * e)
    (q4 : a + e = g)
    (q5 : d + f < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2721 (a b d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * b + 2 * g < 4 * e)
    (q4 : a + 2 * d < 2 * e)
    (q5 : a + e = g) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2722 (a b d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * b + 2 * g < 4 * e)
    (q4 : a + 2 * d < 2 * e)
    (q5 : a + e = g) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2723 (a b d e f g : Nat)
    (q0 : 3 * a > e)
    (q1 : 4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + f < 2 * e)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + 2 * d < 2 * e)
    (q4 : a + e = g) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e ∧ 2 * b + d < 2 * e ∧ b + g < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2724 (a b d e f g : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 7 * a > 2 * f)
    (q4 : a + 2 * e < 2 * f)
    (q5 : a + d < f) :
    4 * a + d < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + d + e < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2725 (a b d e f g : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * f = 2 * g)
    (q4 : a + d < f)
    (q5 : e + g < 2 * f) :
    4 * a + d < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + d + e < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2726 (a b d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d < 2 * g)
    (q2 : 4 * a + f < 2 * g)
    (q3 : 4 * a > g)
    (q4 : 5 * a + 2 * b < 2 * g)
    (q5 : a + e < g) :
    3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 3 * a + b + e < 2 * g ∧ 2 * a + 2 * b + d < 2 * g ∧ 5 * b < 2 * g ∧ 2 * a + d + e < 2 * g ∧ a + 2 * b + f < 2 * g ∧ a + b + 2 * d < 2 * g ∧ 3 * b + e < 2 * g ∧ a + e + f < 2 * g ∧ b + d + f < 2 * g ∧ b + 2 * e < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2727 (a c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + d < a + f)
    (q4 : d + g < a + c + f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2728 (a c d e f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + d < a + f)
    (q4 : c + f = d + e)
    (q5 : d + g < a + c + f) :
    4 * a + f < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ a + e + f < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2729 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : a + 2 * c = 2 * d)
    (q3 : c + d < a + f)
    (q4 : d + g < a + c + f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2730 (a c d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : c + f = d + e)
    (q5 : e < a + c) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2731 (a c d e f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + d < a + d + f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : c + f = d + e)
    (q5 : e < a + c) :
    4 * a + d < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + c + f < a + d + f ∧ a + d + e < a + d + f ∧ 2 * c + d < a + d + f ∧ d + g < a + d + f ∧ e + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2732 (a c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : c + f = d + e)
    (q5 : e < a + c) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2733 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * g < a + 2 * f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : c + f = d + e)
    (q5 : e < a + c) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2734 (a c d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2735 (a c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * c + 2 * f = 4 * e)
    (q4 : d + e < c + f)
    (q5 : e < a + c) :
    2 * a + d < 2 * e ∧ a + f < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2736 (a c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : e < a + c)
    (q5 : g < 2 * a + c) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ a + d + e < 2 * f ∧ 2 * c + d < 2 * f ∧ d + g < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2737 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    ¬ (5 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2738 (a c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * f < 2 * g) :
    3 * a + c + d < 2 * g ∧ 4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2739 (a c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : d + f < c + g) :
    3 * a + c + d < 2 * g ∧ 4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2740 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    3 * a + c + d < 2 * g ∧ 4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2741 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    3 * a + c + d < 2 * g ∧ 4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2742 (a c d f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    3 * a + c + d < 2 * g ∧ 4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2743 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + c + d < 2 * g ∧ 4 * a + f < 2 * g)
    (q3 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q4 : c + g = a + 2 * d) :
    4 * a + f < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + c + f < 2 * g ∧ 2 * a + d + e < 2 * g ∧ a + 2 * c + d < 2 * g ∧ a + e + f < 2 * g ∧ 2 * c + f < 2 * g ∧ c + d + e < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2744 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    ¬ (3 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2745 (a c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * f < 2 * g) :
    3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2746 (a c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : d + f < c + g) :
    3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2747 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2748 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2749 (a c d f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2750 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g)
    (q3 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q4 : c + g = a + 2 * d) :
    3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g ∧ a + c + f < 2 * g ∧ a + d + e < 2 * g ∧ 2 * c + d < 2 * g ∧ e + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2751 (a b c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : b = 0)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    ¬ (a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2752 (a c f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 2 * f < 2 * g) :
    2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2753 (a c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : d + f < c + g) :
    2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2754 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * e)
    (q3 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2755 (a c d f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 9 * a ≤ 4 * f)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2756 (a c d f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : c + g = a + 2 * d)
    (q4 : d + f < c + g) :
    2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2757 (a c d e f g : Nat)
    (q0 : 2 * a + f < 2 * g)
    (q1 : 2 * c < g)
    (q2 : 2 * d < a + 2 * c)
    (q3 : a + 2 * d + 2 * e < 2 * c + 2 * g)
    (q4 : c + g = a + 2 * d) :
    2 * a + f < 2 * g ∧ a + c + d < 2 * g ∧ c + f < 2 * g ∧ d + e < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2758 (a c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q2 : 2 * c < g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2759 (a c d e f g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 4 * a + d < e + g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    4 * a + d < e + g ∧ 3 * a + f < e + g ∧ 2 * a + c + d < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2760 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q2 : 2 * c < g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2761 (a c d e f g : Nat)
    (q0 : 2 * c + 2 * g = a + 2 * d + 2 * e)
    (q1 : 2 * c < g)
    (q2 : 3 * a + d < e + g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g) :
    3 * a + d < e + g ∧ 2 * a + f < e + g ∧ a + c + d < e + g ∧ c + f < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2762 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * c = 2 * d)
    (q3 : d + f < c + g)
    (q4 : e < a + c) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2763 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < g)
    (q2 : 4 * a + f < 2 * g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d)
    (q5 : e < a + c) :
    4 * a + f < 2 * g ∧ 3 * a + c + d < 2 * g ∧ 2 * a + c + f < 2 * g ∧ 2 * a + d + e < 2 * g ∧ a + 2 * c + d < 2 * g ∧ a + e + f < 2 * g ∧ 2 * c + f < 2 * g ∧ c + d + e < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2764 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * c = 2 * d)
    (q3 : d + f < c + g)
    (q4 : e < a + c) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2765 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < g)
    (q2 : 3 * a + f < 2 * g)
    (q3 : a + 2 * c = 2 * d)
    (q4 : c + g = a + 2 * d)
    (q5 : d + f < c + g)
    (q6 : e < a + c) :
    3 * a + f < 2 * g ∧ 2 * a + c + d < 2 * g ∧ a + c + f < 2 * g ∧ a + d + e < 2 * g ∧ 2 * c + d < 2 * g ∧ e + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2766 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * d < c + g)
    (q2 : b = 0)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    ¬ (5 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2767 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2768 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2769 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2770 (a c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2771 (a c d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2772 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + d < e + g ∧ 3 * a + f < e + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    4 * a + d < e + g ∧ 3 * a + f < e + g ∧ 2 * a + c + d < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2773 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * d < c + g)
    (q2 : b = 0)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    ¬ (3 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2774 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2775 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2776 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2777 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2778 (a c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2779 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + d < e + g ∧ 2 * a + f < e + g)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c) :
    3 * a + d < e + g ∧ 2 * a + f < e + g ∧ a + c + d < e + g ∧ c + f < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2780 (a b c d e g : Nat)
    (q0 : 2 * c < g)
    (q1 : a + 2 * d < c + g)
    (q2 : b = 0)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    ¬ (a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2781 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : c + g = 2 * e)
    (q5 : e < a + c) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2782 (a c d e f g : Nat)
    (q0 : 2 * a + d < e + g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c) :
    2 * a + d < e + g ∧ a + f < e + g ∧ c + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2783 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2784 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2785 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2786 (a c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2787 (a c d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    4 * a + d < e + g ∧ 3 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2788 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + d < e + g ∧ 3 * a + f < e + g)
    (q2 : a + c = e)
    (q3 : c + g = 2 * e) :
    4 * a + d < e + g ∧ 3 * a + f < e + g ∧ 2 * a + c + d < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2789 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    3 * a + d < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2790 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    3 * a + d < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2791 (a c d e f g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    3 * a + d < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2792 (a c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    3 * a + d < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2793 (a c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    3 * a + d < e + g ∧ 2 * a + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2794 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + d < e + g ∧ 2 * a + f < e + g)
    (q2 : a + 2 * d < c + g)
    (q3 : a + 2 * f < 2 * g)
    (q4 : a + c = e)
    (q5 : c + g = 2 * e) :
    3 * a + d < e + g ∧ 2 * a + f < e + g ∧ a + c + d < e + g ∧ c + f < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2795 (a c d e f g : Nat)
    (q0 : 2 * c + 2 * f < a + 4 * d)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e)
    (q4 : a + d = f)
    (q5 : e + g < 2 * a + 2 * d) :
    4 * a + f < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ a + e + f < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ c + d + e < a + 2 * f ∧ 3 * d < a + 2 * f ∧ f + g < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2796 (a c d e f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 4 * a + d < e + g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e)
    (q4 : c + g < a + 2 * d)
    (q5 : f < a + d) :
    4 * a + d < e + g ∧ 3 * a + f < e + g ∧ 2 * a + c + d < e + g ∧ a + c + f < e + g ∧ a + d + e < e + g ∧ 2 * c + d < e + g ∧ d + g < e + g ∧ e + f < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2797 (a c d e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < e + g)
    (q3 : a + 2 * d = 2 * e)
    (q4 : c + g < a + 2 * d)
    (q5 : f < a + d) :
    3 * a + d < e + g ∧ 2 * a + f < e + g ∧ a + c + d < e + g ∧ c + f < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2798 (a c d e f g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : c + g < a + 2 * d)
    (q4 : e + g < 2 * a + 2 * d)
    (q5 : f < a + d) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_2799 (a d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * d < 2 * e)
    (q4 : g < a + e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e := by
  omega

end Max11DegreeRoutes
