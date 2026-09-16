import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0400 (a b c : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : a ≤ 4 * b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0401 (a b c : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * c) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0402 (a b c d : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0403 (a e : Nat)
    (q0 : 0 < a)
    (q1 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0404 (a f : Nat)
    (q0 : 0 < a)
    (q1 : f = 0) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0405 (a b c g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : 2 * c < a + 2 * b)
    (q3 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0406 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b + c < 2 * a + 4 * b)
    (q2 : 2 * c < a + 2 * b)
    (q3 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0407 (a b c e f : Nat)
    (q0 : 6 * a ≤ e + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : c + e < 2 * a + 2 * b)
    (q3 : c + f < a + 3 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0408 (a b c e f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : c + f < a + 3 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0409 (a b c e f : Nat)
    (q0 : 5 * a ≤ e + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : c + e < 2 * a + 2 * b)
    (q3 : c + f < a + 3 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0410 (a b c e f : Nat)
    (q0 : 4 * a ≤ e + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : c + e < 2 * a + 2 * b)
    (q3 : c + f < a + 3 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0411 (a b c e f : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : c + e < 2 * a + 2 * b)
    (q3 : c + f < a + 3 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0412 (a b c e f : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : c + e < 2 * a + 2 * b)
    (q3 : c + f < a + 3 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0413 (a b c e f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : c + f < a + 3 * b) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0414 (a b c e f : Nat)
    (q0 : 3 * a + b < a + 2 * b + c)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : c + f < a + 3 * b) :
    3 * a + b < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0415 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a > g)
    (q3 : 6 * a ≤ d + g)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0416 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 6 * a ≤ e + f)
    (q3 : f < 2 * a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0417 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : d = 0)
    (q4 : f < 2 * a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0418 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 6 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0419 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 6 * a ≤ b + 2 * d)
    (q3 : d = 0)
    (q4 : f < 2 * a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0420 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 6 * a ≤ 2 * c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0421 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0422 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a > g)
    (q3 : 5 * a ≤ d + g)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0423 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ e + f)
    (q3 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0424 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : d = 0)
    (q4 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0425 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 5 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0426 (a b d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a ≤ b + 2 * d)
    (q3 : d = 0)
    (q4 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0427 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 2 * c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0428 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0429 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ d + g)
    (q3 : d = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0430 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ e + f)
    (q3 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0431 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : d = 0)
    (q4 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0432 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 4 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0433 (a b d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ b + 2 * d)
    (q3 : d = 0)
    (q4 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0434 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * c + d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0435 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ b + e)
    (q3 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0436 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ c + d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0437 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a < a + 3 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0438 (a b d e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ d + g)
    (q3 : d = 0)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0439 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ e + f)
    (q3 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0440 (a b d f : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : d = 0)
    (q3 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0441 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 3 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0442 (a b d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + 2 * d)
    (q3 : d = 0)
    (q4 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0443 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d = 0)
    (q4 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0444 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + e)
    (q3 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0445 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ c + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0446 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ e + f)
    (q2 : 2 * e < a + b + f)
    (q3 : 2 * f = a + 4 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0447 (a b c e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + c + e)
    (q2 : 2 * e < a + b + f)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0448 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + 2 * d)
    (q2 : 2 * f = a + 4 * b)
    (q3 : d = 0)
    (q4 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0449 (a b e f : Nat)
    (q0 : 2 * a ≤ b + e)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0450 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ c + d)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0451 (a b c f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a > g)
    (q2 : 5 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0452 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ d + e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : d = 0)
    (q6 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0453 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0454 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b < a + 2 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0455 (a b c e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0456 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ d + e)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : d = 0)
    (q6 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0457 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0458 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a + b < a + 2 * b + c)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0459 (a b c e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0460 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0461 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0462 (a b c f : Nat)
    (q0 : 2 * a + b < a + 2 * b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0463 (a b c f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a > g)
    (q2 : 5 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0464 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ d + e)
    (q4 : a + 2 * b = 2 * c)
    (q5 : d = 0)
    (q6 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0465 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a > 2 * d)
    (q2 : 5 * a ≤ 2 * b + d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0466 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a + b + c < 2 * a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0467 (a b c e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0468 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 4 * a ≤ d + e)
    (q3 : 5 * a > 2 * d)
    (q4 : a + 2 * b = 2 * c)
    (q5 : d = 0)
    (q6 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0469 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0470 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a + b + c < 2 * a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0471 (a b c e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ b + g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0472 (a b c d e f : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : 3 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0473 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d = 0)
    (q5 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0474 (a b c e f : Nat)
    (q0 : 2 * a + b + c < 2 * a + 4 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a + 2 * b = 2 * c)
    (q4 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0475 (a b c e g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : g < a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0476 (a b c e g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : g < a + 2 * b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0477 (a b c e g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : g < a + 2 * b) :
    4 * a + b < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0478 (a b c e : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 6 * a ≤ b + c + e) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0479 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 6 * a ≤ 2 * c + d)
    (q4 : d = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0480 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 5 * a < a + 3 * b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0481 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ 2 * b + f)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0482 (a b c e : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 5 * a ≤ b + c + e) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0483 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ b + 2 * d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0484 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a > 2 * d)
    (q3 : 5 * a ≤ 2 * c + d)
    (q4 : d = 0)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0485 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 4 * a < a + 3 * b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0486 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ d + g)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0487 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ 2 * b + d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0488 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ 2 * b + f)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0489 (a b c e : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 4 * a ≤ b + c + e) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0490 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ b + 2 * d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0491 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ 2 * c + d)
    (q3 : 5 * a > 2 * d)
    (q4 : d = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0492 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ c + d)
    (q3 : 5 * a > 2 * d)
    (q4 : d = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0493 (a b c e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : 2 * g < 5 * a + 2 * b)
    (q4 : 3 * a < a + 3 * b)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0494 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ 2 * b + f)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0495 (a b c e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a ≤ b + c + e)
    (q3 : 4 * e < a + 2 * b + 2 * g)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0496 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ b + 2 * d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0497 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ 2 * c + d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0498 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 3 * a ≤ c + d)
    (q4 : d = 0)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0499 (a b c f g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ f)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0500 (a b e f g : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0501 (a b c e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + c + e)
    (q2 : 2 * c < a + 2 * b)
    (q3 : 4 * e < a + 2 * b + 2 * g)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0502 (a b c d g : Nat)
    (q0 : 2 * a ≤ b + 2 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0503 (a b c d g : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0504 (a b c d g : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0505 (a b c f g : Nat)
    (q0 : 2 * a ≤ f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0506 (a b c d g : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0507 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 5 * a ≤ 4 * b)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0508 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 7 * a ≤ 4 * c)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0509 (a b c e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : 2 * g < 5 * a + 2 * b)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0510 (a b c e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : 2 * g < 5 * a + 2 * b)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0511 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0512 (a b c e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a ≤ 4 * b)
    (q3 : 4 * e < a + 2 * b + 2 * g)
    (q4 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0513 (a b c e : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 5 * a ≤ 4 * c) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0514 (a b c e : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 9 * a ≤ 4 * e) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0515 (a b c e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * e < 3 * a + 2 * b)
    (q3 : 2 * g < 5 * a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0516 (a b c e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b)
    (q3 : 4 * e < a + 2 * b + 2 * g)
    (q4 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0517 (a d : Nat)
    (q0 : 0 < a)
    (q1 : d = 0) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0518 (a b c e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : 7 * a ≤ 4 * e)
    (q4 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0519 (a b c e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b + c < 2 * a + 4 * b)
    (q2 : 2 * c < a + 2 * b)
    (q3 : 4 * e < a + 2 * b + 2 * g)
    (q4 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0520 (a b c d e g : Nat)
    (q0 : 6 * a ≤ d + g)
    (q1 : d = 0)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0521 (a b c e f g : Nat)
    (q0 : 6 * a ≤ e + f)
    (q1 : 7 * a > 2 * f)
    (q2 : e < a + c)
    (q3 : f = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0522 (a b c d g : Nat)
    (q0 : 5 * a > 2 * d)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : d = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0523 (a b c f g : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : f = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0524 (a b c e : Nat)
    (q0 : 6 * a ≤ b + c + e)
    (q1 : e < a + c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0525 (a b c d g : Nat)
    (q0 : 5 * a > 2 * d)
    (q1 : 6 * a ≤ b + 2 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : d = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0526 (a b c d e g : Nat)
    (q0 : 6 * a ≤ 2 * c + d)
    (q1 : d = 0)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0527 (a b c g : Nat)
    (q0 : 6 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0528 (a b c e g : Nat)
    (q0 : 5 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    5 * a < b + 2 * c ∧ 3 * a + c < b + 2 * c ∧ 2 * a + 2 * b < b + 2 * c ∧ 2 * a + e < b + 2 * c ∧ a + 2 * c < b + 2 * c ∧ 2 * b + c < b + 2 * c ∧ a + g < b + 2 * c ∧ c + e < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0529 (a b c d e g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : d = 0)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0530 (a b c e f g : Nat)
    (q0 : 5 * a ≤ e + f)
    (q1 : 7 * a > 2 * f)
    (q2 : e < a + c)
    (q3 : f = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0531 (a b c d g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : d = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0532 (a b c f g : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : f = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0533 (a b c e : Nat)
    (q0 : 5 * a ≤ b + c + e)
    (q1 : e < a + c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0534 (a b c d e g : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0535 (a b c d e g : Nat)
    (q0 : 5 * a ≤ 2 * c + d)
    (q1 : d = 0)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0536 (a b c g : Nat)
    (q0 : 5 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0537 (a b c e g : Nat)
    (q0 : 4 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a < b + 2 * c ∧ 2 * a + c < b + 2 * c ∧ a + 2 * b < b + 2 * c ∧ a + e < b + 2 * c ∧ 2 * c < b + 2 * c ∧ g < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0538 (a b c d g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0539 (a b c e f g : Nat)
    (q0 : 4 * a ≤ e + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c)
    (q3 : f = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0540 (a b c d g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : d = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0541 (a b c f g : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : f = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0542 (a b c e : Nat)
    (q0 : 4 * a ≤ b + c + e)
    (q1 : e < a + c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0543 (a b c d e g : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0544 (a b c d g : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0545 (a b c g : Nat)
    (q0 : 4 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0546 (a b c e g : Nat)
    (q0 : 4 * a ≤ b + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0547 (a b c d g : Nat)
    (q0 : 4 * a ≤ c + d)
    (q1 : 5 * a > 2 * d)
    (q2 : d = 0)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0548 (a b c g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0549 (a b c e g : Nat)
    (q0 : 3 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c ∧ a + c < b + 2 * c ∧ 2 * b < b + 2 * c ∧ e < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0550 (a b c d g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : d = 0)
    (q2 : g < 2 * a + c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0551 (a b c e f g : Nat)
    (q0 : 3 * a ≤ e + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c)
    (q3 : f = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0552 (a b c d g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0553 (a b c e f g : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c)
    (q3 : f = 0)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0554 (a b c e : Nat)
    (q0 : 3 * a ≤ b + c + e)
    (q1 : e < a + c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0555 (a b c d e g : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : d = 0)
    (q3 : e < a + c)
    (q4 : g < 2 * a + c)
    (q5 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0556 (a b c d g : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : d = 0)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0557 (a b c g : Nat)
    (q0 : 3 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0558 (a b c e g : Nat)
    (q0 : 3 * a ≤ b + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0559 (a b c d e g : Nat)
    (q0 : 3 * a ≤ c + d)
    (q1 : d = 0)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0560 (a b c g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a ≤ b)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0561 (a b c e f g : Nat)
    (q0 : 3 * a ≤ f)
    (q1 : e < a + c)
    (q2 : f = 0)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0562 (a b c g : Nat)
    (q0 : 3 * a ≤ b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0563 (a b c g : Nat)
    (q0 : 2 * a < b + 2 * c)
    (q1 : g < 2 * a + c)
    (q2 : g = 2 * c) :
    2 * a < b + 2 * c ∧ c < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0564 (a b c : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c) :
    4 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0565 (a b c : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c) :
    4 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0566 (a b c d g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : d = 0)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0567 (a b c e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c) :
    4 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0568 (a b c f g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : f = 0)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0569 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c) :
    4 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0570 (a b c e g : Nat)
    (q0 : 4 * a + b < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    4 * a + b < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + b + e < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0571 (a b c : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0572 (a b c : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0573 (a b c d g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : d = 0)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0574 (a b c e : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0575 (a b c f g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : f = 0)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0576 (a b c g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0577 (a b c e g : Nat)
    (q0 : 3 * a + b < 3 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c)
    (q3 : g < 2 * a + c)
    (q4 : g = 2 * c) :
    3 * a + b < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ b + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0578 (a b c : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a ≤ 4 * b) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0579 (a b c : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0580 (a b c d g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : d = 0)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0581 (a b c e : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : e < a + c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0582 (a b c f g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : f = 0)
    (q2 : g < 2 * a + c)
    (q3 : g = 2 * c) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0583 (a b c g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : g < 2 * a + c) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0584 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c) :
    2 * a + b < 3 * c ∧ b + c < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0585 (a b c d e g : Nat)
    (q0 : 5 * a > 2 * d)
    (q1 : 6 * a ≤ d + g)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0586 (a b c e f g : Nat)
    (q0 : 6 * a ≤ e + f)
    (q1 : 7 * a > 2 * f)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : f = 0)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0587 (a b c d e g : Nat)
    (q0 : 5 * a > 2 * d)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0588 (a b c e f g : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0589 (a b c d e g : Nat)
    (q0 : 5 * a > 2 * d)
    (q1 : 6 * a ≤ b + 2 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0590 (a b c d e g : Nat)
    (q0 : 5 * a > 2 * d)
    (q1 : 6 * a ≤ 2 * c + d)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0591 (a b c e g : Nat)
    (q0 : 6 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0592 (a b c e g : Nat)
    (q0 : 5 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    5 * a < b + 2 * c ∧ 3 * a + c < b + 2 * c ∧ 2 * a + 2 * b < b + 2 * c ∧ 2 * a + e < b + 2 * c ∧ a + 2 * c < b + 2 * c ∧ 2 * b + c < b + 2 * c ∧ a + g < b + 2 * c ∧ c + e < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0593 (a b c d e g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0594 (a b c e f g : Nat)
    (q0 : 5 * a ≤ e + f)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : f = 0)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0595 (a b c d e g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = 2 * e)
    (q4 : d = 0)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0596 (a b c e f g : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * b < 2 * c)
    (q3 : c + g = 2 * e)
    (q4 : e < a + c)
    (q5 : f = 0)
    (q6 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0597 (a b c d e g : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0598 (a b c d e g : Nat)
    (q0 : 5 * a ≤ 2 * c + d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d = 0)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0599 (a b c e g : Nat)
    (q0 : 5 * a ≤ 3 * b + c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega

end Max11DegreeRoutes
