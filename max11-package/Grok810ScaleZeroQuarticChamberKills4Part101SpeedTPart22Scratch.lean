import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4400 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ f + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4401 (a b d f : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4402 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + c + g)
    (q1 : b + f = 2 * d)
    (q2 : c + g < a + b + f)
    (q3 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4403 (a b d : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4404 (a b d f : Nat)
    (q0 : 4 * a ≤ b + d + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4405 (a b d e f : Nat)
    (q0 : 4 * a ≤ b + 2 * e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4406 (a b c d f : Nat)
    (q0 : 4 * a ≤ 2 * c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4407 (a b c d e f : Nat)
    (q0 : 4 * a ≤ c + d + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4408 (a b d : Nat)
    (q0 : 4 * a ≤ 3 * d)
    (q1 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4409 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4410 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4411 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4412 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4413 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 5 * b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4414 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4415 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ d + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4416 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a ≤ b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4417 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4418 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4419 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4420 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4421 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4422 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a < a + 2 * b + d)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    3 * a < a + 2 * b + d ∧ a + c < a + 2 * b + d ∧ 2 * b < a + 2 * b + d ∧ e < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4423 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4424 (a b d f : Nat)
    (q0 : 2 * a ≤ 2 * b + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4425 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + c + g)
    (q1 : b + f = 2 * d)
    (q2 : c + g < a + b + f)
    (q3 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4426 (a b d : Nat)
    (q0 : 2 * a ≤ b + 2 * d)
    (q1 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4427 (a b d f : Nat)
    (q0 : 3 * a ≤ b + d + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4428 (a b d e f : Nat)
    (q0 : 3 * a ≤ b + 2 * e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4429 (a b c d f : Nat)
    (q0 : 3 * a ≤ 2 * c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4430 (a b c d e f : Nat)
    (q0 : 3 * a ≤ c + d + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4431 (a b d : Nat)
    (q0 : a ≤ d)
    (q1 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4432 (a b c d f : Nat)
    (q0 : 2 * a ≤ 3 * b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4433 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 3 * b + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4434 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4435 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4436 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 5 * b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4437 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4438 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4439 (a b d f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4440 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4441 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4442 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4443 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4444 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a ≤ b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4445 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4446 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4447 (a b c d f : Nat)
    (q0 : 2 * a < a + 2 * b + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 2 * b + d ∧ c < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4448 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4449 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ c + f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f = 0)
    (q6 : g = a + 2 * b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4450 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4451 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4452 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4453 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4454 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4455 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4456 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4457 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4458 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a ≤ b)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4459 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4460 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4461 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4462 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4463 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4464 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4465 (a b c d g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4466 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4467 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4468 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4469 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4470 (a b c d g : Nat)
    (q0 : 2 * a + b < a + 2 * b + c)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4471 (a b d e g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : b + g = d + e)
    (q2 : d < a + b) :
    4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4472 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ c + f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + g = d + e)
    (q5 : d < a + b)
    (q6 : f = 0)
    (q7 : g = a + 2 * b) :
    4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4473 (a b d e g : Nat)
    (q0 : 4 * a ≤ 3 * b)
    (q1 : b + g = d + e)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4474 (a b d e g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : b + g = d + e)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4475 (a b c d e g : Nat)
    (q0 : 5 * a ≤ b + 2 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4476 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + d < a + 2 * b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4477 (a b d e g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : b + g = d + e)
    (q2 : d < a + b) :
    3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4478 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : f = 0)
    (q6 : g = a + 2 * b) :
    3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4479 (a b d e g : Nat)
    (q0 : a ≤ b)
    (q1 : b + g = d + e)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4480 (a b d e g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : b + g = d + e)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4481 (a b c d e g : Nat)
    (q0 : 4 * a ≤ b + 2 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4482 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + d < a + 2 * b + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4483 (a b d e g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : b + g = d + e)
    (q2 : d < a + b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4484 (a b c d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : f = 0)
    (q6 : g = a + 2 * b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4485 (a b d e g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : b + g = d + e)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4486 (a b d e g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : b + g = d + e)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4487 (a b c d e g : Nat)
    (q0 : 3 * a ≤ b + 2 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4488 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ f)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4489 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4490 (a b c d e g : Nat)
    (q0 : 2 * a + d < a + 2 * b + e)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4491 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4492 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ c + f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f = 0)
    (q6 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4493 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4494 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4495 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4496 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4497 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a + b + c < 2 * a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4498 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4499 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4500 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4501 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a ≤ b)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4502 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4503 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4504 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a + b + c < 2 * a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4505 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4506 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4507 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4508 (a b c d g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4509 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4510 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4511 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4512 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4513 (a b c d e g : Nat)
    (q0 : 2 * a + b + c < 2 * a + 4 * b)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4514 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ e + f)
    (q2 : 7 * a > 2 * f)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : f = 0)
    (q6 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4515 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4516 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4517 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4518 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4519 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ e + f)
    (q2 : 7 * a > 2 * f)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : f = 0)
    (q6 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4520 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4521 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4522 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4523 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4524 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ e + f)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4525 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4526 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4527 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4528 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4529 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4530 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4531 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4532 (a b d e f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ e + f)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4533 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 2 * b + f)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4534 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4535 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4536 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4537 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4538 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a ≤ b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4539 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ f)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4540 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4541 (a b c d g : Nat)
    (q0 : 2 * a < a + 3 * b)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4542 (a b d e f g : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4543 (a b d f g : Nat)
    (q0 : 2 * a ≤ 2 * b + f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4544 (a b c d e g : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4545 (a b c d g : Nat)
    (q0 : 2 * a ≤ 3 * b + c)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4546 (a b d e g : Nat)
    (q0 : 2 * a ≤ b + e)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4547 (a b c d g : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4548 (a b d g : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4549 (a b d f g : Nat)
    (q0 : 2 * a ≤ f)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4550 (a b c d g : Nat)
    (q0 : 2 * a ≤ b + c)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4551 (a b d g : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4552 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a > 2 * f)
    (q2 : 7 * a ≤ f + g)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4553 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4554 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ b + c + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4555 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a > 2 * f)
    (q2 : 7 * a ≤ b + d + f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4556 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ b + 2 * e)
    (q2 : b + g = d + e)
    (q3 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4557 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a > 2 * f)
    (q2 : 7 * a ≤ 2 * c + f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f = 0)
    (q6 : g = a + 2 * b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4558 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ c + d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4559 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4560 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ 3 * b + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4561 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4562 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4563 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 7 * a ≤ 5 * b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4564 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a < a + 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    6 * a < a + 2 * b + d ∧ 4 * a + c < a + 2 * b + d ∧ 3 * a + 2 * b < a + 2 * b + d ∧ 3 * a + e < a + 2 * b + d ∧ 2 * a + b + d < a + 2 * b + d ∧ 2 * a + 2 * c < a + 2 * b + d ∧ a + 2 * b + c < a + 2 * b + d ∧ 4 * b < a + 2 * b + d ∧ 2 * a + g < a + 2 * b + d ∧ a + c + e < a + 2 * b + d ∧ a + 2 * d < a + 2 * b + d ∧ 2 * b + e < a + 2 * b + d ∧ b + c + d < a + 2 * b + d ∧ 3 * c < a + 2 * b + d ∧ c + g < a + 2 * b + d ∧ 2 * e < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4565 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ f + g)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4566 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4567 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ b + c + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4568 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ b + d + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4569 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ b + 2 * e)
    (q2 : b + g = d + e)
    (q3 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4570 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ 2 * c + f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f = 0)
    (q6 : g = a + 2 * b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4571 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ c + d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4572 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4573 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ 3 * b + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4574 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4575 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4576 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 6 * a ≤ 5 * b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4577 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a < a + 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    5 * a < a + 2 * b + d ∧ 3 * a + c < a + 2 * b + d ∧ 2 * a + 2 * b < a + 2 * b + d ∧ 2 * a + e < a + 2 * b + d ∧ a + b + d < a + 2 * b + d ∧ a + 2 * c < a + 2 * b + d ∧ 2 * b + c < a + 2 * b + d ∧ a + g < a + 2 * b + d ∧ c + e < a + 2 * b + d ∧ 2 * d < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4578 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ f + g)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4579 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 2 * b + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4580 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ b + c + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4581 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ b + d + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4582 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ b + 2 * e)
    (q2 : b + g = d + e)
    (q3 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4583 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 2 * c + f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f = 0)
    (q6 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4584 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ c + d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4585 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4586 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 3 * b + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4587 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4588 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4589 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : a ≤ b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4590 (a b c d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ c + f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : f = 0)
    (q6 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4591 (a b d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ d + e)
    (q2 : b + g = d + e)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4592 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4593 (a b d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4594 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4595 (a b c d e g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a < a + 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + g = d + e)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    4 * a < a + 2 * b + d ∧ 2 * a + c < a + 2 * b + d ∧ a + 2 * b < a + 2 * b + d ∧ a + e < a + 2 * b + d ∧ b + d < a + 2 * b + d ∧ 2 * c < a + 2 * b + d ∧ g < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4596 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ f + g)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4597 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 3 * a ≤ 2 * b + f)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4598 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + c + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    3 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4599 (a b d f g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 4 * a ≤ b + d + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 2 * b + d := by
  omega

end Max11DegreeRoutes
