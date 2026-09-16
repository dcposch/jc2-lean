import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4200 (a b c d f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + c + f < d + g)
    (q3 : b + g < c + f)
    (q4 : c + g = a + 2 * d)
    (q5 : g = 2 * c) :
    3 * a + d < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4201 (a b c d e f g : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + d < c + 2 * d)
    (q2 : a + c + f < d + g)
    (q3 : b + g < c + f)
    (q4 : c + f = d + e)
    (q5 : c + g = a + 2 * d)
    (q6 : g = 2 * c) :
    3 * a + d < c + 2 * d ∧ 2 * a + b + c < c + 2 * d ∧ a + 3 * b < c + 2 * d ∧ 2 * a + f < c + 2 * d ∧ a + b + e < c + 2 * d ∧ a + c + d < c + 2 * d ∧ 2 * b + d < c + 2 * d ∧ b + 2 * c < c + 2 * d ∧ c + f < c + 2 * d ∧ d + e < c + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4202 (a b c d e g : Nat)
    (q0 : 6 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : d + e < b + g)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4203 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4204 (a b c d e f g : Nat)
    (q0 : 6 * a ≤ b + 2 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4205 (a b c d e g : Nat)
    (q0 : 6 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : d + e < b + g)
    (q3 : e < a + c) :
    5 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4206 (a b c d e f g : Nat)
    (q0 : 5 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d + e < b + g)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    5 * a < b + 2 * c ∧ 3 * a + c < b + 2 * c ∧ 2 * a + 2 * b < b + 2 * c ∧ 2 * a + e < b + 2 * c ∧ a + b + d < b + 2 * c ∧ a + 2 * c < b + 2 * c ∧ 2 * b + c < b + 2 * c ∧ a + g < b + 2 * c ∧ b + f < b + 2 * c ∧ c + e < b + 2 * c ∧ 2 * d < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4207 (a b c d e g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : d + e < b + g)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4208 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4209 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4210 (a b c d e g : Nat)
    (q0 : 5 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : d + e < b + g)
    (q3 : e < a + c) :
    4 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4211 (a b c d e f g : Nat)
    (q0 : 4 * a < b + 2 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d + e < b + g)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    4 * a < b + 2 * c ∧ 2 * a + c < b + 2 * c ∧ a + 2 * b < b + 2 * c ∧ a + e < b + 2 * c ∧ b + d < b + 2 * c ∧ 2 * c < b + 2 * c ∧ g < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4212 (a b c d e g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : d + e < b + g)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4213 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4214 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4215 (a b c d e g : Nat)
    (q0 : 4 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : d + e < b + g)
    (q3 : e < a + c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4216 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ c + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4217 (a b c d e g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : c + g = 2 * e)
    (q2 : d + e < b + g)
    (q3 : e < a + c)
    (q4 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4218 (a b c d e f g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4219 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ b + 2 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4220 (a b c d e g : Nat)
    (q0 : 3 * a ≤ 2 * c + d)
    (q1 : c + g = 2 * e)
    (q2 : d + e < b + g)
    (q3 : e < a + c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4221 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ c + d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a < b + 2 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4222 (a b c d e g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d + e < b + g)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    3 * a + b + c < 2 * c + e ∧ 4 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4223 (a b c d e f g : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d + e < b + g)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    3 * a + b + c < 2 * c + e ∧ 4 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4224 (a b c d e f g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a + b + c < 2 * c + e ∧ 4 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4225 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d + e < b + g)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    3 * a + b + c < 2 * c + e ∧ 4 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4226 (a b c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a + b + c < 2 * c + e ∧ 4 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4227 (a b c d e f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d + e < b + g)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    3 * a + b + c < 2 * c + e ∧ 4 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4228 (a b c d e f g : Nat)
    (q0 : 3 * a + b + c < 2 * c + e ∧ 4 * a + d < 2 * c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d + e < b + g)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e ∧ 2 * a + 3 * b < 2 * c + e ∧ 3 * a + f < 2 * c + e ∧ 2 * a + b + e < 2 * c + e ∧ 2 * a + c + d < 2 * c + e ∧ a + 2 * b + d < 2 * c + e ∧ a + b + 2 * c < 2 * c + e ∧ 3 * b + c < 2 * c + e ∧ a + c + f < 2 * c + e ∧ a + d + e < 2 * c + e ∧ 2 * b + f < 2 * c + e ∧ b + c + e < 2 * c + e ∧ b + 2 * d < 2 * c + e ∧ 2 * c + d < 2 * c + e ∧ d + g < 2 * c + e ∧ e + f < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4229 (a b c d e g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b < 2 * c)
    (q2 : c + g = 2 * e)
    (q3 : d + e < b + g)
    (q4 : e < a + c)
    (q5 : g = 2 * c) :
    2 * a + b + c < 2 * c + e ∧ 3 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4230 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d + e < b + g)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    2 * a + b + c < 2 * c + e ∧ 3 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4231 (a b c d e f g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a + b + c < 2 * c + e ∧ 3 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4232 (a b c d e f g : Nat)
    (q0 : 9 * a ≤ 4 * e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d + e < b + g)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    2 * a + b + c < 2 * c + e ∧ 3 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4233 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a + b + c < 2 * c + e ∧ 3 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4234 (a b c d e f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : b + g = c + f)
    (q4 : c + g = 2 * e)
    (q5 : d + e < b + g)
    (q6 : e < a + c)
    (q7 : g = 2 * c) :
    2 * a + b + c < 2 * c + e ∧ 3 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4235 (a b c d e f g : Nat)
    (q0 : 2 * a + b + c < 2 * c + e ∧ 3 * a + d < 2 * c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e ∧ a + 3 * b < 2 * c + e ∧ 2 * a + f < 2 * c + e ∧ a + b + e < 2 * c + e ∧ a + c + d < 2 * c + e ∧ 2 * b + d < 2 * c + e ∧ b + 2 * c < 2 * c + e ∧ c + f < 2 * c + e ∧ d + e < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4236 (a b c d e g : Nat)
    (q0 : a + 2 * b < 2 * c)
    (q1 : a ≤ 4 * b)
    (q2 : c + g = 2 * e)
    (q3 : d + e < b + g) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4237 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4238 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4239 (a b c d e f g : Nat)
    (q0 : 7 * a ≤ 4 * e)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4240 (a b c d e f g : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 2 * f < 2 * g)
    (q2 : a + b + f < c + g)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4241 (a b c d e f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + b + f < c + g)
    (q2 : b + g = c + f)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4242 (a b c d e f g : Nat)
    (q0 : 2 * a + d < 2 * c + e)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a + b + f < c + g)
    (q3 : c + g = 2 * e)
    (q4 : d + e < b + g)
    (q5 : e < a + c)
    (q6 : g = 2 * c) :
    2 * a + d < 2 * c + e ∧ a + b + c < 2 * c + e ∧ 3 * b < 2 * c + e ∧ a + f < 2 * c + e ∧ b + e < 2 * c + e ∧ c + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4243 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + f = 2 * d)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4244 (a b c d f : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4245 (a b c d e f : Nat)
    (q0 : 5 * a ≤ d + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4246 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4247 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4248 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4249 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c ∧ c + f < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4250 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + f = 2 * d)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4251 (a b c d f : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4252 (a b c d e f : Nat)
    (q0 : 4 * a ≤ d + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4253 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a ≤ b)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4254 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4255 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4256 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4257 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + f = 2 * d)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4258 (a b c d f : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4259 (a b c d e f : Nat)
    (q0 : 3 * a ≤ d + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4260 (a b c d f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4261 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4262 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4263 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4264 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4265 (a b c d f : Nat)
    (q0 : 2 * a + b < a + 2 * b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4266 (a b c d e f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b) :
    4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4267 (a b c d e f : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4268 (a b d e : Nat)
    (q0 : 5 * a ≤ d + e)
    (q1 : d < a + b) :
    4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4269 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : d < a + b) :
    4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4270 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : d < a + b) :
    4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4271 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    4 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4272 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + d < a + 2 * b + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    4 * a + d < a + 2 * b + e ∧ 3 * a + b + c < a + 2 * b + e ∧ 2 * a + 3 * b < a + 2 * b + e ∧ 3 * a + f < a + 2 * b + e ∧ 2 * a + b + e < a + 2 * b + e ∧ 2 * a + c + d < a + 2 * b + e ∧ a + 2 * b + d < a + 2 * b + e ∧ a + b + 2 * c < a + 2 * b + e ∧ 3 * b + c < a + 2 * b + e ∧ a + c + f < a + 2 * b + e ∧ a + d + e < a + 2 * b + e ∧ 2 * b + f < a + 2 * b + e ∧ b + c + e < a + 2 * b + e ∧ b + 2 * d < a + 2 * b + e ∧ 2 * c + d < a + 2 * b + e ∧ d + g < a + 2 * b + e ∧ e + f < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4273 (a b c d e f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b) :
    3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4274 (a b c d e f : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4275 (a b d e : Nat)
    (q0 : 4 * a ≤ d + e)
    (q1 : d < a + b) :
    3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4276 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a ≤ b)
    (q3 : d < a + b) :
    3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4277 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : d < a + b) :
    3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4278 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    3 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4279 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + d < a + 2 * b + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    3 * a + d < a + 2 * b + e ∧ 2 * a + b + c < a + 2 * b + e ∧ a + 3 * b < a + 2 * b + e ∧ 2 * a + f < a + 2 * b + e ∧ a + b + e < a + 2 * b + e ∧ a + c + d < a + 2 * b + e ∧ 2 * b + d < a + 2 * b + e ∧ b + 2 * c < a + 2 * b + e ∧ c + f < a + 2 * b + e ∧ d + e < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4280 (a b c d e f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + g < a + b + f)
    (q4 : d < a + b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4281 (a b c d e f : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4282 (a b d e : Nat)
    (q0 : 3 * a ≤ d + e)
    (q1 : d < a + b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4283 (a b d e f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : d < a + b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4284 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : d < a + b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4285 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4286 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4287 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    2 * a + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4288 (a b c d e f : Nat)
    (q0 : 2 * a + d < a + 2 * b + e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    2 * a + d < a + 2 * b + e ∧ a + b + c < a + 2 * b + e ∧ 3 * b < a + 2 * b + e ∧ a + f < a + 2 * b + e ∧ b + e < a + 2 * b + e ∧ c + d < a + 2 * b + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4289 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + g)
    (q1 : b + f = 2 * d)
    (q2 : c + g < a + b + f)
    (q3 : d < a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4290 (a b c d f : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4291 (a b c d e f : Nat)
    (q0 : 5 * a ≤ d + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4292 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4293 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4294 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4295 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + b + c < 2 * a + 4 * b)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ 2 * a + d + e < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + c + e < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ a + e + f < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ c + d + e < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b ∧ f + g < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4296 (a b c d f g : Nat)
    (q0 : 4 * a ≤ b + g)
    (q1 : b + f = 2 * d)
    (q2 : c + g < a + b + f)
    (q3 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4297 (a b c d f : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4298 (a b c d e f : Nat)
    (q0 : 4 * a ≤ d + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4299 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a ≤ b)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4300 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4301 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4302 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + b + c < 2 * a + 4 * b)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ a + d + e < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + c + e < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b ∧ e + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4303 (a b c d f g : Nat)
    (q0 : 3 * a ≤ b + g)
    (q1 : b + f = 2 * d)
    (q2 : c + g < a + b + f)
    (q3 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4304 (a b c d f : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4305 (a b c d e f : Nat)
    (q0 : 3 * a ≤ d + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4306 (a b c d f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4307 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4308 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4309 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4310 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4311 (a b c d e f : Nat)
    (q0 : 2 * a + b + c < 2 * a + 4 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + b + e < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b ∧ d + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4312 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ e + f)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4313 (a b d f : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4314 (a b c d e f : Nat)
    (q0 : 6 * a ≤ b + c + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4315 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4316 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ b + f < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4317 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ e + f)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4318 (a b d f : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4319 (a b c d e f : Nat)
    (q0 : 5 * a ≤ b + c + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4320 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4321 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4322 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ e + f)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4323 (a b d f : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4324 (a b c d e f : Nat)
    (q0 : 4 * a ≤ b + c + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4325 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4326 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4327 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4328 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4329 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a < a + 3 * b)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : d < a + b) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b ∧ e < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4330 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ e + f)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4331 (a b d f : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4332 (a b c d e f : Nat)
    (q0 : 3 * a ≤ b + c + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4333 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4334 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4335 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4336 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a ≤ b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4337 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4338 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4339 (a b c d f : Nat)
    (q0 : 2 * a < a + 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4340 (a b d e f : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4341 (a b d f : Nat)
    (q0 : 2 * a ≤ 2 * b + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4342 (a b c d e f : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4343 (a b c d f : Nat)
    (q0 : 2 * a ≤ 3 * b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4344 (a b d e f : Nat)
    (q0 : 2 * a ≤ b + e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4345 (a b c d f : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4346 (a b d f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4347 (a b d f : Nat)
    (q0 : 2 * a ≤ f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4348 (a b c d f : Nat)
    (q0 : 2 * a ≤ b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4349 (a b d f : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4350 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 7 * a ≤ f + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4351 (a b d f : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4352 (a b c d f g : Nat)
    (q0 : 7 * a ≤ b + c + g)
    (q1 : b + f = 2 * d)
    (q2 : c + g < a + b + f)
    (q3 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4353 (a b d : Nat)
    (q0 : 6 * a ≤ b + 2 * d)
    (q1 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4354 (a b d f : Nat)
    (q0 : 7 * a ≤ b + d + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4355 (a b d e f : Nat)
    (q0 : 7 * a ≤ b + 2 * e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4356 (a b c d f : Nat)
    (q0 : 7 * a ≤ 2 * c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4357 (a b c d e f : Nat)
    (q0 : 7 * a ≤ c + d + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4358 (a b d : Nat)
    (q0 : 7 * a ≤ 3 * d)
    (q1 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4359 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4360 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 7 * a ≤ 3 * b + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4361 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 7 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4362 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 7 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4363 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 7 * a ≤ 5 * b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    6 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4364 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a < a + 2 * b + d)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    6 * a < a + 2 * b + d ∧ 4 * a + c < a + 2 * b + d ∧ 3 * a + 2 * b < a + 2 * b + d ∧ 3 * a + e < a + 2 * b + d ∧ 2 * a + b + d < a + 2 * b + d ∧ 2 * a + 2 * c < a + 2 * b + d ∧ a + 2 * b + c < a + 2 * b + d ∧ 4 * b < a + 2 * b + d ∧ 2 * a + g < a + 2 * b + d ∧ a + b + f < a + 2 * b + d ∧ a + c + e < a + 2 * b + d ∧ a + 2 * d < a + 2 * b + d ∧ 2 * b + e < a + 2 * b + d ∧ b + c + d < a + 2 * b + d ∧ 3 * c < a + 2 * b + d ∧ c + g < a + 2 * b + d ∧ d + f < a + 2 * b + d ∧ 2 * e < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4365 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ f + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4366 (a b d f : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4367 (a b c d f g : Nat)
    (q0 : 6 * a ≤ b + c + g)
    (q1 : b + f = 2 * d)
    (q2 : c + g < a + b + f)
    (q3 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4368 (a b d : Nat)
    (q0 : 5 * a ≤ b + 2 * d)
    (q1 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4369 (a b d f : Nat)
    (q0 : 6 * a ≤ b + d + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4370 (a b d e f : Nat)
    (q0 : 6 * a ≤ b + 2 * e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4371 (a b c d f : Nat)
    (q0 : 6 * a ≤ 2 * c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4372 (a b c d e f : Nat)
    (q0 : 6 * a ≤ c + d + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4373 (a b d : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4374 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4375 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ 3 * b + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4376 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4377 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4378 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ 5 * b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    5 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4379 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a < a + 2 * b + d)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    5 * a < a + 2 * b + d ∧ 3 * a + c < a + 2 * b + d ∧ 2 * a + 2 * b < a + 2 * b + d ∧ 2 * a + e < a + 2 * b + d ∧ a + b + d < a + 2 * b + d ∧ a + 2 * c < a + 2 * b + d ∧ 2 * b + c < a + 2 * b + d ∧ a + g < a + 2 * b + d ∧ b + f < a + 2 * b + d ∧ c + e < a + 2 * b + d ∧ 2 * d < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4380 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ f + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : c + g < a + b + f)
    (q5 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4381 (a b d f : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4382 (a b c d f g : Nat)
    (q0 : 5 * a ≤ b + c + g)
    (q1 : b + f = 2 * d)
    (q2 : c + g < a + b + f)
    (q3 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4383 (a b d : Nat)
    (q0 : 4 * a ≤ b + 2 * d)
    (q1 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4384 (a b d f : Nat)
    (q0 : 5 * a ≤ b + d + f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4385 (a b d e f : Nat)
    (q0 : 5 * a ≤ b + 2 * e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4386 (a b c d f : Nat)
    (q0 : 5 * a ≤ 2 * c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4387 (a b c d e f : Nat)
    (q0 : 5 * a ≤ c + d + e)
    (q1 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4388 (a b d : Nat)
    (q0 : 5 * a ≤ 3 * d)
    (q1 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4389 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4390 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 3 * b + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4391 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 2 * b + c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4392 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 3 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4393 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a ≤ b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4394 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ c + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4395 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ d + e)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4396 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4397 (a b d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4398 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a < a + 2 * b + d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_4399 (a b c d e f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a < a + 2 * b + d)
    (q2 : a + 2 * b + 2 * f = 2 * d + 2 * e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : b + f = 2 * d)
    (q5 : c + g < a + b + f)
    (q6 : d < a + b) :
    4 * a < a + 2 * b + d ∧ 2 * a + c < a + 2 * b + d ∧ a + 2 * b < a + 2 * b + d ∧ a + e < a + 2 * b + d ∧ b + d < a + 2 * b + d ∧ 2 * c < a + 2 * b + d ∧ g < a + 2 * b + d := by
  omega

end Max11DegreeRoutes
