import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0200 (a b d g : Nat)
    (q0 : 2 * a ≤ 2 * b + d)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : d = 0)
    (q3 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0201 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ 2 * b + f)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0202 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ b + c + e)
    (q3 : c = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0203 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ b + 2 * d)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0204 (a b c d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ 2 * c + d)
    (q3 : 5 * a > 2 * d)
    (q4 : c = 0)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0205 (a b c g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ 3 * b + c)
    (q2 : c = 0)
    (q3 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0206 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ b + e)
    (q3 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0207 (a b c d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ c + d)
    (q3 : 5 * a > 2 * d)
    (q4 : c = 0)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0208 (a b g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : a ≤ b)
    (q2 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0209 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ f)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0210 (a b c g : Nat)
    (q0 : 2 * a > c)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ b + c)
    (q3 : c = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0211 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ d + g)
    (q2 : d = 0)
    (q3 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0212 (a b e f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ e + f)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0213 (a b c e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + c + e)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : c = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0214 (a b d g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + 2 * d)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : d = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0215 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 2 * c + d)
    (q2 : c = 0)
    (q3 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0216 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 3 * b + c)
    (q2 : c = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0217 (a b e g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + e)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0218 (a b c d : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ c + d)
    (q2 : c = 0)
    (q3 : d = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0219 (a b c g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ b + c)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : c = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0220 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0221 (a c : Nat)
    (q0 : 0 < a)
    (q1 : c = 0) :
    ¬ (7 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0222 (a d : Nat)
    (q0 : 0 < a)
    (q1 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0223 (a b e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0224 (a f : Nat)
    (q0 : 0 < a)
    (q1 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0225 (a b e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0226 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b)
    (q3 : g = a + 2 * b) :
    3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + b + e < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 3 * b + e < 2 * a + 4 * b ∧ b + 2 * e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0227 (a b e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : 4 * e < a + 2 * b + 2 * g)
    (q3 : g = a + 2 * b) :
    2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0228 (a c : Nat)
    (q0 : 0 < a)
    (q1 : c = 0) :
    ¬ (5 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0229 (a d : Nat)
    (q0 : 0 < a)
    (q1 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0230 (a b e : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * e) :
    2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0231 (a f : Nat)
    (q0 : 0 < a)
    (q1 : f = 0) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0232 (a b e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b) :
    2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0233 (a b e : Nat)
    (q0 : 2 * a + b + e < 2 * a + 4 * b) :
    2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + b + e < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0234 (a b c d e : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : d < a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ 2 * a + e < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ c + e < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0235 (a b c d e : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : d < a + b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ a + e < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0236 (a b c d e : Nat)
    (q0 : 5 * a ≤ d + e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : c + e < 2 * a + 2 * b)
    (q3 : d < a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0237 (a b c d e : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : d < a + b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + b + e < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ d + e < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0238 (a b c d e : Nat)
    (q0 : 4 * a ≤ d + e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : c + e < 2 * a + 2 * b)
    (q3 : d < a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0239 (a b c d e : Nat)
    (q0 : 3 * a + b < a + 2 * b + c)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + e < 2 * a + 2 * b)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ b + e < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0240 (a b c d e : Nat)
    (q0 : 3 * a ≤ d + e)
    (q1 : a + 2 * b = 2 * c)
    (q2 : c + e < 2 * a + 2 * b)
    (q3 : d < a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0241 (a b c d f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b)
    (q4 : d < a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0242 (a b c d f : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b)
    (q4 : d < a + b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0243 (a b c d f : Nat)
    (q0 : 3 * a + b < a + 2 * b + c)
    (q1 : 3 * a > 2 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0244 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : c + f < a + 3 * b)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0245 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a > g)
    (q2 : 6 * a ≤ d + g)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0246 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ e + f)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : f < 2 * a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0247 (a b f : Nat)
    (q0 : 6 * a ≤ 2 * b + f)
    (q1 : f < 2 * a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0248 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : f < 2 * a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0249 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 6 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0250 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ b + f < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0251 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a > g)
    (q2 : 5 * a ≤ d + g)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0252 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ e + f)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0253 (a b f : Nat)
    (q0 : 5 * a ≤ 2 * b + f)
    (q1 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0254 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0255 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0256 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0257 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ d + g)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b)
    (q4 : g = 0) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0258 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ e + f)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0259 (a b f : Nat)
    (q0 : 4 * a ≤ 2 * b + f)
    (q1 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0260 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0261 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0262 (a b e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ b + e)
    (q3 : e = 0)
    (q4 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0263 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0264 (a b f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : f < 2 * a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0265 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0266 (a b d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + g)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b)
    (q4 : g = 0) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0267 (a b e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ e + f)
    (q2 : e = 0)
    (q3 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0268 (a b f : Nat)
    (q0 : 3 * a ≤ 2 * b + f)
    (q1 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0269 (a b c e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : e = 0)
    (q4 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0270 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 3 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0271 (a b d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + e)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0272 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ c + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0273 (a b f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a ≤ b)
    (q2 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0274 (a b f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0275 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0276 (a b c f : Nat)
    (q0 : 2 * a < a + 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0277 (a b d f g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : 2 * f = a + 4 * b)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b)
    (q4 : g = 0) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0278 (a b e f : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : e = 0)
    (q2 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0279 (a b d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * d < b + f)
    (q2 : 2 * f = a + 4 * b)
    (q3 : a ≤ 2 * b + d) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0280 (a b f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 2 * b + f)
    (q2 : 2 * f = a + 4 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0281 (a b c e f : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : e = 0)
    (q4 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0282 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 2 * c + d)
    (q2 : 2 * d < b + f)
    (q3 : 2 * f = a + 4 * b)
    (q4 : a + 2 * b = 2 * c) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0283 (a b d e f : Nat)
    (q0 : 2 * a ≤ b + e)
    (q1 : 2 * f = a + 4 * b)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0284 (a b c d f : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0285 (a b f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0286 (a b f : Nat)
    (q0 : 2 * a ≤ f)
    (q1 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0287 (a b c f : Nat)
    (q0 : 2 * a ≤ b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0288 (a b d f : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * f = a + 4 * b)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0289 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0290 (a b c f : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0291 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : e = 0)
    (q6 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0292 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0293 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0294 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0295 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ 2 * a + f < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ c + f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0296 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0297 (a b c f : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0298 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : e = 0)
    (q6 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0299 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a ≤ b)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0300 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0301 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0302 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + 2 * b + c ∧ 2 * a + d < a + 2 * b + c ∧ a + b + c < a + 2 * b + c ∧ 3 * b < a + 2 * b + c ∧ a + f < a + 2 * b + c ∧ c + d < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0303 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0304 (a b c f : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0305 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0306 (a b c f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0307 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0308 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0309 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0310 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0311 (a b c d f : Nat)
    (q0 : 2 * a + b < a + 2 * b + c)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    2 * a + b < a + 2 * b + c ∧ a + d < a + 2 * b + c ∧ b + c < a + 2 * b + c ∧ f < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0312 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0313 (a b c f : Nat)
    (q0 : 5 * a ≤ c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0314 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 5 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : e = 0)
    (q6 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0315 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0316 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0317 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 5 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0318 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a + b + c < 2 * a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 4 * a + f < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ 2 * a + c + f < 2 * a + 4 * b ∧ a + 2 * b + f < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + d + f < 2 * a + 4 * b ∧ 2 * c + f < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0319 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0320 (a b c f : Nat)
    (q0 : 4 * a ≤ c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0321 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ d + e)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b)
    (q5 : e = 0)
    (q6 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0322 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a ≤ b)
    (q3 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0323 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0324 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 4 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0325 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a + b + c < 2 * a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + f < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ a + c + f < 2 * a + 4 * b ∧ 2 * b + f < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0326 (a b c d f g : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b)
    (q5 : g = 0) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0327 (a b c f : Nat)
    (q0 : 3 * a ≤ c + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0328 (a b c d e f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ d + e)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0329 (a b c f : Nat)
    (q0 : 2 * a ≤ 3 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0330 (a b c d f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ 2 * b + d)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0331 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + 2 * c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0332 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0333 (a b c f : Nat)
    (q0 : 2 * f = a + 4 * b)
    (q1 : 3 * a ≤ b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0334 (a b c d f : Nat)
    (q0 : 2 * a + b + c < 2 * a + 4 * b)
    (q1 : 2 * f = a + 4 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    2 * a + b + c < 2 * a + 4 * b ∧ a + 3 * b < 2 * a + 4 * b ∧ 2 * a + f < 2 * a + 4 * b ∧ a + c + d < 2 * a + 4 * b ∧ 2 * b + d < 2 * a + 4 * b ∧ b + 2 * c < 2 * a + 4 * b ∧ c + f < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0335 (a b d g : Nat)
    (q0 : 6 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g < a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0336 (a b c d g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 5 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g < a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0337 (a b d g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g < a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0338 (a b c d g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a < a + 3 * b)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g < a + 2 * b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0339 (a b d g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g < a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0340 (a b d g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g < a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0341 (a b d g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g < a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0342 (a b c d g : Nat)
    (q0 : 3 * a > 2 * b)
    (q1 : 4 * a + b < a + 2 * b + c)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b)
    (q4 : g < a + 2 * b) :
    4 * a + b < a + 2 * b + c ∧ 3 * a + d < a + 2 * b + c ∧ 2 * a + b + c < a + 2 * b + c ∧ a + 3 * b < a + 2 * b + c ∧ a + c + d < a + 2 * b + c ∧ 2 * b + d < a + 2 * b + c ∧ b + 2 * c < a + 2 * b + c ∧ b + g < a + 2 * b + c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0343 (a b d g : Nat)
    (q0 : 6 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0344 (a b d e f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 6 * a ≤ e + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0345 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 6 * a ≤ 2 * b + f)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0346 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 6 * a ≤ b + c + e)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0347 (a b c d : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 6 * a ≤ 2 * c + d)
    (q2 : d < a + b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0348 (a b c g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 6 * a ≤ 3 * b + c)
    (q3 : g = a + 2 * b) :
    5 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0349 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a < a + 3 * b)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    5 * a < a + 3 * b ∧ 3 * a + c < a + 3 * b ∧ 2 * a + 2 * b < a + 3 * b ∧ a + b + d < a + 3 * b ∧ a + 2 * c < a + 3 * b ∧ 2 * b + c < a + 3 * b ∧ a + g < a + 3 * b ∧ 2 * d < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0350 (a b d g : Nat)
    (q0 : 5 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0351 (a b d e f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a ≤ e + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0352 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 5 * a ≤ 2 * b + f)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0353 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ b + c + e)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0354 (a b c d : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 2 * c + d)
    (q2 : d < a + b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0355 (a b c g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ 3 * b + c)
    (q3 : g = a + 2 * b) :
    4 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0356 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a < a + 3 * b)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a < a + 3 * b ∧ 2 * a + c < a + 3 * b ∧ a + 2 * b < a + 3 * b ∧ b + d < a + 3 * b ∧ 2 * c < a + 3 * b ∧ g < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0357 (a b d g : Nat)
    (q0 : 4 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0358 (a b d e f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ e + f)
    (q2 : 7 * a > 2 * f)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0359 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a ≤ 2 * b + f)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0360 (a b c d e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ b + c + e)
    (q3 : d < a + b)
    (q4 : e = 0)
    (q5 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0361 (a b c d : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 4 * a ≤ 2 * c + d)
    (q2 : d < a + b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0362 (a b c g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ 3 * b + c)
    (q3 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0363 (a b e g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a > e)
    (q2 : 4 * a ≤ b + e)
    (q3 : e = 0)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0364 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a ≤ c + d)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0365 (a b c g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 3 * a < a + 3 * b)
    (q4 : g = a + 2 * b) :
    3 * a < a + 3 * b ∧ a + c < a + 3 * b ∧ 2 * b < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0366 (a b d g : Nat)
    (q0 : 3 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0367 (a b d e f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ e + f)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0368 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ 2 * b + f)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0369 (a b c e g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ b + c + e)
    (q3 : e = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0370 (a b c d : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 2 * c + d)
    (q2 : d < a + b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0371 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a ≤ 3 * b + c) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0372 (a b d e g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ b + e)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0373 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ c + d)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0374 (a b d f g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a ≤ f)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0375 (a b c g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 3 * a ≤ b + c)
    (q3 : g = a + 2 * b) :
    2 * a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0376 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a < a + 3 * b)
    (q2 : 2 * c < a + 2 * b) :
    2 * a < a + 3 * b ∧ c < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0377 (a b d g : Nat)
    (q0 : 2 * a ≤ d + g)
    (q1 : d < a + b)
    (q2 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0378 (a b d e f g : Nat)
    (q0 : 2 * a ≤ e + f)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : f = 0)
    (q5 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0379 (a b f g : Nat)
    (q0 : 2 * a ≤ 2 * b + f)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : f = 0)
    (q3 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0380 (a b c e g : Nat)
    (q0 : 2 * a ≤ b + c + e)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : e = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0381 (a b c d : Nat)
    (q0 : 2 * a ≤ 2 * c + d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : d < a + b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0382 (a b c : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a ≤ 3 * b + c)
    (q2 : 2 * c < a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0383 (a b d e g : Nat)
    (q0 : 2 * a ≤ b + e)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : d < a + b)
    (q3 : e = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0384 (a b c d g : Nat)
    (q0 : 2 * a ≤ c + d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0385 (a b d f g : Nat)
    (q0 : 2 * a ≤ f)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : d < a + b)
    (q3 : f = 0)
    (q4 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0386 (a b c g : Nat)
    (q0 : 2 * a ≤ b + c)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0387 (a b d g : Nat)
    (q0 : 2 * a ≤ d)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : d < a + b)
    (q3 : g = a + 2 * b) :
    a < a + 3 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0388 (a b c g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0389 (a b c g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0390 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0391 (a e : Nat)
    (q0 : 0 < a)
    (q1 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0392 (a b c g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0393 (a b c d g : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : 4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b)
    (q3 : d < a + b)
    (q4 : g = a + 2 * b) :
    4 * a + b + c < 2 * a + 4 * b ∧ 3 * a + 3 * b < 2 * a + 4 * b ∧ 3 * a + c + d < 2 * a + 4 * b ∧ 2 * a + 2 * b + d < 2 * a + 4 * b ∧ 2 * a + b + 2 * c < 2 * a + 4 * b ∧ a + 3 * b + c < 2 * a + 4 * b ∧ 5 * b < 2 * a + 4 * b ∧ a + b + 2 * d < 2 * a + 4 * b ∧ a + 2 * c + d < 2 * a + 4 * b ∧ 2 * b + c + d < 2 * a + 4 * b ∧ b + 3 * c < 2 * a + 4 * b ∧ b + c + g < 2 * a + 4 * b ∧ 3 * d < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0394 (a b c : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0395 (a b c : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * c) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0396 (a b c d : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : d < a + b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0397 (a e : Nat)
    (q0 : 0 < a)
    (q1 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0398 (a b c g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_0399 (a b c d g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 2 * g < 5 * a + 2 * b)
    (q3 : 3 * a + b + c < 2 * a + 4 * b)
    (q4 : d < a + b)
    (q5 : g = a + 2 * b) :
    3 * a + b + c < 2 * a + 4 * b ∧ 2 * a + 3 * b < 2 * a + 4 * b ∧ 2 * a + c + d < 2 * a + 4 * b ∧ a + 2 * b + d < 2 * a + 4 * b ∧ a + b + 2 * c < 2 * a + 4 * b ∧ 3 * b + c < 2 * a + 4 * b ∧ b + 2 * d < 2 * a + 4 * b ∧ 2 * c + d < 2 * a + 4 * b := by
  omega

end Max11DegreeRoutes
